import Ephemeris.Definitions.Message

/-!
# Shared binary64 reconstruction schedule

FP3 / B25 Table 3: one finite-precision algorithm, instantiated with native Float
operations in Float/PositionReconstruction and software Float.Model operations in
Correctness/Float. Standard arithmetic instances and a small backend class supply the operations;
this module supplies bounded tick subtraction, the eleven-entry loops, finite
intermediate checks, and the shared Message validation policy.

No algebraic laws are assumed: every multiply, add, subtract, and divide is a
separate backend operation. The real source interpretation and optional rational
evaluator have their own definitions. Arithmetic correspondence and accuracy are
separate contracts in Correctness/Float, not consequences of sharing this code.
-/

namespace Ephemeris.Implementation.Float.ReconstructionKernel

/-- FP3: binary64-specific decoding and classification.
Arithmetic uses Lean's existing Add/Sub/Mul/Div and numeric-literal instances.
This class carries no proof fields or algebraic laws. -/
class Backend (α : Type) where
  coefficient : Int32 → α
  ofUInt64 : UInt64 → α
  isFinite : α → Bool

variable {α : Type} [Backend α]
variable [Add α] [Sub α] [Mul α] [Div α]
variable [OfNat α 0] [OfNat α 1] [OfNat α 2]

/-- FP3: reject a nonfinite intermediate before a later operation can use it. -/
@[inline]
def finite (value : α) : Option α :=
  if Backend.isFinite value then some value else none

/-- FP3: subtract integer ticks first, then separately divide, multiply, and subtract.
The unchecked helper requires a validated query. -/
@[inline]
def normalizedEpoch (m : Message) (time : UInt64) : Option α := do
  let elapsed := time - Message.startTick m
  let ratio ←
    finite (Backend.ofUInt64 elapsed / Backend.ofUInt64 (Message.durationTicks m))
  let scaled ← finite (2 * ratio)
  finite (scaled - 1)

/-- FP3 / B25 Table 3: eleven basis values in the adopted recurrence order. -/
@[inline]
def basis (argument : α) : Option (Array α) := do
  let x ← finite argument
  let mut values := #[]
  for i in [:11] do
    let value ←
      if i == 0 then
        pure 1
      else if i == 1 then
        pure x
      else do
        let twiceX ← finite (2 * x)
        let product ← finite (twiceX * values.getD (i - 1) 0)
        finite (product - values.getD (i - 2) 0)
    values := values.push value
  return values

/-- FP3 / B25 Table 3: decode and accumulate a_0..a_10 without fused operations
or reassociation. The checked evaluator validates storage shape first. -/
@[inline]
def coordinate (integers : Array Int32) (values : Array α) : Option α := do
  let mut result := (0 : α)
  for i in [:11] do
    let product ← finite (Backend.coefficient (integers.getD i 0) * values.getD i 0)
    result ← finite (result + product)
  return result

/-- FP3: unchecked reconstruction of all three coordinates. -/
@[inline]
def reconstruct (m : Message) (time : UInt64) : Option (XYZ α) := do
  let x ← normalizedEpoch m time
  let values ← basis x
  let px ← coordinate m.coefficients.x values
  let py ← coordinate m.coefficients.y values
  let pz ← coordinate m.coefficients.z values
  return ⟨px, py, pz⟩

/-- FP2/FP3: validate the same Message and query before reconstruction, preserving
error precedence and rejecting any nonfinite intermediate. -/
@[inline]
def evaluate (m : Message) (time : UInt64) : Except ReceiverError (XYZ α) := do
  Message.validateQuery m time
  match reconstruct m time with
  | some value => return value
  | none => throw .nonfiniteComputation

end Ephemeris.Implementation.Float.ReconstructionKernel
