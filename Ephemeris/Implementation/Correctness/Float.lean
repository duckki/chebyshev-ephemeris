import Ephemeris.Definitions.Message
import Ephemeris.Definitions.PositionReconstruction
import Ephemeris.Implementation.PositionReconstruction
import Ephemeris.Implementation.Correctness.Message
import Ephemeris.Implementation.Correctness.PositionAccuracy

/-!
# Binary64 Lean model and native Float correctness contracts

The model spells out normalization and reconstruction using Float.Model operations.
It executes independently of the native implementation, with its own concrete
loops and arithmetic. Both use the Message validation policy from Definitions.
The real source interpretation is a separate mathematical definition.

The final section states decoding, native/model correspondence, and real-error
contracts.
-/

namespace Ephemeris.Implementation.Correctness.Float
open Ephemeris.Implementation.Correctness.Message
      Ephemeris.Implementation.Correctness.PositionAccuracy

------------------------------------------------------------------------------------------
-- Concrete Float.Model execution
------------------------------------------------------------------------------------------

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def modelCoefficient (q : Int32) : Float.Model :=
  Definitions.Message.int32ToBinary64 q / Float.Model.ofUInt8 32

/-- FP3: numeric literals denote the corresponding software binary64 values. -/
local instance (n : Nat) : OfNat Float.Model n := ⟨Float.Model.ofNat n⟩

/-- FP3: reject a nonfinite intermediate before a later operation can use it. -/
@[inline]
def modelFinite (value : Float.Model) : Option Float.Model :=
  if Float.Model.isFinite value then some value else none

/-- FP3: subtract integer ticks first, then separately divide, multiply, and subtract.
The unchecked helper requires a validated query. -/
@[inline]
def modelNormalizedEpoch (m : Message) (time : UInt64) : Option Float.Model := do
  let elapsed := time - Message.startTick m
  let ratio ←
    modelFinite
      (Definitions.Message.uint64ToBinary64 elapsed
        / Definitions.Message.uint64ToBinary64 (Message.durationTicks m))
  let scaled ← modelFinite (2 * ratio)
  modelFinite (scaled - 1)

/-- FP3 / B25 Table 3: eleven basis values in the adopted recurrence order. -/
@[inline]
def modelBasis (argument : Float.Model) : Option (Array Float.Model) := do
  let x ← modelFinite argument
  let mut values := #[]
  for i in [:11] do
    let value ←
      if i == 0 then
        pure 1
      else if i == 1 then
        pure x
      else do
        let twiceX ← modelFinite (2 * x)
        let product ← modelFinite (twiceX * values.getD (i - 1) 0)
        modelFinite (product - values.getD (i - 2) 0)
    values := values.push value
  return values

/-- FP3 / B25 Table 3: decode and accumulate a_0..a_10 without fused operations
or reassociation. The checked evaluator validates storage shape first. -/
@[inline]
def modelCoordinate (integers : Array Int32) (values : Array Float.Model)
    : Option Float.Model := do
  let mut result := (0 : Float.Model)
  for i in [:11] do
    let product ← modelFinite (modelCoefficient (integers.getD i 0) * values.getD i 0)
    result ← modelFinite (result + product)
  return result

/-- FP3: unchecked reconstruction of all three coordinates. -/
@[inline]
def modelReconstruct (m : Message) (time : UInt64) : Option (XYZ Float.Model) := do
  let x ← modelNormalizedEpoch m time
  let values ← modelBasis x
  let px ← modelCoordinate m.coefficients.x values
  let py ← modelCoordinate m.coefficients.y values
  let pz ← modelCoordinate m.coefficients.z values
  return ⟨px, py, pz⟩

/-- FP2/FP3: validate the same Message and query before reconstruction, preserving
error precedence and rejecting any nonfinite intermediate. -/
@[inline]
def modelEvaluate (m : Message) (time : UInt64)
    : Except ReceiverError (XYZ Float.Model) := do
  Message.validateQuery m time
  match modelReconstruct m time with
  | some value => return value
  | none => throw .nonfiniteComputation

------------------------------------------------------------------------------------------
-- Correctness/accuracy statements
------------------------------------------------------------------------------------------

/-! FP3: relations on the same Message, not different message formats. These
statements specify the 1/100000-meter target and native/model correspondence. -/

/-- FP3: fixed-point decoding in the binary64 specification introduces no error,
even for any Int32 carrier. -/
def CoefficientDecodingExact : Prop :=
  ∀ q : Int32,
    Definitions.Binary64Value.toReal (modelCoefficient q)
    = some (Definitions.PositionReconstruction.coefficient q)

/-- FP3: the native signed-conversion adaptation agrees with binary64 semantics. -/
def CoefficientModelsAgree : Prop :=
  ∀ q : Int32,
    (Implementation.PositionReconstruction.coefficient q).toModel = modelCoefficient q

/-- FP3: native evaluation has the specified bits and error outcomes, including
invalid inputs. Mapping an already computed result here is an interpretation;
the independent oracle actually executes modelEvaluate. -/
def EvaluationModelsAgree : Prop :=
  ∀ m time,
    (Implementation.PositionReconstruction.evaluate m time).map (XYZ.map Float.toModel)
    = modelEvaluate m time

/-- FP3: every valid query succeeds within a useful uniform per-coordinate bound
of real evaluation of the SAME message and query tick. -/
def UniformAccuracy (tolerance : ℝ) : Prop :=
  0 ≤ tolerance
  ∧ ∀ m time,
      ValidMessage m
      → InWindow m time
      → ∃ result,
          Implementation.PositionReconstruction.evaluate m time = .ok result
          ∧ Binary64Within (result.map Float.toModel)
              (Definitions.PositionReconstruction.reconstruct m time) tolerance

end Ephemeris.Implementation.Correctness.Float
