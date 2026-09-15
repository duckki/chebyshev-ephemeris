import Init.Data.Float.Float
import Ephemeris.Definitions.Message

/-! FP3: native binary64 evaluation of the authoritative fixed-point Message.
Conversions, normalization, and reconstruction loops use concrete Float operations.
The independent software model and correctness contracts live in Correctness/Float. -/

namespace Ephemeris.Implementation.PositionReconstruction

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def coefficient (q : Int32) : Float :=
  -- Int32.toFloat is opaque in Lean v4.33.1. UInt32.toFloat has a logical model.
  -- For q < 0, -(q+1) fits Int32 even at its minimum; +1 then fits UInt32.
  let value := if q < 0 then -((-(q + 1)).toUInt32 + 1).toFloat else q.toUInt32.toFloat
  value / 32.0

/-- FP3: reject a nonfinite intermediate before a later operation can use it. -/
@[inline]
def finite (value : Float) : Option Float :=
  if Float.isFinite value then some value else none

/-- FP3: subtract integer ticks first, then separately divide, multiply, and subtract.
The unchecked helper requires a validated query. -/
@[inline]
def normalizedEpoch (m : Message) (time : UInt64) : Option Float := do
  let elapsed := time - Message.startTick m
  let ratio ← finite (UInt64.toFloat elapsed / UInt64.toFloat (Message.durationTicks m))
  let scaled ← finite (2 * ratio)
  finite (scaled - 1)

/-- FP3 / B25 Table 3: eleven basis values in the adopted recurrence order. -/
@[inline]
def basis (argument : Float) : Option (Array Float) := do
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
def coordinate (integers : Array Int32) (values : Array Float) : Option Float := do
  let mut result := (0 : Float)
  for i in [:11] do
    let product ← finite (coefficient (integers.getD i 0) * values.getD i 0)
    result ← finite (result + product)
  return result

/-- FP3: unchecked reconstruction of all three coordinates. -/
@[inline]
def reconstruct (m : Message) (time : UInt64) : Option (XYZ Float) := do
  let x ← normalizedEpoch m time
  let values ← basis x
  let px ← coordinate m.coefficients.x values
  let py ← coordinate m.coefficients.y values
  let pz ← coordinate m.coefficients.z values
  return ⟨px, py, pz⟩

/-- FP2/FP3: validate the same Message and query before reconstruction, preserving
error precedence and rejecting any nonfinite intermediate. -/
@[inline]
def evaluate (m : Message) (time : UInt64) : Except ReceiverError (XYZ Float) := do
  Message.validateQuery m time
  match reconstruct m time with
  | some value => return value
  | none => throw .nonfiniteComputation

end Ephemeris.Implementation.PositionReconstruction
