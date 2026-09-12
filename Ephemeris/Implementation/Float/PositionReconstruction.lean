import Ephemeris.Definitions.Message
import Init.Data.Float.Float

/-! FP3: native binary64 evaluation of the authoritative fixed-point Message.
All numerical operations use Float and bounded integers. Float.Model supplies
the independent model functions in Correctness/Float, outside this runtime path.
The eleven-coefficient loops preserve the adopted Table 3 operation order. -/

namespace Ephemeris.Implementation.Float.PositionReconstruction

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def coefficient (q : Int32) : Float :=
  -- Int32.toFloat is opaque in Lean v4.33.1. UInt32.toFloat has a logical model.
  -- For q < 0, -(q+1) fits Int32 even at its minimum; +1 then fits UInt32.
  let value := if q < 0 then -((-(q + 1)).toUInt32 + 1).toFloat else q.toUInt32.toFloat
  value / 32.0

/-- FP3: reject a nonfinite intermediate before it can enter a later operation. -/
def finite (value : Float) : Option Float :=
  if value.isFinite then some value else none

/-- FP3: subtract integer ticks before converting; division/multiply/subtract
are separately rounded. The unchecked helper requires a validated query. -/
def normalizedEpoch (m : Message) (time : UInt64) : Option Float := do
  let elapsed := time - Message.startTick m
  let ratio ← finite (elapsed.toFloat / (Message.durationTicks m).toFloat)
  let scaled ← finite (2.0 * ratio)
  finite (scaled - 1.0)

/-- FP3 / B25 Table 3: eleven basis values, with separately rounded operations. -/
def basis (argument : Float) : Option (Array Float) := do
  let x ← finite argument
  let mut values := #[]
  for i in [:11] do
    let value ←
      if i == 0 then
        pure 1.0
      else if i == 1 then
        pure x
      else do
        let twiceX ← finite (2.0 * x)
        let product ← finite (twiceX * values.getD (i - 1) 0.0)
        finite (product - values.getD (i - 2) 0.0)
    values := values.push value
  return values

/-- FP3 / B25 Table 3: decode fixed-point coefficients and accumulate a_0..a_10.
No fused operations or reassociation. Storage shape is checked by evaluate. -/
def coordinate (integers : Array Int32) (values : Array Float) : Option Float := do
  let zero := 0.0
  let mut result := zero
  for i in [:11] do
    let product ← finite (coefficient (integers.getD i 0) * values.getD i zero)
    result ← finite (result + product)
  return result

/-- FP3: unchecked evaluation; the public checked entry point has identical inputs. -/
def reconstruct (m : Message) (time : UInt64) : Option (XYZ Float) := do
  let x ← normalizedEpoch m time
  let values ← basis x
  let px ← coordinate m.coefficients.x values
  let py ← coordinate m.coefficients.y values
  let pz ← coordinate m.coefficients.z values
  return ⟨px, py, pz⟩

/-- FP2/FP3: same message and query as the real evaluator. There is no radius or
budget parameter: the fixed-profile error bound must be proved offline. -/
def evaluate (m : Message) (time : UInt64) : Except ReceiverError (XYZ Float) := do
  Message.validateQuery m time
  match reconstruct m time with
  | some value => return value
  | none => throw .nonfiniteComputation

end Ephemeris.Implementation.Float.PositionReconstruction
