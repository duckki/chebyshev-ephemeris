import Ephemeris.Definitions.Message
import Ephemeris.Implementation.Float.PositionReconstruction
import Ephemeris.Definitions.PositionReconstruction
import Ephemeris.Implementation.Correctness.Message
import Ephemeris.Implementation.Correctness.PositionAccuracy

/-!
# Binary64 execution semantics and native Float correctness contracts

The first section executes Float.Model operations independently of the native
evaluator. The second states decoding, native/model correspondence, and real-error
contracts. Decoding, native/model correspondence, and uniform accuracy at 10 micrometers
per coordinate are proved in Proofs/Float. This module contains no proof scripts.
-/

/-! FP3: software binary64 semantics of the fixed-point receiver, for correctness
statements and independent oracle execution. Every operation explicitly uses
Float.Model. In particular this does not run the native evaluator and convert
its result afterward. The operation schedule follows the adopted Table 3 loops.

This is an original finite-precision specification, not an external source
translation. The implementation is separate in Implementation/Float. Complete
native/model correspondence is established in Proofs/Float/PositionReconstruction. -/

namespace Ephemeris.Implementation.Correctness.Float
open Ephemeris.Implementation.Correctness.Message
      Ephemeris.Implementation.Correctness.PositionAccuracy

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def modelCoefficient (q : Int32) : Float.Model :=
  Definitions.Message.int32ToBinary64 q / Float.Model.ofUInt8 32

/-- FP3: reject a nonfinite intermediate before it can enter a later operation. -/
def modelFinite (value : Float.Model) : Option Float.Model :=
  if value.isFinite then some value else none

/-- FP3: subtract integer ticks before converting; division/multiply/subtract
are separately rounded. The unchecked helper requires a validated query. -/
def modelNormalizedEpoch (m : Message) (time : UInt64) : Option Float.Model := do
  let elapsed := time - Message.startTick m
  let ratio ←
    modelFinite
      (Definitions.Message.uint64ToBinary64 elapsed
        / Definitions.Message.uint64ToBinary64 (Message.durationTicks m))
  let scaled ← modelFinite (Float.Model.ofUInt8 2 * ratio)
  modelFinite (scaled - Float.Model.ofUInt8 1)

/-- FP3 / B25 Table 3: eleven basis values, with separately rounded operations. -/
def modelBasis (argument : Float.Model) : Option (Array Float.Model) := do
  let x ← modelFinite argument
  let mut values := #[]
  for i in [:11] do
    let value ←
      if i == 0 then
        pure (Float.Model.ofUInt8 1)
      else if i == 1 then
        pure x
      else do
        let twiceX ← modelFinite (Float.Model.ofUInt8 2 * x)
        let product ← modelFinite (twiceX * values.getD (i - 1) (Float.Model.ofUInt8 0))
        modelFinite (product - values.getD (i - 2) (Float.Model.ofUInt8 0))
    values := values.push value
  return values

/-- FP3 / B25 Table 3: decode fixed-point coefficients and accumulate a_0..a_10.
No fused operations or reassociation. Storage shape is checked by modelEvaluate. -/
def modelCoordinate (integers : Array Int32) (values : Array Float.Model)
    : Option Float.Model := do
  let zero := Float.Model.ofUInt8 0
  let mut result := zero
  for i in [:11] do
    let product ← modelFinite (modelCoefficient (integers.getD i 0) * values.getD i zero)
    result ← modelFinite (result + product)
  return result

/-- FP3: unchecked evaluation; the public checked entry point has identical inputs. -/
def modelReconstruct (m : Message) (time : UInt64) : Option (XYZ Float.Model) := do
  let x ← modelNormalizedEpoch m time
  let values ← modelBasis x
  let px ← modelCoordinate m.coefficients.x values
  let py ← modelCoordinate m.coefficients.y values
  let pz ← modelCoordinate m.coefficients.z values
  return ⟨px, py, pz⟩

/-- FP2/FP3: same message and query as the real evaluator. There is no radius or
budget parameter: the fixed-profile error bound must be proved offline. -/
def modelEvaluate (m : Message) (time : UInt64)
    : Except ReceiverError (XYZ Float.Model) := do
  Message.validateQuery m time
  match modelReconstruct m time with
  | some value => return value
  | none => throw .nonfiniteComputation

/-! FP3: relate arithmetic choices on the same Message, not different message formats.
The bounds are proved at tolerance 1/100000 meters. No optional rational
evaluator is imported. -/

/-- FP3: fixed-point decoding in the binary64 specification introduces no error,
even for any Int32 carrier. -/
def CoefficientDecodingExact : Prop :=
  ∀ q : Int32,
    Definitions.Binary64Value.toReal (modelCoefficient q)
    = some (Definitions.PositionReconstruction.coefficient q)

/-- FP3: the native signed-conversion adaptation agrees with binary64 semantics. -/
def CoefficientModelsAgree : Prop :=
  ∀ q : Int32,
    (Implementation.Float.PositionReconstruction.coefficient q).toModel
    = modelCoefficient q

/-- FP3: native evaluation has the specified bits and error outcomes, including
invalid inputs. Mapping an already computed result here is an interpretation;
the independent oracle actually executes modelEvaluate. -/
def EvaluationModelsAgree : Prop :=
  ∀ m time,
    (Implementation.Float.PositionReconstruction.evaluate m time).map
      (XYZ.map Float.toModel)
    = modelEvaluate m time

/-- FP3: numerical proof target for the explicit software semantics. -/
def ModelUniformAccuracy (tolerance : ℝ) : Prop :=
  0 ≤ tolerance
  ∧ ∀ m time,
      ValidMessage m
      → InWindow m time
      → ∃ result,
          modelEvaluate m time = .ok result
          ∧ Binary64Within result (Definitions.PositionReconstruction.reconstruct m time)
              tolerance

/-- FP3: every valid query succeeds within a useful uniform per-coordinate bound
of real evaluation of the SAME message and query tick. The evaluator computes no radius. -/
def UniformAccuracy (tolerance : ℝ) : Prop :=
  0 ≤ tolerance
  ∧ ∀ m time,
      ValidMessage m
      → InWindow m time
      → ∃ result,
          Implementation.Float.PositionReconstruction.evaluate m time = .ok result
          ∧ Binary64Within (result.map Float.toModel)
              (Definitions.PositionReconstruction.reconstruct m time) tolerance

end Ephemeris.Implementation.Correctness.Float
