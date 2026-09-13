import Ephemeris.Definitions.Message
import Ephemeris.Definitions.PositionReconstruction
import Ephemeris.Implementation.Float.PositionReconstruction
import Ephemeris.Implementation.Correctness.Message
import Ephemeris.Implementation.Correctness.PositionAccuracy

/-!
# Binary64 model backend and native Float correctness contracts

The model backend executes Float.Model operations through the same reconstruction
kernel as the native Float backend. It shares control flow, while its arithmetic
runs independently of native Float; it does not run the native evaluator and then
convert its result. The real source interpretation and optional rational evaluator
remain separate definitions.

The final section states decoding, native/model correspondence, and real-error
contracts.
-/

namespace Ephemeris.Implementation.Correctness.Float
open Ephemeris.Implementation.Correctness.Message
      Ephemeris.Implementation.Correctness.PositionAccuracy

------------------------------------------------------------------------------------------
-- Float.Model instance of ReconstructionKernel
------------------------------------------------------------------------------------------

/-- FP3: exact coefficient decoding for these signed integer widths. -/
def modelCoefficient (q : Int32) : Float.Model :=
  Definitions.Message.int32ToBinary64 q / Float.Model.ofUInt8 32

/-- FP3: software binary64 conversion and classification.
The existing Float.Model arithmetic instances supply every rounded operation. -/
local instance : Implementation.Float.ReconstructionKernel.Backend Float.Model where
  coefficient := modelCoefficient
  ofUInt64 := Definitions.Message.uint64ToBinary64
  isFinite := Float.Model.isFinite

/-- FP3: model interpretation of the kernel's numeric literals (0, 1, and 2).
This instance is local to model execution and does not affect native Float. -/
local instance (n : Nat) : OfNat Float.Model n := ⟨Float.Model.ofNat n⟩

/-- FP3: reject nonfinite model values. -/
abbrev modelFinite := Implementation.Float.ReconstructionKernel.finite (α := Float.Model)

/-- FP3: bounded elapsed ticks, with separately rounded model operations. -/
abbrev modelNormalizedEpoch :=
  Implementation.Float.ReconstructionKernel.normalizedEpoch (α := Float.Model)

/-- FP3 / B25 Table 3: the shared eleven-entry recurrence using Float.Model. -/
abbrev modelBasis := Implementation.Float.ReconstructionKernel.basis (α := Float.Model)

/-- FP3 / B25 Table 3: the shared ascending sum using Float.Model. -/
abbrev modelCoordinate :=
  Implementation.Float.ReconstructionKernel.coordinate (α := Float.Model)

/-- FP3: unchecked software-model reconstruction of the same Message and tick. -/
abbrev modelReconstruct :=
  Implementation.Float.ReconstructionKernel.reconstruct (α := Float.Model)

/-- FP2/FP3: common validation and software-model reconstruction. -/
abbrev modelEvaluate :=
  Implementation.Float.ReconstructionKernel.evaluate (α := Float.Model)

------------------------------------------------------------------------------------------
-- Correctness/accuracy statements
------------------------------------------------------------------------------------------

/-! FP3: relations on the same Message, not different message formats. These
statements specify the 1/100000-meter target and shared-kernel correspondence. -/

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

/-- FP3: every valid query succeeds within a useful uniform per-coordinate bound
of real evaluation of the SAME message and query tick. -/
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
