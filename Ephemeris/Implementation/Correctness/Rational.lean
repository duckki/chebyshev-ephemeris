import Ephemeris.Implementation.Rational.PositionReconstruction
import Ephemeris.Definitions.PositionReconstruction

/-!
# Exact rational refinement of the ideal real Message evaluator

Both evaluators receive the same Message and UInt64 tick. Cast only the computed
rational coordinates. The bounded integer fields and tick embed exactly into
both rational and real arithmetic. Intermediate cast/loop lemmas live
in Proofs/Rational. Shared input validity is specified in Correctness/Message.
-/

namespace Ephemeris.Implementation.Correctness.Rational

/-- FP3 / N2: exact agreement with the ideal real evaluation of the same Message.
The unchecked identity also holds outside the accepted domain: both algorithms
use the same totalized division and missing-coefficient defaults. -/
def ReconstructionCorrect : Prop :=
  ∀ (m : Message) (time : UInt64),
    (Implementation.Rational.PositionReconstruction.reconstruct m time).map
      (fun q : ℚ => (q : ℝ))
    = Definitions.PositionReconstruction.reconstruct m time

/-- FP2-FP3 / N2: complete checked results agree, including errors. Thus Rational
inherits the ideal evaluator's supported-domain success and rejection behavior.
Only successful coordinates are cast; the Message and tick are unchanged. -/
def EvaluationCorrect : Prop :=
  ∀ (m : Message) (time : UInt64),
    (Implementation.Rational.PositionReconstruction.evaluate m time).map
      (XYZ.map fun q : ℚ => (q : ℝ))
    = Definitions.PositionReconstruction.evaluate m time

end Ephemeris.Implementation.Correctness.Rational
