import Ephemeris.Definitions.PositionReconstruction
import Ephemeris.Definitions.Message
import Ephemeris.Implementation.Float.PositionReconstruction
import Ephemeris.Implementation.Correctness.Message
import Ephemeris.Implementation.Correctness.Real
import Ephemeris.Implementation.Correctness.Float
import Ephemeris.Proofs.Real.PositionReconstruction
import Ephemeris.Proofs.Float.PositionReconstruction
import Ephemeris.Proofs.Float.UniformAccuracy

/-! One fixed-point Message, ideal real evaluation, and native Float evaluation.
Message and real correctness, exact coefficient decoding, complete native/model
correspondence, and a uniform 10-micrometer per-coordinate error bound are proved.
Every supported query succeeds with finite results. Float.Model semantics live in
Correctness. Optional reference implementations require explicit module imports. -/
