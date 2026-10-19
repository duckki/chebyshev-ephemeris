module

public import Ephemeris.Definitions.PositionReconstruction
public import Ephemeris.Definitions.Message
public import Ephemeris.Implementation.PositionReconstruction
public import Ephemeris.Implementation.Correctness.Message
public import Ephemeris.Implementation.Correctness.Real
public import Ephemeris.Implementation.Correctness.Float
public import Ephemeris.Proofs.Real.PositionReconstruction
public import Ephemeris.Proofs.PositionReconstruction
public import Ephemeris.Proofs.UniformAccuracy

@[expose] public section

/-! One fixed-point Message, ideal real evaluation, and native Float evaluation.
Message and real correctness, exact coefficient decoding, complete native/model
correspondence, and a uniform 10-micrometer per-coordinate error bound are proved.
Every supported query succeeds with finite results. Float.Model semantics live in
Correctness. -/
