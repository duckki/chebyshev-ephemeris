import Ephemeris.Proofs.ErrorComposition
import Ephemeris
import Lean.Util.CollectAxioms

/-! Reject admitted proofs or extra axioms in the real specification and Float refinement. -/

run_cmd do
  let obligations := #[
    ``Ephemeris.Proofs.Real.PositionReconstruction.sourceAlgorithmCorrect,
    ``Ephemeris.Proofs.Real.PositionReconstruction.queryInterpretationCorrect,
    ``Ephemeris.Proofs.Real.PositionReconstruction.evaluationCorrect,
    ``Ephemeris.Proofs.Message.validationCorrect,
    ``Ephemeris.Proofs.Message.queryValidationCorrect,
    ``Ephemeris.Proofs.Message.tickArithmeticCorrect,
    ``Ephemeris.Proofs.CoefficientDecoding.coefficientDecodingExact,
    ``Ephemeris.Proofs.CoefficientDecoding.coefficientModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.normalizedEpochModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.basisModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.coordinateModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.reconstructModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.evaluationModelsAgree,
    ``Ephemeris.Proofs.PositionReconstruction.uniformAccuracy_of_modelAccuracy,
    ``Ephemeris.Proofs.Binary64Rounding.normalize_error,
    ``Ephemeris.Proofs.Binary64Arithmetic.add_error,
    ``Ephemeris.Proofs.Binary64Arithmetic.sub_error,
    ``Ephemeris.Proofs.Binary64Arithmetic.mul_error,
    ``Ephemeris.Proofs.Binary64Division.ofNat_exact,
    ``Ephemeris.Proofs.Binary64Division.nat_div_error,
    ``Ephemeris.Proofs.EpochNormalization.normalized_epoch_error,
    ``Ephemeris.Proofs.ChebyshevBasis.basis_error,
    ``Ephemeris.Proofs.CoordinateReconstruction.coordinate_error,
    ``Ephemeris.Proofs.UniformAccuracy.modelUniformAccuracy,
    ``Ephemeris.Proofs.UniformAccuracy.uniformAccuracy,
    ``Ephemeris.Proofs.Real.PositionReconstruction.epochMappingCorrect,
    ``Ephemeris.Proofs.ErrorComposition.errorBudgetsCompose]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for obligation in obligations do
    for axiomName in ← Lean.collectAxioms obligation do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {obligation}"
  Lean.logInfo m!"All {obligations.size} theorem entry points pass the axiom audit. The primary Float receiver has a proved 10-micrometer per-coordinate bound and supported-domain success."
