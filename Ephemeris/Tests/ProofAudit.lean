import Ephemeris.Proofs.Rational.PositionSemantics
import Ephemeris.Proofs.ErrorComposition
import Ephemeris
import Lean.Util.CollectAxioms

/-! Reject admitted proofs or extra axioms in the exact receiver and numeric refinements. -/

run_cmd do
  let obligations := #[
    ``Ephemeris.Proofs.Real.PositionReconstruction.sourceAlgorithmCorrect,
    ``Ephemeris.Proofs.Real.PositionReconstruction.queryInterpretationCorrect,
    ``Ephemeris.Proofs.Real.PositionReconstruction.evaluationCorrect,
    ``Ephemeris.Proofs.Message.validationCorrect,
    ``Ephemeris.Proofs.Message.queryValidationCorrect,
    ``Ephemeris.Proofs.Message.tickArithmeticCorrect,
    ``Ephemeris.Proofs.Float.CoefficientDecoding.coefficientDecodingExact,
    ``Ephemeris.Proofs.Float.CoefficientDecoding.coefficientModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.normalizedEpochModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.basisModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.coordinateModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.reconstructModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.evaluationModelsAgree,
    ``Ephemeris.Proofs.Float.PositionReconstruction.uniformAccuracy_of_modelAccuracy,
    ``Ephemeris.Proofs.Float.Binary64Rounding.normalize_error,
    ``Ephemeris.Proofs.Float.Binary64Arithmetic.add_error,
    ``Ephemeris.Proofs.Float.Binary64Arithmetic.sub_error,
    ``Ephemeris.Proofs.Float.Binary64Arithmetic.mul_error,
    ``Ephemeris.Proofs.Float.Binary64Division.ofNat_exact,
    ``Ephemeris.Proofs.Float.Binary64Division.nat_div_error,
    ``Ephemeris.Proofs.Float.EpochNormalization.normalized_epoch_error,
    ``Ephemeris.Proofs.Float.ChebyshevBasis.basis_error,
    ``Ephemeris.Proofs.Float.CoordinateReconstruction.coordinate_error,
    ``Ephemeris.Proofs.Float.UniformAccuracy.modelUniformAccuracy,
    ``Ephemeris.Proofs.Float.UniformAccuracy.uniformAccuracy,
    ``Ephemeris.Proofs.Rational.ChebyshevRecurrence.equation4Correct,
    ``Ephemeris.Proofs.Rational.ReconstructionLoops.table3BasisCorrect,
    ``Ephemeris.Proofs.Rational.ReconstructionLoops.equation5Table3Relation,
    ``Ephemeris.Proofs.Rational.PositionSemantics.table3PositionCorrect,
    ``Ephemeris.Proofs.Real.PositionReconstruction.epochMappingCorrect,
    ``Ephemeris.Proofs.Rational.PositionSemantics.reconstructionCorrect,
    ``Ephemeris.Proofs.Rational.PositionSemantics.checkedReceiverCorrect,
    ``Ephemeris.Proofs.ErrorComposition.errorBudgetsCompose]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for obligation in obligations do
    for axiomName in ← Lean.collectAxioms obligation do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {obligation}"
  Lean.logInfo m!"All {obligations.size} theorem entry points pass the axiom audit. The primary Float receiver has a proved 10-micrometer per-coordinate bound and supported-domain success."
