import Ephemeris.Proofs.Rational.ReconstructionLoops
import Ephemeris.Proofs.Real.PositionReconstruction

/-! Rational-to-real refinement of the full position reconstruction. -/

namespace Ephemeris.Proofs.Rational.PositionSemantics
open Ephemeris.Proofs.Rational.ChebyshevRecurrence
      Ephemeris.Proofs.Rational.ReconstructionLoops

private theorem cast_getD (a : List ℚ) (i : Nat)
    : (a.map (fun q : ℚ => (q : ℝ))).getD i 0 = (a.getD i 0 : ℝ) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[i]? <;> simp

private theorem sum_cast (k : Nat) (a : List ℚ) (x : ℚ)
    : (((List.range k).map fun i => a.getD i 0 * rationalChebyshevT x i).sum : ℝ)
      = ∑ i ∈ Finset.range k,
          (a.map (fun q : ℚ => (q : ℝ))).getD i 0
          * Implementation.Correctness.Real.polynomialBasis i (x : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.sum_range_succ, Rat.cast_add, Finset.sum_range_succ, ih]
      simp only [Rat.cast_mul, chebyshevT_eq_basis, cast_getD]

theorem table3Coordinate_cast (n : Nat) (a : List ℚ) (x : ℚ)
    : (Implementation.Rational.PositionReconstruction.table3Coordinate n a
          (Implementation.Rational.PositionReconstruction.table3Basis n x)
        : ℝ)
      = Implementation.Correctness.Real.polynomialCoordinate n
          (a.map fun q : ℚ => (q : ℝ)) (x : ℝ) := by
  rw [table3Coordinate_basis_sum]
  exact sum_cast (n + 1) a x

/-- The rational loops equal the independent real polynomial sum after casting. -/
theorem table3PositionCorrect
    : ∀ (n : Nat) (a : XYZ (List ℚ)) (x : ℚ),
        (Implementation.Rational.PositionReconstruction.table3Position n a x).map
          (fun q : ℚ => (q : ℝ))
        = Implementation.Correctness.Real.polynomialPosition n
            (a.map (List.map fun q : ℚ => (q : ℝ))) (x : ℝ) := by
  intro n a x
  simp only [Implementation.Rational.PositionReconstruction.table3Position, XYZ.map,
    Implementation.Correctness.Real.polynomialPosition, table3Coordinate_cast]

theorem coefficients_cast (m : Message)
    : (Implementation.Rational.PositionReconstruction.coefficients m).map
        (List.map fun q : ℚ => (q : ℝ))
      = Definitions.PositionReconstruction.coefficients m := by
  simp [Implementation.Rational.PositionReconstruction.coefficients, Definitions.PositionReconstruction.coefficients,
    Implementation.Rational.PositionReconstruction.coefficient, Definitions.PositionReconstruction.coefficient, XYZ.map, List.map_map,
    Function.comp_def]

theorem normalizedEpoch_cast (m : Message) (time : UInt64)
    : (Implementation.Rational.PositionReconstruction.normalizedEpoch m time : ℝ)
      = Definitions.PositionReconstruction.normalizedEpoch
          (Definitions.PositionReconstruction.referenceDay
            m) (Definitions.PositionReconstruction.secondOfDay m)
          (Definitions.PositionReconstruction.validityHours
            m) (Definitions.PositionReconstruction.timeToReal time) := by
  simp [Implementation.Rational.PositionReconstruction.normalizedEpoch, Implementation.Rational.PositionReconstruction.referenceDay,
    Implementation.Rational.PositionReconstruction.secondOfDay, Implementation.Rational.PositionReconstruction.validityHours,
    Implementation.Rational.PositionReconstruction.timeToRational, Definitions.PositionReconstruction.normalizedEpoch,
    Definitions.PositionReconstruction.endEpoch, Definitions.PositionReconstruction.normalizeEpoch, Definitions.PositionReconstruction.startEpoch,
    Definitions.PositionReconstruction.referenceDay, Definitions.PositionReconstruction.secondOfDay,
    Definitions.PositionReconstruction.validityHours, Definitions.PositionReconstruction.timeToReal]

/-- Direct exact refinement of the concrete real evaluator on the same Message. -/
theorem reconstructionCorrect
    : Implementation.Correctness.Rational.ReconstructionCorrect := by
  intro m time
  unfold Implementation.Rational.PositionReconstruction.reconstruct Definitions.PositionReconstruction.reconstruct
  rw [table3PositionCorrect, normalizedEpoch_cast, coefficients_cast,
    Ephemeris.Proofs.Real.PositionReconstruction.sourceAlgorithmCorrect]

/-- Shared validation gives complete equality of checked results, including errors. -/
theorem checkedReceiverCorrect
    : Implementation.Correctness.Rational.EvaluationCorrect := by
  intro m time
  cases h : Message.validateQuery m time with
  | error error =>
      simp [Implementation.Rational.PositionReconstruction.evaluate, Definitions.PositionReconstruction.evaluate, h, Except.map]
  | ok value =>
      simpa [Implementation.Rational.PositionReconstruction.evaluate,
        Definitions.PositionReconstruction.evaluate, h, Except.map]
        using reconstructionCorrect m time

end Ephemeris.Proofs.Rational.PositionSemantics
