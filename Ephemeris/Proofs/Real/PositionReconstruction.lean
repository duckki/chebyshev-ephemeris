import Ephemeris.Implementation.Correctness.Real
import Ephemeris.Proofs.Message

/-! Consistency of the real source model.
This checks source loops against independent polynomial semantics. The separate Float proof establishes its roundoff bound. -/

namespace Ephemeris.Proofs.Real.PositionReconstruction

private noncomputable def basisStep (x : ℝ) (T : Array ℝ) (i : Nat) : Array ℝ :=
  if i = 0 then
    T.push 1
  else if i = 1 then
    T.push x
  else
    T.push (2 * x * T.getD (i - 1) 0 - T.getD (i - 2) 0)

private theorem basis_as_fold (n : Nat) (x : ℝ)
    : Definitions.PositionReconstruction.table3Basis n x
      = (List.range (n + 1)).foldl (basisStep x) #[] := by
  simp only [Definitions.PositionReconstruction.table3Basis, beq_iff_eq]
  simp only [← apply_ite (fun a : Array ℝ => (pure (ForInStep.yield a) : Id _))]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ← List.range_eq_range']
  unfold basisStep
  simp only [Array.getD_eq_getD_getElem?]

private theorem basis_step_prefix (x : ℝ) (k : Nat)
    : basisStep x
        (((List.range k).map (Definitions.PositionReconstruction.chebyshevT x)).toArray) k
      = ((List.range (k + 1)).map
          (Definitions.PositionReconstruction.chebyshevT x)).toArray := by
  rw [List.range_succ, List.map_append]
  cases k with
  | zero => simp [basisStep, Definitions.PositionReconstruction.chebyshevT]
  | succ k =>
      cases k with
      | zero => simp [basisStep, Definitions.PositionReconstruction.chebyshevT]
      | succ k =>
          simp [basisStep, Array.getD, Definitions.PositionReconstruction.chebyshevT]

private theorem basis_fold_prefix (x : ℝ) (k : Nat)
    : (List.range k).foldl (basisStep x) #[]
      = ((List.range k).map
          (Definitions.PositionReconstruction.chebyshevT x)).toArray := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      simpa only [List.range_succ] using basis_step_prefix x k

theorem table3Basis_eq_prefix (n : Nat) (x : ℝ)
    : Definitions.PositionReconstruction.table3Basis n x
      = ((List.range (n + 1)).map
          (Definitions.PositionReconstruction.chebyshevT x)).toArray := by
  rw [basis_as_fold, basis_fold_prefix]

private theorem fold_sum (f : Nat → ℝ) (k : Nat) (v : ℝ)
    : (List.range k).foldl (fun acc i => acc + f i) v
      = v + ((List.range k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.foldl_append, ih, add_assoc]

theorem table3Coordinate_eq_sum (n : Nat) (a : List ℝ) (T : Array ℝ)
    : Definitions.PositionReconstruction.table3Coordinate n a T
      = ((List.range (n + 1)).map fun i => a.getD i 0 * T.getD i 0).sum := by
  simp only [Definitions.PositionReconstruction.table3Coordinate]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', fold_sum]

theorem table3Coordinate_basis_sum (n : Nat) (a : List ℝ) (x : ℝ)
    : Definitions.PositionReconstruction.table3Coordinate n a
        (Definitions.PositionReconstruction.table3Basis n x)
      = ((List.range (n + 1)).map
          fun i =>
            a.getD i 0 * Definitions.PositionReconstruction.chebyshevT x i).sum := by
  rw [table3Coordinate_eq_sum, table3Basis_eq_prefix]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [Array.getD, hi]

theorem real_chebyshevT_eq_basis (i : Nat) (x : ℝ)
    : Definitions.PositionReconstruction.chebyshevT x i
      = Implementation.Correctness.Real.polynomialBasis i x := by
  induction i using Nat.twoStepInduction with
  | zero =>
      simp [Definitions.PositionReconstruction.chebyshevT, Implementation.Correctness.Real.polynomialBasis]
  | one =>
      simp [Definitions.PositionReconstruction.chebyshevT, Implementation.Correctness.Real.polynomialBasis]
  | more n ih₀ ih₁ =>
      simp only [Definitions.PositionReconstruction.chebyshevT, ih₀, ih₁, Implementation.Correctness.Real.polynomialBasis,
        Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Polynomial.Chebyshev.T_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

private theorem real_sum (k : Nat) (a : List ℝ) (x : ℝ)
    : ((List.range k).map
        fun i => a.getD i 0 * Definitions.PositionReconstruction.chebyshevT x i).sum
      = ∑ i ∈ Finset.range k,
          a.getD i 0 * Implementation.Correctness.Real.polynomialBasis i x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.sum_range_succ, Finset.sum_range_succ, ih]
      rw [show Definitions.PositionReconstruction.chebyshevT x k = Implementation.Correctness.Real.polynomialBasis k x from
        real_chebyshevT_eq_basis k x]

theorem real_table3Coordinate (n : Nat) (a : List ℝ) (x : ℝ)
    : Definitions.PositionReconstruction.table3Coordinate n a
        (Definitions.PositionReconstruction.table3Basis n x)
      = Implementation.Correctness.Real.polynomialCoordinate n a x := by
  rw [table3Coordinate_basis_sum]
  exact real_sum (n + 1) a x

theorem sourceAlgorithmCorrect
    : Implementation.Correctness.Real.SourceAlgorithmCorrect := by
  intro n a x
  simp only [Definitions.PositionReconstruction.table3Position, Implementation.Correctness.Real.polynomialPosition,
    real_table3Coordinate]

theorem reconstructCorrect (m : Message) (time : UInt64)
    : Definitions.PositionReconstruction.reconstruct m time
      = Implementation.Correctness.Real.position m time :=
  sourceAlgorithmCorrect 10 (Definitions.PositionReconstruction.coefficients m)
    (Definitions.PositionReconstruction.normalizedEpoch
      (Definitions.PositionReconstruction.referenceDay
        m) (Definitions.PositionReconstruction.secondOfDay m)
      (Definitions.PositionReconstruction.validityHours
        m) (Definitions.PositionReconstruction.timeToReal time))

theorem queryInterpretationCorrect
    : Implementation.Correctness.Real.QueryInterpretationCorrect := by
  intro m time _
  change (Ephemeris.Proofs.Message.startTickNat m ≤ time.toNat ∧
    time.toNat ≤ Ephemeris.Proofs.Message.startTickNat m + Ephemeris.Proofs.Message.durationTicksNat m) ↔ _
  constructor
  · rintro ⟨ha, hb⟩
    have haR : (Ephemeris.Proofs.Message.startTickNat m : ℝ) ≤ (time.toNat : ℝ) := by exact_mod_cast ha
    have hbR : (time.toNat : ℝ) ≤ (Ephemeris.Proofs.Message.startTickNat m + Ephemeris.Proofs.Message.durationTicksNat m : ℕ) := by exact_mod_cast hb
    dsimp [Ephemeris.Proofs.Message.startTickNat, Ephemeris.Proofs.Message.durationTicksNat] at haR hbR
    push_cast at haR hbR
    dsimp [Definitions.PositionReconstruction.referenceDay, Definitions.PositionReconstruction.secondOfDay,
      Definitions.PositionReconstruction.validityHours, Definitions.PositionReconstruction.timeToReal,
      Definitions.PositionReconstruction.startEpoch, Definitions.PositionReconstruction.endEpoch,
      Definitions.Message.referenceDayTwice, Definitions.Message.validityFractionBits]
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    dsimp [Definitions.PositionReconstruction.referenceDay, Definitions.PositionReconstruction.secondOfDay,
      Definitions.PositionReconstruction.validityHours, Definitions.PositionReconstruction.timeToReal,
      Definitions.PositionReconstruction.startEpoch, Definitions.PositionReconstruction.endEpoch,
      Definitions.Message.referenceDayTwice, Definitions.Message.validityFractionBits] at ha hb
    have haR : (Ephemeris.Proofs.Message.startTickNat m : ℝ) ≤ (time.toNat : ℝ) := by
      dsimp [Ephemeris.Proofs.Message.startTickNat]
      push_cast
      linarith
    have hbR : (time.toNat : ℝ) ≤ (Ephemeris.Proofs.Message.startTickNat m + Ephemeris.Proofs.Message.durationTicksNat m : ℕ) := by
      dsimp [Ephemeris.Proofs.Message.startTickNat, Ephemeris.Proofs.Message.durationTicksNat]
      push_cast
      linarith
    exact ⟨by exact_mod_cast haR, by exact_mod_cast hbR⟩

private theorem checked_return (check : Except ReceiverError Unit) (value result : α)
    : (check >>= fun _ => pure value) = .ok result ↔ check = .ok () ∧ result = value := by
  cases check with
  | error e => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, pure, Except.bind, Except.pure, eq_comm]

theorem evaluationCorrect : Implementation.Correctness.Real.EvaluationCorrect := by
  intro m time result
  unfold Definitions.PositionReconstruction.evaluate
  rw [checked_return, Ephemeris.Proofs.Message.queryValidationCorrect, reconstructCorrect]
  exact and_assoc

/-- I1: the concrete real interval has positive length, maps its endpoints to
±1, and maps every included time into [-1,1]. The parameters are real scalars. -/
theorem epochMappingCorrect (referenceDay secondOfDay validityHours : ℝ)
    (hduration : 0 < validityHours)
    : let start := Definitions.PositionReconstruction.startEpoch referenceDay secondOfDay
      let stop :=
        Definitions.PositionReconstruction.endEpoch referenceDay secondOfDay validityHours
      let normalize :=
        Definitions.PositionReconstruction.normalizedEpoch referenceDay secondOfDay
          validityHours
      start < stop
      ∧ normalize start = -1
      ∧ normalize stop = 1
      ∧ ∀ t, start ≤ t ∧ t ≤ stop → -1 ≤ normalize t ∧ normalize t ≤ 1 := by
  have hd : 0 < validityHours / 24 := div_pos hduration (by norm_num)
  have he : Definitions.PositionReconstruction.endEpoch referenceDay secondOfDay validityHours - Definitions.PositionReconstruction.startEpoch referenceDay secondOfDay =
      validityHours / 24 := by simp [Definitions.PositionReconstruction.endEpoch]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [Definitions.PositionReconstruction.endEpoch]
    linarith
  · simp [Definitions.PositionReconstruction.normalizedEpoch, Definitions.PositionReconstruction.normalizeEpoch]
  · norm_num [Definitions.PositionReconstruction.normalizedEpoch, Definitions.PositionReconstruction.normalizeEpoch,
      he, ne_of_gt hd]
  · intro t ht
    have h₀ : 0 ≤ (t - Definitions.PositionReconstruction.startEpoch referenceDay secondOfDay) / (validityHours / 24) :=
      div_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hd)
    have h₁ : (t - Definitions.PositionReconstruction.startEpoch referenceDay secondOfDay) / (validityHours / 24) ≤ 1 := by
      apply (div_le_iff₀ hd).mpr
      have h := ht.2
      dsimp [Definitions.PositionReconstruction.endEpoch] at h
      linarith
    simp only [Definitions.PositionReconstruction.normalizedEpoch, Definitions.PositionReconstruction.normalizeEpoch, he]
    constructor <;> linarith

end Ephemeris.Proofs.Real.PositionReconstruction
