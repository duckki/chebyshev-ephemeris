import Mathlib.Tactic.Ring
import Ephemeris.Proofs.Float.EpochNormalization
import Mathlib.Tactic.IntervalCases

/-! Finite ascending coordinate accumulation and the error budget supplied by the
profile's individual coefficient widths. Loop prefixes track the exact real sum
and a proved allowance, without adding any arithmetic to the runtime receiver. -/

namespace Ephemeris.Proofs.Float.CoordinateReconstruction
open Ephemeris.Proofs.Float.CoefficientDecoding Ephemeris.Proofs.Float.EpochNormalization
open Ephemeris.Proofs.Float.Binary64Arithmetic Ephemeris.Proofs.Float.Binary64Division

private noncomputable def coefficientBound (i : Nat) : ℝ :=
  (2 : ℝ)^((Definitions.Message.oneHourCoefficientWidths.getD i 5)-1) / 32

private noncomputable def termAllowance (i : Nat) : ℝ :=
  coefficientBound i * ((3 : ℝ)^i * (2 : ℝ)^(-43 : Int)) + 2 * (2 : ℝ)^(-25 : Int)

private theorem coefficient_bound (a : Int32) (i : Nat)
    (ha
      : Implementation.Correctness.Message.CoefficientFits a
          (Definitions.Message.oneHourCoefficientWidths.getD i 5))
    : |Definitions.PositionReconstruction.coefficient a| ≤ coefficientBound i := by
  have h : |(a.toInt : ℝ)| ≤ (2 : ℝ)^((Definitions.Message.oneHourCoefficientWidths.getD i 5)-1) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast ha.1, le_of_lt (by exact_mod_cast ha.2)⟩
  unfold Definitions.PositionReconstruction.coefficient coefficientBound
  norm_num only [Definitions.Message.coefficientFractionBits, pow_succ, pow_zero]
  rw [abs_div, abs_of_pos (show (0:ℝ)<32 by norm_num)]
  exact div_le_div_of_nonneg_right h (by norm_num)

private theorem coefficientBound_nonneg (i : Nat) : 0 ≤ coefficientBound i := by
  unfold coefficientBound
  positivity

private theorem coefficientBound_le (i : Nat) (hi : i < 11)
    : coefficientBound i ≤ 2^24 := by
  interval_cases i <;> norm_num [coefficientBound, Definitions.Message.oneHourCoefficientWidths]

private theorem weight_prefix_bound (k : Nat) (hk : k ≤ 11)
    : ((List.range k).map coefficientBound).sum ≤ (2 : ℝ)^25 := by
  interval_cases k <;> norm_num [coefficientBound, Definitions.Message.oneHourCoefficientWidths, List.range_succ]

private theorem allowance_prefix_bound (k : Nat) (hk : k ≤ 11)
    : ((List.range k).map termAllowance).sum ≤ (1 : ℝ) := by
  interval_cases k <;> norm_num [termAllowance, coefficientBound, Definitions.Message.oneHourCoefficientWidths, List.range_succ]

private theorem coordinate_truth_bound (integers : Array Int32) (X : ℝ)
    (hT : ∀ i, |Definitions.PositionReconstruction.chebyshevT X i| ≤ 1)
    (ha
      : ∀ i < 11,
          Implementation.Correctness.Message.CoefficientFits (integers.getD i 0)
            (Definitions.Message.oneHourCoefficientWidths.getD i 5))
    (k : Nat) (hk : k ≤ 11)
    : |((List.range k).map
          fun i =>
            Definitions.PositionReconstruction.coefficient (integers.getD i 0)
            * Definitions.PositionReconstruction.chebyshevT X i).sum|
      ≤ ((List.range k).map coefficientBound).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.sum_range_succ]
      have ht := mul_le_mul (coefficient_bound _ k (ha k (by omega))) (hT k)
        (abs_nonneg _) (coefficientBound_nonneg k)
      rw [← abs_mul, mul_one] at ht
      exact le_trans (abs_add_le _ _) (add_le_add (ih (by omega)) ht)

private def coordinateStep (integers : Array Int32) (values : Array Float.Model)
    (result : Float.Model) (i : Nat)
    : Option Float.Model := do
  let product ←
    Implementation.Correctness.Float.modelFinite
      (Implementation.Correctness.Float.modelCoefficient (integers.getD i 0)
        * values.getD i (Float.Model.ofUInt8 0))
  Implementation.Correctness.Float.modelFinite (result + product)

private theorem coordinate_as_fold (integers : Array Int32) (values : Array Float.Model)
    : Implementation.Correctness.Float.modelCoordinate integers values
      = (List.range 11).foldlM (coordinateStep integers values)
          (Float.Model.ofUInt8 0) := by
  unfold Implementation.Correctness.Float.modelCoordinate
  simp only [bind_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ← List.range_eq_range']
  have hfold := List.forIn_yield_eq_foldlM (m := Option) (l := List.range 11)
    (fun i result => coordinateStep integers values result i)
    (fun _ _ value => value) (Float.Model.ofUInt8 0)
  have hid : (fun result i => (fun value : Float.Model => value) <$>
      coordinateStep integers values result i) = coordinateStep integers values := by
    funext result i
    cases coordinateStep integers values result i <;> rfl
  rw [hid] at hfold
  rw [← hfold]
  congr 1
  funext i result
  simp only [coordinateStep, Option.map_eq_map, Option.bind_eq_bind, Option.map_bind]
  congr 1
  funext product
  simp only [Function.comp_apply]
  cases Implementation.Correctness.Float.modelFinite (result + product) <;> rfl

private theorem coordinate_prefix (integers : Array Int32) (values : Array Float.Model)
    (X : ℝ) (hT : ∀ i, |Definitions.PositionReconstruction.chebyshevT X i| ≤ 1)
    (ha
      : ∀ i < 11,
          Implementation.Correctness.Message.CoefficientFits (integers.getD i 0)
            (Definitions.Message.oneHourCoefficientWidths.getD i 5))
    (hv
      : ∀ i < 11,
          ∃ v : ℝ,
            Definitions.Binary64Value.toReal (values.getD i (Float.Model.ofUInt8 0))
              = some v
            ∧ |v - Definitions.PositionReconstruction.chebyshevT X i|
              ≤ (3 : ℝ)^i * (2 : ℝ)^(-43 : Int))
    (k : Nat) (hk : k ≤ 11)
    : ∃ result r,
        (List.range k).foldlM (coordinateStep integers values) (Float.Model.ofUInt8 0)
          = some result
        ∧ Definitions.Binary64Value.toReal result = some r
        ∧ |r
            - ((List.range k).map
                fun i =>
                  Definitions.PositionReconstruction.coefficient (integers.getD i 0)
                  * Definitions.PositionReconstruction.chebyshevT X i).sum|
          ≤ ((List.range k).map termAllowance).sum := by
  induction k with
  | zero => exact ⟨Float.Model.ofUInt8 0, 0, rfl, model_zero_real, by simp⟩
  | succ k ih =>
      have hklt : k < 11 := by omega
      obtain ⟨result, r, hr, hrval, er⟩ := ih (by omega)
      obtain ⟨v, hvval, ev⟩ := hv k (by omega)
      let C := Definitions.PositionReconstruction.coefficient (integers.getD k 0)
      let T := Definitions.PositionReconstruction.chebyshevT X k
      let S := ((List.range k).map fun i => Definitions.PositionReconstruction.coefficient (integers.getD i 0) *
        Definitions.PositionReconstruction.chebyshevT X i).sum
      have hC : |C| ≤ coefficientBound k := coefficient_bound _ _ (ha k (by omega))
      have hS : |S| ≤ (2 : ℝ)^25 := le_trans (coordinate_truth_bound integers X hT ha k (by omega))
        (weight_prefix_bound k (by omega))
      have hAllow := allowance_prefix_bound k (show k ≤ 11 by omega)
      have hrmag : |r| ≤ (2 : ℝ)^26 := by
        have h := abs_sub_le r S 0
        simp only [sub_zero] at h
        norm_num at hS ⊢
        linarith only [h, er, hAllow, hS]
      have hvMag : |v| ≤ 2 := by
        have h := abs_sub_le v T 0
        simp only [sub_zero] at h
        have hE : (3 : ℝ)^k * (2 : ℝ)^(-43 : Int) ≤ 1 := by interval_cases k <;> norm_num
        linarith only [h, ev, hE, hT k]
      have hCmax := le_trans hC (coefficientBound_le k (by omega))
      have hProdMag : |C*v| ≤ (2 : ℝ)^25 := by
        rw [abs_mul]
        have := mul_le_mul hCmax hvMag (abs_nonneg v) (by positivity : (0:ℝ) ≤ 2^24)
        norm_num at this ⊢
        exact this
      obtain ⟨p, hpval, ep⟩ := mul_error_real (Implementation.Correctness.Float.modelCoefficient (integers.getD k 0))
        (values.getD k (Float.Model.ofUInt8 0)) C v 27 (coefficientDecodingExact _) hvval
        (by norm_num) (by norm_num) (le_trans hProdMag (by norm_num))
      have hpMag : |p| ≤ (2 : ℝ)^25 + 1 := by
        have h := abs_sub_le p (C*v) 0
        simp only [sub_zero] at h
        have heps : (2 : ℝ)^(27-52 : Int) ≤ 1 := by norm_num
        linarith only [h, ep, hProdMag, heps]
      obtain ⟨q, hqval, eq⟩ := add_error_real result
        (Implementation.Correctness.Float.modelCoefficient (integers.getD k 0) * values.getD k (Float.Model.ofUInt8 0)) r p 27 hrval hpval
        (by norm_num) (by norm_num) (by
          have h := abs_add_le r p
          norm_num at hrmag hpMag ⊢
          linarith only [h, hrmag, hpMag])
      let next := result + Implementation.Correctness.Float.modelCoefficient (integers.getD k 0) * values.getD k (Float.Model.ofUInt8 0)
      have hstep : coordinateStep integers values result k = some next := by
        unfold coordinateStep
        rewrite [finite_of_real _ _ hpval, Option.bind_eq_bind, Option.bind_some]
        exact finite_of_real _ _ hqval
      refine ⟨next, q, ?_, hqval, ?_⟩
      · rewrite [List.range_succ, List.foldlM_append, hr, Option.bind_eq_bind, Option.bind_some,
          List.foldlM_cons, hstep]
        simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_nil]
        rfl
      · have hCV : |C*v - C*T| ≤ coefficientBound k * ((3 : ℝ)^k * (2 : ℝ)^(-43 : Int)) := by
          rw [← mul_sub, abs_mul]
          exact mul_le_mul hC ev (abs_nonneg _) (coefficientBound_nonneg k)
        have hpError := abs_sub_le p (C*v) (C*T)
        have hqError := abs_sub_le q (r+p) (S+C*T)
        have hsError : |(r+p)-(S+C*T)| ≤ |r-S|+|p-C*T| := by
          rw [show (r+p)-(S+C*T) = (r-S)+(p-C*T) by ring]
          exact abs_add_le _ _
        simp only [List.sum_range_succ]
        change |q-(S+C*T)| ≤ ((List.range k).map termAllowance).sum + termAllowance k
        change |q-(S+C*T)| ≤ ((List.range k).map termAllowance).sum +
          (coefficientBound k * ((3 : ℝ)^k * (2 : ℝ)^(-43 : Int)) + 2 * (2 : ℝ)^(-25 : Int))
        norm_num only [Int.reduceSub] at ep eq hCV ⊢
        linarith only [hqError, hsError, hpError, hCV, ep, eq, er]

/-- Success and a uniform 10-micrometer per-coordinate bound for the ascending
fixed-point coefficient sum, assuming the established basis bounds. -/
theorem coordinate_error (integers : Array Int32) (values : Array Float.Model) (X : ℝ)
    (hT : ∀ i, |Definitions.PositionReconstruction.chebyshevT X i| ≤ 1)
    (ha
      : ∀ i < 11,
          Implementation.Correctness.Message.CoefficientFits (integers.getD i 0)
            (Definitions.Message.oneHourCoefficientWidths.getD i 5))
    (hv
      : ∀ i < 11,
          ∃ v : ℝ,
            Definitions.Binary64Value.toReal (values.getD i (Float.Model.ofUInt8 0))
              = some v
            ∧ |v - Definitions.PositionReconstruction.chebyshevT X i|
              ≤ (3 : ℝ)^i * (2 : ℝ)^(-43 : Int))
    : ∃ result r,
        Implementation.Correctness.Float.modelCoordinate integers values = some result
        ∧ Definitions.Binary64Value.toReal result = some r
        ∧ |r
            - ((List.range 11).map
                fun i =>
                  Definitions.PositionReconstruction.coefficient (integers.getD i 0)
                  * Definitions.PositionReconstruction.chebyshevT X i).sum|
          ≤ (1 : ℝ)/100000 := by
  obtain ⟨result, r, hr, hrval, er⟩ := coordinate_prefix integers values X hT ha hv 11 (by omega)
  refine ⟨result, r, ?_, hrval, le_trans er ?_⟩
  · rw [coordinate_as_fold]; exact hr
  · norm_num [termAllowance, coefficientBound, Definitions.Message.oneHourCoefficientWidths, List.range_succ]

end Ephemeris.Proofs.Float.CoordinateReconstruction
