import Mathlib.Tactic.Ring
import Ephemeris.Proofs.Float.EpochNormalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic.IntervalCases

/-! Finiteness, array-prefix invariants, and propagated error for the eleven-step
Chebyshev recurrence. The comparison uses the real source argument, whose interval
bound supplies Mathlib's |T_i(x)| ≤ 1 theorem. -/

namespace Ephemeris.Proofs.Float.ChebyshevBasis
open Ephemeris.Proofs.Float.CoefficientDecoding Ephemeris.Proofs.Float.EpochNormalization
open Ephemeris.Proofs.Float.Binary64Arithmetic Ephemeris.Proofs.Float.Binary64Division

private def basisValue (x : Float.Model) (values : Array Float.Model) (i : Nat)
    : Option Float.Model :=
  if i = 0 then
    some (Float.Model.ofUInt8 1)
  else if i = 1 then
    some x
  else do
    let twiceX ← Implementation.Correctness.Float.modelFinite (Float.Model.ofUInt8 2 * x)
    let product ←
      Implementation.Correctness.Float.modelFinite
        (twiceX * values.getD (i - 1) (Float.Model.ofUInt8 0))
    Implementation.Correctness.Float.modelFinite
      (product - values.getD (i - 2) (Float.Model.ofUInt8 0))

private def basisStep (x : Float.Model) (values : Array Float.Model) (i : Nat)
    : Option (Array Float.Model) :=
  (basisValue x values i).map values.push

private theorem basis_as_fold (x : Float.Model) (u : ℝ)
    (hx : Definitions.Binary64Value.toReal x = some u)
    : Implementation.Correctness.Float.modelBasis x
      = (List.range 11).foldlM (basisStep x) #[] := by
  unfold Implementation.Correctness.Float.modelBasis Implementation.Float.ReconstructionKernel.basis
  change (Implementation.Correctness.Float.modelFinite x).bind _ = _
  rw [finite_of_real _ _ hx]
  simp only [Option.bind_eq_bind, Option.bind, bind_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ← List.range_eq_range']
  change _ = (List.range 11).foldlM (fun values i => values.push <$> basisValue x values i) #[]
  rw [← List.forIn_yield_eq_foldlM (fun i values => basisValue x values i)
    (fun _ values v => values.push v)]
  congr 1
  funext i values
  by_cases hi0 : i = 0
  · simp [basisValue, hi0]
    rfl
  by_cases hi1 : i = 1
  · simp [basisValue, hi1]
  simp only [basisValue, hi0, hi1, ↓reduceIte, beq_iff_eq, Option.bind_eq_bind]
  simp only [Option.map_eq_map, Option.map_eq_bind, Option.bind_assoc]
  rfl

private theorem abs_mul_difference (a b c d : ℝ)
    : |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

private theorem abs_near (a b e : ℝ) (h : |a-b| ≤ e) (hb : |b| ≤ 1) : |a| ≤ e + 1 := by
  have := abs_sub_le a b 0
  simp only [sub_zero] at this
  exact le_trans this (add_le_add h hb)

private theorem recurrence_error (x b c : Float.Model) (u v w X Y Z E F : ℝ)
    (hx : Definitions.Binary64Value.toReal x = some u)
    (hb : Definitions.Binary64Value.toReal b = some v)
    (hc : Definitions.Binary64Value.toReal c = some w) (hX : |X| ≤ 1) (hY : |Y| ≤ 1)
    (hZ : |Z| ≤ 1) (ex : |u-X| ≤ 3 * (2 : ℝ)^(-50 : Int)) (ey : |v-Y| ≤ E)
    (ez : |w-Z| ≤ F) (hE : E ≤ 1) (hF : F ≤ 1)
    : ∃ q : ℝ,
        (do
          let a ← Implementation.Correctness.Float.modelFinite (Float.Model.ofUInt8 2 * x)
          let p ← Implementation.Correctness.Float.modelFinite (a * b)
          Implementation.Correctness.Float.modelFinite (p - c))
          = some ((Float.Model.ofUInt8 2 * x) * b - c)
        ∧ Definitions.Binary64Value.toReal ((Float.Model.ofUInt8 2 * x) * b - c) = some q
        ∧ |q - (2 * X * Y - Z)| ≤ 2 * E + F + 22 * (2 : ℝ)^(-50 : Int) := by
  have hu : |u| ≤ 2 := by have := abs_near u X _ ex hX; norm_num at this; linarith only [this]
  have hv : |v| ≤ 2 := le_trans (abs_near v Y E ey hY) (by linarith only [hE])
  have hw : |w| ≤ 2 := le_trans (abs_near w Z F ez hZ) (by linarith only [hF])
  obtain ⟨a, ha, ea⟩ := mul_error_real (Float.Model.ofUInt8 2) x 2 u 2 model_two_real hx
    (by norm_num) (by norm_num) (by norm_num [abs_mul]; linarith only [hu])
  have ha' : |a| ≤ 5 := by
    have h := abs_sub_le a (2*u) 0
    simp only [sub_zero, abs_mul, abs_of_pos (show (0:ℝ)<2 by norm_num)] at h
    norm_num at ea
    linarith only [h, ea, hu]
  obtain ⟨p, hp, ep⟩ := mul_error_real (Float.Model.ofUInt8 2 * x) b a v 4 ha hb
    (by norm_num) (by norm_num) (by
      have h := mul_le_mul ha' hv (abs_nonneg v) (by norm_num : (0:ℝ) ≤ 5)
      rw [abs_mul]
      norm_num
      linarith only [h])
  have hp' : |p| ≤ 11 := by
    have h := abs_sub_le p (a*v) 0
    simp only [sub_zero] at h
    have hprod := mul_le_mul ha' hv (abs_nonneg v) (by norm_num : (0:ℝ) ≤ 5)
    rw [← abs_mul] at hprod
    norm_num at ep
    linarith only [h, ep, hprod]
  obtain ⟨q, hq, eq⟩ := sub_error_real ((Float.Model.ofUInt8 2 * x) * b) c p w 4 hp hc
    (by norm_num) (by norm_num) (by
      have h := abs_sub p w
      norm_num
      linarith only [h, hp', hw])
  refine ⟨q, ?_, hq, ?_⟩
  · simp only [finite_of_real _ _ ha, Option.bind_eq_bind, Option.bind,
      finite_of_real _ _ hp, finite_of_real _ _ hq]
  · have he0 : 0 ≤ E := le_trans (abs_nonneg _) ey
    have heA : |a - 2 * X| ≤ (2 : ℝ)^(-50 : Int) + 2 * (3 * (2 : ℝ)^(-50 : Int)) := by
      have h := abs_sub_le a (2*u) (2*X)
      have h' : |2*u - 2*X| = 2*|u-X| := by rw [← mul_sub, abs_mul]; norm_num
      rw [h'] at h
      norm_num at ea ex ⊢
      linarith only [h, ea, ex]
    have heP : |p - 2 * X * Y| ≤ (2 : ℝ)^(-48 : Int) +
        2 * ((2 : ℝ)^(-50 : Int) + 2 * (3 * (2 : ℝ)^(-50 : Int))) + 2 * E := by
      have h := abs_sub_le p (a*v) (2*X*Y)
      have h' := abs_mul_difference a v (2*X) Y
      have haE := mul_le_mul heA hv (abs_nonneg v) (by positivity)
      have hyE := mul_le_mul (show |2*X| ≤ 2 by rw [abs_mul]; norm_num; linarith only [hX]) ey
        (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      norm_num at ep haE ⊢
      nlinarith only [h, h', haE, hyE, ep]
    have h := abs_sub_le q (p-w) (2*X*Y-Z)
    have hd : |(p-w)-(2*X*Y-Z)| ≤ |p-2*X*Y| + |w-Z| := by
      rw [show (p-w)-(2*X*Y-Z) = (p-2*X*Y)-(w-Z) by ring]
      exact abs_sub _ _
    norm_num at eq heP ⊢
    linarith only [h, hd, eq, heP, ez]

theorem chebyshev_bound (X : ℝ) (hX : |X| ≤ 1) (i : Nat)
    : |Definitions.PositionReconstruction.chebyshevT X i| ≤ 1 := by
  rw [Ephemeris.Proofs.Real.PositionReconstruction.real_chebyshevT_eq_basis]
  exact Polynomial.Chebyshev.abs_eval_T_real_le_one (i : Int) hX

private theorem basis_prefix (x : Float.Model) (u X : ℝ)
    (hx : Definitions.Binary64Value.toReal x = some u) (hX : |X| ≤ 1)
    (ex : |u-X| ≤ 3 * (2 : ℝ)^(-50 : Int)) (k : Nat) (hk : k ≤ 11)
    : ∃ values,
        (List.range k).foldlM (basisStep x) #[] = some values
        ∧ values.size = k
        ∧ ∀ i < k,
            ∃ v : ℝ,
              Definitions.Binary64Value.toReal (values.getD i (Float.Model.ofUInt8 0))
                = some v
              ∧ |v - Definitions.PositionReconstruction.chebyshevT X i|
                ≤ (3 : ℝ)^i * (2 : ℝ)^(-43 : Int) := by
  induction k with
  | zero => exact ⟨#[], rfl, rfl, by omega⟩
  | succ k ih =>
      have hklt : k < 11 := by omega
      obtain ⟨values, hv, hsize, hvalues⟩ := ih (by omega)
      have hnew : ∃ f v, basisValue x values k = some f ∧
          Definitions.Binary64Value.toReal f = some v ∧
          |v - Definitions.PositionReconstruction.chebyshevT X k| ≤ (3 : ℝ)^k * (2 : ℝ)^(-43 : Int) := by
        by_cases hk0 : k = 0
        · exact ⟨Float.Model.ofUInt8 1, 1, by simp [basisValue, hk0], model_one_real,
            by norm_num [hk0, Definitions.PositionReconstruction.chebyshevT]⟩
        by_cases hk1 : k = 1
        · refine ⟨x, u, by simp [basisValue, hk1], hx, ?_⟩
          simp only [hk1, Definitions.PositionReconstruction.chebyshevT]
          norm_num at ex ⊢
          linarith only [ex]
        have hk2 : 2 ≤ k := by omega
        obtain ⟨v, hv, ev⟩ := hvalues (k-1) (by omega)
        obtain ⟨w, hw, ew⟩ := hvalues (k-2) (by omega)
        have hE : (3 : ℝ)^(k-1) * (2 : ℝ)^(-43 : Int) ≤ 1 := by
          interval_cases k <;> norm_num
        have hF : (3 : ℝ)^(k-2) * (2 : ℝ)^(-43 : Int) ≤ 1 := by
          interval_cases k <;> norm_num
        obtain ⟨q, hrun, hq, eq⟩ := recurrence_error x
          (values.getD (k-1) (Float.Model.ofUInt8 0)) (values.getD (k-2) (Float.Model.ofUInt8 0))
          u v w X (Definitions.PositionReconstruction.chebyshevT X (k-1)) (Definitions.PositionReconstruction.chebyshevT X (k-2))
          _ _ hx hv hw hX (chebyshev_bound X hX _) (chebyshev_bound X hX _) ex ev ew hE hF
        refine ⟨_, q, ?_, hq, ?_⟩
        · simpa only [basisValue, hk0, hk1, ↓reduceIte] using hrun
        · have hrec : Definitions.PositionReconstruction.chebyshevT X k =
              2 * X * Definitions.PositionReconstruction.chebyshevT X (k-1) - Definitions.PositionReconstruction.chebyshevT X (k-2) := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
            simp [Definitions.PositionReconstruction.chebyshevT]
          rw [hrec]
          refine le_trans eq ?_
          interval_cases k <;> norm_num
      obtain ⟨f, v, hf, hvreal, ev⟩ := hnew
      refine ⟨values.push f, ?_, by simpa using hsize, ?_⟩
      · rw [List.range_succ, List.foldlM_append, hv]
        simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil,
          basisStep, hf, Option.map_some]
        rfl
      · intro i hi
        by_cases hik : i < k
        · obtain ⟨w, hw, ew⟩ := hvalues i hik
          refine ⟨w, ?_, ew⟩
          simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize, if_neg (Nat.ne_of_lt hik)] using hw
        · have hik : i = k := by omega
          subst i
          refine ⟨v, ?_, ev⟩
          simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize, ite_true, Option.getD_some] using hvreal

/-- The model's eleven-entry Chebyshev loop succeeds and each stored basis value
approximates the real source recurrence. Bounds are conservative and index-dependent. -/
theorem basis_error (x : Float.Model) (u X : ℝ)
    (hx : Definitions.Binary64Value.toReal x = some u) (hX : |X| ≤ 1)
    (ex : |u-X| ≤ 3 * (2 : ℝ)^(-50 : Int))
    : ∃ values,
        Implementation.Correctness.Float.modelBasis x = some values
        ∧ values.size = 11
        ∧ ∀ i < 11,
            ∃ v : ℝ,
              Definitions.Binary64Value.toReal (values.getD i (Float.Model.ofUInt8 0))
                = some v
              ∧ |v - Definitions.PositionReconstruction.chebyshevT X i|
                ≤ (3 : ℝ)^i * (2 : ℝ)^(-43 : Int) := by
  rw [basis_as_fold x u hx]
  exact basis_prefix x u X hx hX ex 11 (by omega)

end Ephemeris.Proofs.Float.ChebyshevBasis
