import Ephemeris.Implementation.Correctness.PositionAccuracy

namespace Ephemeris.Proofs.ErrorComposition

theorem errorBudgetsCompose
    : ∀ approximate intermediate exact first second,
        Implementation.Correctness.PositionAccuracy.RealWithin approximate intermediate
          first
        → Implementation.Correctness.PositionAccuracy.RealWithin intermediate exact second
        → Implementation.Correctness.PositionAccuracy.RealWithin approximate exact
            (first + second) := by
  intro a b c e₁ e₂ ⟨he₁, hx₁, hy₁, hz₁⟩ ⟨he₂, hx₂, hy₂, hz₂⟩
  exact ⟨add_nonneg he₁ he₂,
    (abs_sub_le a.x b.x c.x).trans (add_le_add hx₁ hx₂),
    (abs_sub_le a.y b.y c.y).trans (add_le_add hy₁ hy₂),
    (abs_sub_le a.z b.z c.z).trans (add_le_add hz₁ hz₂)⟩

theorem binary64_error_trans (value : XYZ Float.Model) (intermediate exact : XYZ ℝ)
    (first second : ℝ)
    (hf
      : Implementation.Correctness.PositionAccuracy.Binary64Within value intermediate
          first)
    (he
      : Implementation.Correctness.PositionAccuracy.RealWithin intermediate exact second)
    : Implementation.Correctness.PositionAccuracy.Binary64Within value exact
        (first + second) := by
  cases hx : Definitions.Binary64Value.toReal value.x with
  | none => simp [Implementation.Correctness.PositionAccuracy.Binary64Within, hx] at hf
  | some x =>
      cases hy : Definitions.Binary64Value.toReal value.y with
      | none =>
          simp [Implementation.Correctness.PositionAccuracy.Binary64Within, hx, hy] at hf
      | some y =>
          cases hz : Definitions.Binary64Value.toReal value.z with
          | none =>
              simp [Implementation.Correctness.PositionAccuracy.Binary64Within, hx, hy, hz] at hf
          | some z =>
              simp only [Implementation.Correctness.PositionAccuracy.Binary64Within, hx, hy, hz] at hf ⊢
              exact errorBudgetsCompose _ _ _ _ _ hf he

end Ephemeris.Proofs.ErrorComposition
