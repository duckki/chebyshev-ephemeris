import Ephemeris.Definitions.Coordinates
import Mathlib.Data.Real.Basic
import Ephemeris.Definitions.Binary64Value

/-!
# Shared real and binary64 position accuracy relations

These statement-only interpretations are independent of any reconstruction
implementation. They compare three coordinates with a nonnegative absolute bound.
-/

/-! Shared real-position error relation; independent of reference implementations. -/

namespace Ephemeris.Implementation.Correctness.PositionAccuracy

/-- N3: nonnegative absolute error bound per coordinate, in meters. This is an
infinity-norm bound, not a Euclidean-distance bound or equality of frame metadata. -/
def RealWithin (approximate exact : XYZ ℝ) (budget : ℝ) : Prop :=
  0 ≤ budget
  ∧ |approximate.x - exact.x| ≤ budget
  ∧ |approximate.y - exact.y| ≤ budget
  ∧ |approximate.z - exact.z| ≤ budget

/-! Project coordinatewise finite-precision accuracy contract N3. -/

/-- F1 / N3: a binary64 result must be finite on all axes and meet the
specified coordinatewise error budget relative to an exact real position.
`Implementation.Correctness.Float.UniformAccuracy` uses this relation for its native
accuracy contract. -/
def Binary64Within (value : XYZ Float.Model) (exact : XYZ ℝ) (budget : ℝ) : Prop :=
  match Definitions.Binary64Value.toReal value.x,
        Definitions.Binary64Value.toReal value.y,
        Definitions.Binary64Value.toReal value.z with
  | some x, some y, some z => RealWithin ⟨x, y, z⟩ exact budget
  | _, _, _ => False

end Ephemeris.Implementation.Correctness.PositionAccuracy
