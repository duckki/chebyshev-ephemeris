/-!
# Source coordinate components and frame families

Source: https://doi.org/10.1186/s40645-024-00676-1 (B25).
The source mapping and interpretation decisions are in `docs/paper-and-spec.md`.
These structures introduce data representations, not additional algorithms.
The componentwise `XYZ.map` helper is colocated with its record for review;
it is a project representation helper, not a formula attributed to B25.
-/

namespace Ephemeris

/-- B25 Section 2.3: the two coordinate-frame families used for the fitted positions.
This tag does not specify a frame realization or implement a transformation. -/
inductive Frame where
  | celestialLunocentric
  | lunarFixed
deriving Repr, DecidableEq, BEq

/-- B25 Table 3, "each coordinate component": the X, Y, and Z components.
Using a record instead of an indexed three-vector is a representation choice. -/
structure XYZ (α : Type) where
  x : α
  y : α
  z : α
deriving Repr, DecidableEq, BEq

/-- Project representation helper: apply the same scalar conversion to all three
components. This structural operation is kept with XYZ, not attributed to B25. -/
def XYZ.map (f : α → β) (v : XYZ α) : XYZ β :=
  ⟨f v.x, f v.y, f v.z⟩

end Ephemeris
