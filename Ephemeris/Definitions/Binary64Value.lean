import Ephemeris.Definitions.Coordinates
import Mathlib.Data.Real.Basic
import Init.Data.Float.Model.Float

/-!
# Value interpretation of Lean's binary64 model

F1: interpretation of the external Lean v4.33.1 `Float.Model` source, not B25.
Sources: `Init/Data/Float/Model/Unpacked/Basic.lean` (constructors),
`Unpacked/Sign.lean` (`Sign.apply`), `Unpacked/Pack/Basic.lean` (`unpack`), and
`Float.lean` (`Float.Model.unpack`). See the pinned links in the source map.
Finite values mean signed mantissa times two to an integer exponent. Unpacking
handles the implicit bit, exponent bias, and subnormals in the external model.

This layer only interprets stored values. The native evaluator uses Float;
the model functions in Correctness/Float and the accuracy contracts use Float.Model. NaN/infinity have no
rational/real value. Signed zeros share numeric value but retain distinct model
bits; numeric equality must not replace bit equality in a Python translation.
-/

namespace Ephemeris.Definitions.Binary64Value

/-- F1: interpret the external unpacked constructors as exact rationals when
finite. The zero constructor includes both signs; sentinels return `none`. -/
def unpackedToRational : Float.Model.UnpackedFloat → Option ℚ
  | .notANumber => none
  | .infinity _ => none
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
      some ((sign.apply (mantissa : ℤ) : ℚ) * (2 : ℚ) ^ exponent)

/-- F1: exact rational interpretation of a stored binary64 value, using the
pinned external decoder rather than a separately invented bit layout. -/
def toRational (value : Float.Model) : Option ℚ :=
  unpackedToRational value.unpack

/-- F1 / N2: finite stored values embed exactly into the reals. This is not a
conversion from an arbitrary real value to a representable float. -/
def toReal (value : Float.Model) : Option ℝ :=
  (toRational value).map (fun q => (q : ℝ))

/-- F1: interpretation of Lean `Float` through its logical model. Native runtime
agreement and CPython behavior remain separate external execution assumptions. -/
def floatToRational (value : Float) : Option ℚ :=
  toRational value.toModel

end Ephemeris.Definitions.Binary64Value
