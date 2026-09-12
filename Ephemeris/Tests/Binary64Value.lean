import Ephemeris.Definitions.Binary64Value

/-!
# Binary64 value-boundary checks (not arithmetic proofs)

Independent binary64 fixtures include signed zeros, subnormals, the smallest
normal, the largest finite value, and nonfinite sentinels. Exact expected values
use integer powers and fractions; no float-to-decimal formatting is involved.
Both the logical model and native `Float` entry point are exercised.
-/

namespace Ephemeris.Tests.Binary64Value

private def run : IO Unit := do
  let cases : List (String × UInt64 × Option ℚ) :=
    [
      ("positive zero", 0x0000000000000000, some 0),
      ("negative zero", 0x8000000000000000, some 0),
      ("one", 0x3ff0000000000000, some 1),
      ("negative one", 0xbff0000000000000, some (-1)),
      (
        "one tenth rounded",
        0x3fb999999999999a,
        some (3602879701896397 / 36028797018963968)
      ),
      (
        "one third rounded",
        0x3fd5555555555555,
        some (6004799503160661 / 18014398509481984)
      ),
      ("smallest subnormal", 0x0000000000000001, some (1 / 2 ^ (1074 : Nat))),
      ("negative subnormal", 0x8000000000000001, some (-1 / 2 ^ (1074 : Nat))),
      (
        "largest subnormal",
        0x000fffffffffffff,
        some ((2 ^ (52 : Nat) - 1) / 2 ^ (1074 : Nat))
      ),
      ("smallest normal", 0x0010000000000000, some (1 / 2 ^ (1022 : Nat))),
      (
        "largest finite",
        0x7fefffffffffffff,
        some ((2 ^ (53 : Nat) - 1) * 2 ^ (971 : Nat))
      ),
      ("positive infinity", 0x7ff0000000000000, none),
      ("negative infinity", 0xfff0000000000000, none),
      ("quiet NaN", 0x7ff8000000000000, none),
      ("NaN payload canonicalized by model", 0x7ff0000000000001, none)
    ]
  for (label, bits, expected) in cases do
    let modeled :=
      Ephemeris.Definitions.Binary64Value.toRational (Float.Model.ofBits bits)
    unless modeled == expected do
      throw (IO.userError s!"Model {label}: expected {repr expected}, got {repr modeled}")
    let native := Ephemeris.Definitions.Binary64Value.floatToRational (Float.ofBits bits)
    unless native == expected do
      throw (IO.userError s!"Native {label}: expected {repr expected}, got {repr native}")
  let tenth := Float.Model.ofBits 0x3fb999999999999a
  unless Ephemeris.Definitions.Binary64Value.toRational tenth != some (1 / 10 : ℚ) do
    throw (IO.userError "Rounded one tenth must differ from exact rational one tenth")
  let twoTenths := Float.Model.ofBits 0x3fc999999999999a
  let roundedSum := Ephemeris.Definitions.Binary64Value.toRational (tenth + twoTenths)
  unless roundedSum == some (1351079888211149 / 4503599627370496 : ℚ) do
    throw (IO.userError "Binary64 addition must be interpreted after its rounding step")
  unless (Float.Model.ofBits 0).toBits
          != (Float.Model.ofBits 0x8000000000000000).toBits do
    throw (IO.userError "Equal numeric zero values must retain different model bits")
  IO.println
    s!"{2 * cases.length + 3} binary64 value checks passed (not roundoff proofs)."

#eval run

end Ephemeris.Tests.Binary64Value
