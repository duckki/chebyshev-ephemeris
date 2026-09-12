import Ephemeris.Definitions.Message
import Mathlib.Algebra.Field.Rat

/-!
# Exact rational evaluation of the authoritative Message

N2 / FP3: a concrete ℚ implementation of the real Table 3 algorithm under I1-I4.
The same bounded integer Message and UInt64 query tick feed Real, Rational, and
Float. Only working arithmetic differs. Fractions below interpret the fixed-point
fields exactly; they are neither input fields nor runtime error certificates.
-/

namespace Ephemeris.Implementation.Rational.PositionReconstruction

/-- FP1 / N2: signed coefficient integer in units of 2^-5 meters. -/
def coefficient (q : Int32) : ℚ :=
  (q.toInt : ℚ) / (2 : ℚ) ^ Definitions.Message.coefficientFractionBits

/-- FP3 / N2: the query's microsecond Julian-date tick as an exact Julian date. -/
def timeToRational (time : UInt64) : ℚ := (time.toNat : ℚ) / 86400000000

/-- FP1 / N2: Table 6 day offset interpreted relative to JD 2461000.5. -/
def referenceDay (m : Message) : ℚ :=
  (Definitions.Message.referenceDayTwice : ℚ) / 2 + (m.dayOffset.toNat : ℚ)

/-- FP1 / N2: seconds after the reference day. -/
def secondOfDay (m : Message) : ℚ := (m.secondOfDay.toNat : ℚ)

/-- FP1 / N2: half-hour validity code interpreted in hours. -/
def validityHours (m : Message) : ℚ :=
  (m.validityCode.toNat : ℚ) / (2 : ℚ) ^ Definitions.Message.validityFractionBits

/-- FP1 / N2: interpret every fixed-point coefficient exactly in meters. -/
def coefficients (m : Message) : XYZ (List ℚ) :=
  m.coefficients.map (fun axis => axis.toList.map coefficient)

/-- N2 / B25 Table 3: ascending basis loop, using Eq. (4)'s indices (I2).
`getD` totalizes access; the loop fills preceding entries before using them. -/
def table3Basis (n : Nat) (x : ℚ) : Array ℚ :=
  Id.run do
    let mut T : Array ℚ := #[]
    for i in [:n + 1] do
      if i == 0 then
        T := T.push 1
      else if i == 1 then
        T := T.push x
      else
        T := T.push (2 * x * T.getD (i - 1) 0 - T.getD (i - 2) 0)
    return T

/-- N2 / B25 Table 3: ascending coordinate sum, including `a_0` (I3)
and initializing the accumulator to zero (I4). -/
def table3Coordinate (n : Nat) (a : List ℚ) (T : Array ℚ) : ℚ :=
  Id.run do
    let mut value : ℚ := 0
    for i in [:n + 1] do
      value := value + a.getD i 0 * T.getD i 0
    return value

/-- N2 / B25 Table 3: share the basis across the three coordinate sums. -/
def table3Position (n : Nat) (a : XYZ (List ℚ)) (x : ℚ) : XYZ ℚ :=
  let T := table3Basis n x
  ⟨table3Coordinate n a.x T, table3Coordinate n a.y T, table3Coordinate n a.z T⟩

/-- N2 / B25 Table 3: normalize in exact Julian-date arithmetic, including the
seconds-of-day offset in the complete start and end epochs (I1). -/
def normalizedEpoch (m : Message) (time : UInt64) : ℚ :=
  let start := referenceDay m + secondOfDay m / 86400
  let stop := start + validityHours m / 24
  2 * ((timeToRational time - start) / (stop - start)) - 1

/-- FP3 / N2: unchecked Table 3 evaluation at degree 10 under I1-I4. -/
def reconstruct (m : Message) (time : UInt64) : XYZ ℚ :=
  table3Position Message.degree.toNat (coefficients m) (normalizedEpoch m time)

/-- FP2-FP3 / N2: share Message validation with the ideal Real and native Float
evaluators, then reconstruct exactly. No additional input domain or error policy. -/
def evaluate (m : Message) (time : UInt64) : Except ReceiverError (XYZ ℚ) := do
  Message.validateQuery m time
  return reconstruct m time

end Ephemeris.Implementation.Rational.PositionReconstruction
