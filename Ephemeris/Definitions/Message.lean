import Ephemeris.Definitions.Coordinates
import Init.Data.SInt.Basic
import Init.Data.Float.Model.Float

/-!
# Authoritative decoded-message definition

Source: `docs/paper-and-spec.md`, decoded input contract FP1, FP2, and FP3.
B25 Table 6 (p. 11) and Figure 8 (p. 15) supply the widths and scales recorded
in the published-allocation section below. Signedness, accepted metadata, microsecond query ticks, carrier
choices, and ordered errors are project requirements, not additional paper claims.

This module interprets that adopted contract as the sole Message, its bounded
arithmetic, and executable validation. The guards are colocated with the input
definition so the ideal real model and Float implementation share one policy.
Coefficients mean q/32 meters. Serialization is outside this component.
-/

/-! ## Published field allocation

B25 Table 6 (p. 11), Figure 8 (p. 15), and conclusions (p. 16).

These are source data, not a serialization algorithm. Bit counts are naturals;
binary fractional scales are recorded as numbers of fractional bits. The day
origin is recorded doubled to preserve the printed half-day exactly. Signedness and
validation are project choices in the decoded-input section below. Serialization is outside
this receiver; no bit/byte order or padding is selected here.
-/

namespace Ephemeris.Definitions.Message

/-- B25 Table 6: integer Julian-date offset field. -/
def dayBits : Nat := 14

/-- B25 Table 6: integer second-of-day field. -/
def secondBits : Nat := 17

/-- B25 Table 6: validity field. -/
def validityBits : Nat := 3

/-- B25 Table 6: validity scale is 2^-1 hours. -/
def validityFractionBits : Nat := 1

/-- B25 Table 6: each coordinate coefficient has scale 2^-5 meters. -/
def coefficientFractionBits : Nat := 5

/-- B25 Table 6: twice the printed Julian-date origin, 2461000.5 days. -/
def referenceDayTwice : Nat := 4922001

/-- B25 Table 6 / conclusions: bits per coordinate for the 11-coefficient case. -/
def coordinateBits : Nat := 187

/-- B25 Figure 8, blue `11_1.0_1.0` bars: visually transcribed widths for
a_0 through a_10. Their sum agrees with Table 6's 187-bit allocation. The figure
does not specify signed encoding; including a sign in each width is FP1 policy. -/
def oneHourCoefficientWidths : List Nat := [30, 28, 25, 21, 19, 17, 14, 12, 9, 7, 5]

/-! ## External machine-number interpretation

Pinned to Lean v4.33.1.

Sources: `Init/Data/UInt/BasicAux.lean` (`UInt16.toNat`, `UInt64.toNat`),
`Init/Data/UInt/Basic.lean` (unsigned arithmetic wraps modulo the type's size),
and `Init/Data/Float/Model/Float.lean` (`Float.Model.ofUInt64`).
Signed sources: `Init/Data/SInt/Basic.lean` (`Int32.toInt`, two's complement)
and `Float.Model.ofInt32` in the same float model file.
Unsigned fields use `toNat` directly for natural values in `[0,2^width)`.
The conversion uses the external binary64 rounding model, not rational-to-float
conversion through separately rounded numerator and denominator.
The decoded-input section below selects application limits and time units as project requirements.
-/

/-- Source `Float.Model.ofUInt64`: conversion of the bounded unsigned integer
according to Lean's binary64 model. No claim about arbitrary rational inputs. -/
def uint64ToBinary64 (value : UInt64) : Float.Model := Float.Model.ofUInt64 value

/-- Source `Float.Model.ofInt32`: signed integer-to-binary64 conversion. -/
def int32ToBinary64 (value : Int32) : Float.Model := Float.Model.ofInt32 value

end Ephemeris.Definitions.Message

/-! ## Adopted decoded input, bounded ticks, and validation (FP1/FP2/FP3) -/

namespace Ephemeris

/-- FP1: decoded integer fields. Carriers retain out-of-profile values for
validation. Adapters must reject out-of-carrier inputs before converting them. -/
structure Message where
  dayOffset : UInt16
  secondOfDay : UInt32
  validityCode : UInt8
  coefficients : XYZ (Array Int32)
deriving Repr, BEq, DecidableEq

/-- FP2: common query errors, nonfinite-computation errors, and fixed-point
decoded-input errors. These error codes are project policy, not B25 claims.
Each implementation's correctness contract specifies its subset and precedence. -/
inductive ReceiverError where
  | invalidSecondOfDay
  | coefficientCountMismatch
  | outsideValidity
  | nonfiniteComputation
  | invalidDayOffset
  | invalidValidityCode
  | coefficientOutOfRange
deriving Repr, DecidableEq, BEq

namespace Message

/-- FP1: select the source's 11-coefficient, one-hour allocation as this profile. -/
def coefficientWidths : Array UInt8 :=
  (Definitions.Message.oneHourCoefficientWidths.map UInt8.ofNat).toArray

/-- FP1: fixed profile; degree and frame are not extra payload fields. -/
def degree : UInt16 := 10

/-- FP1: the frame family used in the paper's Section 3.3 fitting study.
The enclosing service must identify its precise frame realization/time scale. -/
def frame : Frame := .celestialLunocentric

/-- FP1: signed range check for a width from `coefficientWidths` (5..30).
The caller supplies a supported width; this helper does not validate widths. -/
def coefficientFits (value : Int32) (width : UInt8) : Bool :=
  let bound := ((1 : UInt32) <<< (width.toUInt32 - 1)).toInt32
  decide (-bound ≤ value ∧ value < bound)

/-- FP2: ordered decoded-input validation. Validity codes 1..7 mean 0.5..3.5 h;
zero is invalid. No offset or special four-hour encoding is inferred. -/
def validate (m : Message) : Except ReceiverError Unit := do
  if m.dayOffset >= 16384 then
    throw .invalidDayOffset
  if m.secondOfDay >= 86400 then
    throw .invalidSecondOfDay
  if m.validityCode == 0 || m.validityCode > 7 then
    throw .invalidValidityCode
  for axis in [m.coefficients.x, m.coefficients.y, m.coefficients.z] do
    if axis.size != 11 then
      throw .coefficientCountMismatch
  for axis in [m.coefficients.x, m.coefficients.y, m.coefficients.z] do
    for i in [:11] do
      unless coefficientFits (axis.getD i 0) (coefficientWidths.getD i 5) do
        throw .coefficientOutOfRange

/-- FP3: exact tick coordinate of JD 2461000.5, in microseconds from JD zero. -/
def epochOriginTick : UInt64 := 212630443200000000

/-- FP3: bounded start tick; validated metadata makes all products/sums fit UInt64. -/
def startTick (m : Message) : UInt64 :=
  epochOriginTick + m.dayOffset.toUInt64 * 86400000000 + m.secondOfDay.toUInt64 * 1000000

/-- FP3: half-hour units to microseconds, with codes 1..7 after validation. -/
def durationTicks (m : Message) : UInt64 := m.validityCode.toUInt64 * 1800000000

/-- FP2/FP3: shared validation for real and float evaluation of the same message.
Check the message before arithmetic, and check order before unsigned subtraction. -/
def validateQuery (m : Message) (time : UInt64) : Except ReceiverError Unit := do
  validate m
  if time < startTick m then
    throw .outsideValidity
  if time - startTick m > durationTicks m then
    throw .outsideValidity

end Message
end Ephemeris
