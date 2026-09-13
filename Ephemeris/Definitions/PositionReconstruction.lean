import Ephemeris.Definitions.Coordinates
import Ephemeris.Definitions.Message
import Mathlib.Data.Real.Basic

/-!
# Real source equations and decoded-message reconstruction

B25 equations (4)-(5) and Table 3 (pp. 6-7), followed by their application to the
decoded Message. Scalar arithmetic is exact over ℝ; degrees and indices are natural.
The source map in `docs/paper-and-spec.md` records the adopted interpretations
I1-I4 and the project's decoded-input contract FP1-FP3.
-/

namespace Ephemeris.Definitions.PositionReconstruction

noncomputable section

/-! ## Literal source equations -/

/-- B25 Eq. (4), with the recurrence index shifted for natural recursion. -/
def chebyshevT (x : ℝ) : Nat → ℝ
  | 0 => 1
  | 1 => x
  | n + 2 => 2 * x * chebyshevT x (n + 1) - chebyshevT x n

/-- B25 Eq. (5) as printed, omitting a_0. Missing entries totalize the formula. -/
def equation5Printed (n : Nat) (a : List ℝ) (x : ℝ) : ℝ :=
  ((List.range n).map fun j => a.getD (j + 1) 0 * chebyshevT x (j + 1)).sum

/-- B25 Table 3: decoded day base plus seconds of day, in Julian days. -/
def startEpoch (referenceDay secondOfDay : ℝ) : ℝ :=
  referenceDay + secondOfDay / 86400

/-- B25 Table 3's ambiguous second-row RHS, retained literally for review. -/
def printedThresholdRhs (referenceDay validityHours : ℝ) : ℝ :=
  referenceDay + validityHours / 24

/-- B25 Table 3: normalize a real epoch to [-1,1] on an increasing interval. -/
def normalizeEpoch (jdMin jdMax t : ℝ) : ℝ :=
  2 * ((t - jdMin) / (jdMax - jdMin)) - 1

/-! ## Interpreted reconstruction algorithm

I1-I4 are adopted readings of Table 3, not author-confirmed errata.
The loops are compared with independent polynomial semantics in
Implementation/Correctness/Real. -/

/-- B25 Table 3, first loop: construct `T[0], ..., T[n]` in ascending order.
Interpretation I2 uses `i-1` and `i-2` in the recurrence, as Eq. (4) requires.
`getD` makes array accesses total; the loop fills each earlier entry first. -/
def table3Basis (n : Nat) (x : ℝ) : Array ℝ :=
  Id.run do
    let mut T : Array ℝ := #[]
    for i in [:n + 1] do
      if i == 0 then
        T := T.push 1
      else if i == 1 then
        T := T.push x
      else
        T := T.push (2 * x * T.getD (i - 1) 0 - T.getD (i - 2) 0)
    return T

/-- B25 Table 3, second loop, for one coordinate. The unspecified accumulator
initialization is made explicit as zero (I4). Coefficients begin at zero (I3). -/
def table3Coordinate (n : Nat) (a : List ℝ) (T : Array ℝ) : ℝ :=
  Id.run do
    let mut value : ℝ := 0
    for i in [:n + 1] do
      value := value + a.getD i 0 * T.getD i 0
    return value

/-- B25 Table 3 / I2-I4: reuse one basis for each coordinate's sum via `XYZ.map`.
The argument `x` is already normalized; the paper's domain is `[-1,1]`. -/
def table3Position (n : Nat) (a : XYZ (List ℝ)) (x : ℝ) : XYZ ℝ :=
  let T := table3Basis n x
  a.map (fun axis => table3Coordinate n axis T)

/-- B25 Table 3 / I1: validity starts at the complete epoch, including seconds of day. -/
def endEpoch (referenceDay secondOfDay validityHours : ℝ) : ℝ :=
  startEpoch referenceDay secondOfDay + validityHours / 24

/-- B25 Table 3 / I1: normalize using the complete start and end epochs. -/
def normalizedEpoch (referenceDay secondOfDay validityHours t : ℝ) : ℝ :=
  normalizeEpoch (startEpoch referenceDay secondOfDay)
    (endEpoch referenceDay secondOfDay validityHours) t

/-! ## Ideal real interpretation of the decoded-message contract

FP1-FP3 interpret Message's integer fields using B25 Table 6 (p. 11) and apply
the Table 3 algorithm. Microsecond query ticks and checked rejection behavior
are project policies. The conversions below introduce no quantization. -/

/-- FP3: exact mathematical coefficient value, in meters. -/
def coefficient (q : Int32) : ℝ :=
  (q.toInt : ℝ) / (2 : ℝ) ^ Definitions.Message.coefficientFractionBits

/-- FP3: exact Julian date of the caller's microsecond tick. -/
def timeToReal (time : UInt64) : ℝ := (time.toNat : ℝ) / 86400000000

/-- FP1/FP3 / B25 Table 6: day origin plus the decoded day offset. -/
def referenceDay (m : Message) : ℝ :=
  (Definitions.Message.referenceDayTwice : ℝ) / 2 + (m.dayOffset.toNat : ℝ)

/-- FP1/FP3: Table 6's integer second of day interpreted in real arithmetic. -/
def secondOfDay (m : Message) : ℝ := (m.secondOfDay.toNat : ℝ)

/-- FP1/FP3: the validity code denotes half-hours. -/
def validityHours (m : Message) : ℝ :=
  (m.validityCode.toNat : ℝ) / (2 : ℝ) ^ Definitions.Message.validityFractionBits

/-- FP3: decode each coordinate's coefficient array as the list used by Table 3. -/
def coefficients (m : Message) : XYZ (List ℝ) :=
  m.coefficients.map (fun axis => axis.toList.map coefficient)

/-- FP3: evaluate B25's interpreted real algorithm at the exact query tick. -/
def reconstruct (m : Message) (time : UInt64) : XYZ ℝ :=
  let normalizedTime :=
    normalizedEpoch (referenceDay m) (secondOfDay m) (validityHours m) (timeToReal time)
  table3Position Message.degree.toNat (coefficients m) normalizedTime

/-- FP2/FP3: same input and query validation as the float evaluator. -/
def evaluate (m : Message) (time : UInt64) : Except ReceiverError (XYZ ℝ) := do
  Message.validateQuery m time
  return reconstruct m time

end -- noncomputable section

end Ephemeris.Definitions.PositionReconstruction
