import Ephemeris.Definitions.Coordinates
import Ephemeris.Definitions.Message
import Mathlib.Data.Real.Basic

/-!
# Real source equations and decoded-message reconstruction

Review the sections in order: literal source equations, Table 3 interpreted
under I1-I4, and the ideal real application
to the adopted Message. Polynomial arithmetic is real; the source does not
prescribe an executable arithmetic precision. The final section interprets the
project's decoded input and query contract, explicitly distinguished from B25.
-/

/-! ## Literal source equations

B25 equations (4)-(5) and Table 3, pp. 6-7, interpreted over real numbers.
These scalar functions describe deterministic mathematics. They do not select an
input encoding or a floating-point precision. Degree/indices remain natural.
Literal source discrepancies are preserved; I1-I4 are in the source map. -/

namespace Ephemeris.Definitions.PositionReconstruction

/-- B25 Eq. (4), with the recurrence index shifted for natural recursion. -/
noncomputable def chebyshevT (x : ℝ) : Nat → ℝ
  | 0 => 1
  | 1 => x
  | n + 2 => 2 * x * chebyshevT x (n + 1) - chebyshevT x n

/-- B25 Eq. (5) as printed, omitting a_0. Missing entries totalize the formula. -/
noncomputable def equation5Printed (n : Nat) (a : List ℝ) (x : ℝ) : ℝ :=
  ((List.range n).map fun j => a.getD (j + 1) 0 * chebyshevT x (j + 1)).sum

/-- B25 Table 3: decoded day base plus seconds of day, in Julian days. -/
noncomputable def startEpoch (referenceDay secondOfDay : ℝ) : ℝ :=
  referenceDay + secondOfDay / 86400

/-- B25 Table 3's ambiguous second-row RHS, retained literally for review. -/
noncomputable def printedThresholdRhs (referenceDay validityHours : ℝ) : ℝ :=
  referenceDay + validityHours / 24

/-- B25 Table 3: normalize a real epoch to [-1,1] on an increasing interval. -/
noncomputable def normalizeEpoch (jdMin jdMax t : ℝ) : ℝ :=
  2 * ((t - jdMin) / (jdMax - jdMin)) - 1

/-! ## Interpreted reconstruction algorithm

Concrete real interpretation of B25 Table 3 (p. 7), retaining its loops.
I1-I4 are explicit source interpretations, not author-confirmed errata.
The independent polynomial correctness target lives in Implementation/Correctness/Real. -/

/-- B25 Table 3, first loop: construct `T[0], ..., T[n]` in ascending order.
Interpretation I2 uses `i-1` and `i-2` in the recurrence, as Eq. (4) requires.
`getD` makes array accesses total; the loop fills each earlier entry first. -/
noncomputable def table3Basis (n : Nat) (x : ℝ) : Array ℝ :=
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
noncomputable def table3Coordinate (n : Nat) (a : List ℝ) (T : Array ℝ) : ℝ :=
  Id.run do
    let mut value : ℝ := 0
    for i in [:n + 1] do
      value := value + a.getD i 0 * T.getD i 0
    return value

/-- B25 Table 3, polynomial construction followed by all three coordinate sums,
under I2-I4. The input `x` is already normalized; the paper's domain is `[-1,1]`.
This retains the table's loops rather than introducing a different evaluator. -/
noncomputable def table3Position (n : Nat) (a : XYZ (List ℝ)) (x : ℝ) : XYZ ℝ :=
  let T := table3Basis n x
  ⟨table3Coordinate n a.x T, table3Coordinate n a.y T, table3Coordinate n a.z T⟩

/-- I1: validity starts at the complete start epoch, including seconds of day. -/
noncomputable def endEpoch (referenceDay secondOfDay validityHours : ℝ) : ℝ :=
  startEpoch referenceDay secondOfDay + validityHours / 24

/-- B25 Table 3 + I1: deterministic real time normalization. -/
noncomputable def normalizedEpoch (referenceDay secondOfDay validityHours t : ℝ) : ℝ :=
  normalizeEpoch (startEpoch referenceDay secondOfDay)
    (endEpoch referenceDay secondOfDay validityHours) t

/-!
## Ideal real interpretation of the decoded-message contract

B25 Table 3 (p. 7), Table 6 (p. 11), and the adopted contract in
`docs/paper-and-spec.md`, FP1/FP2/FP3. These definitions apply the interpreted
paper algorithm to the one authoritative Message. Real values are exact meanings
of its integer fields, not a second input format or a quantization step.
Microsecond query ticks and checked rejection behavior come from the project
contract. This is a non-executable ideal model, not a finite-precision algorithm.
-/

/-- FP3: exact mathematical coefficient value, in meters. -/
noncomputable def coefficient (q : Int32) : ℝ :=
  (q.toInt : ℝ) / (2 : ℝ) ^ Definitions.Message.coefficientFractionBits

/-- FP3: exact Julian date of the caller's microsecond tick. -/
noncomputable def timeToReal (time : UInt64) : ℝ := (time.toNat : ℝ) / 86400000000

/-- FP1/FP3: decoded Table 6 day base; no extra stored field. -/
noncomputable def referenceDay (m : Message) : ℝ :=
  (Definitions.Message.referenceDayTwice : ℝ) / 2 + (m.dayOffset.toNat : ℝ)

/-- FP1/FP3: Table 6's integer second of day interpreted in real arithmetic. -/
noncomputable def secondOfDay (m : Message) : ℝ := (m.secondOfDay.toNat : ℝ)

/-- FP1/FP3: the validity code denotes half-hours. -/
noncomputable def validityHours (m : Message) : ℝ :=
  (m.validityCode.toNat : ℝ) / (2 : ℝ) ^ Definitions.Message.validityFractionBits

/-- FP3: real polynomial coefficients, derived from the same bounded integers. -/
noncomputable def coefficients (m : Message) : XYZ (List ℝ) :=
  m.coefficients.map (fun axis => axis.toList.map coefficient)

/-- FP3: evaluate B25's interpreted real algorithm at the exact query tick. -/
noncomputable def reconstruct (m : Message) (time : UInt64) : XYZ ℝ :=
  table3Position Message.degree.toNat (coefficients m)
    (normalizedEpoch (referenceDay m) (secondOfDay m) (validityHours m) (timeToReal time))

/-- FP2/FP3: same input and query validation as the float evaluator. -/
noncomputable def evaluate (m : Message) (time : UInt64)
    : Except ReceiverError (XYZ ℝ) := do
  Message.validateQuery m time
  return reconstruct m time

end Ephemeris.Definitions.PositionReconstruction
