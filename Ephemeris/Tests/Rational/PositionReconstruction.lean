import Ephemeris.Proofs.Rational.PositionSemantics

/-! Executable rational regression checks on the authoritative Message/tick domain.
Hand-expanded polynomials and explicit integer offsets provide independent expected
values. Proof-only recurrence helpers are exercised separately from runtime loops. -/

namespace Ephemeris.Tests.Rational.PositionReconstruction
open Ephemeris.Proofs.Rational.ChebyshevRecurrence
      Ephemeris.Proofs.Rational.PositionSemantics
      Ephemeris.Proofs.Rational.ReconstructionLoops

private def checkEq [BEq α] [Repr α]
    (count : IO.Ref Nat) (label : String) (actual expected : α)
    : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  count.modify (· + 1)

private def axis (values : List Int) : Array Int32 :=
  ((List.range 11).map fun i => Int32.ofInt (values.getD i 0)).toArray

private def fixture : Message :=
  ⟨0, 43200, 2, ⟨axis [96, 64, 32], axis [-32, 0, 64], axis [0, 32, 0]⟩⟩

private def run : IO Unit := do
  let count ← IO.mkRef 0
  for x in ([-1, -1/2, 0, 1/2, 1, 3/2] : List ℚ) do
    let expected := [1, x, 2*x*x-1, 4*x*x*x-3*x]
    for i in [:4] do
      checkEq count s!"Eq. (4), T_{i}({x})" (rationalChebyshevT x i) (expected.getD i 0)
    checkEq count s!"Table 3 basis at {x}"
      (Implementation.Rational.PositionReconstruction.table3Basis 3 x) expected.toArray
  checkEq count "basis at one-half"
    (Implementation.Rational.PositionReconstruction.table3Basis 5 (1/2 : ℚ))
    #[1, 1/2, -1/2, -1, -1/2, 1/2]
  checkEq count "degree-64 right endpoint"
    (Implementation.Rational.PositionReconstruction.table3Basis 64 1)
    (Array.replicate 65 1)
  checkEq count "degree-64 left endpoint"
    (Implementation.Rational.PositionReconstruction.table3Basis 64 (-1))
    ((List.range 65).map fun i => if i % 2 == 0 then (1 : ℚ) else -1).toArray
  checkEq count "printed Eq. (5) omits a0" (rationalEquation5Sum 2 [3, 2, 1] (1/2)) (1/2)
  checkEq count "Table 3 includes a0"
    (Implementation.Rational.PositionReconstruction.table3Coordinate 2 [3, 2, 1]
      (Implementation.Rational.PositionReconstruction.table3Basis 2 (1/2))) (7/2)
  for q in ([-2147483648, -32, -1, 0, 1, 32, 2147483647] : List Int) do
    checkEq count s!"coefficient q/32: {q}"
      (Implementation.Rational.PositionReconstruction.coefficient (Int32.ofInt q))
      ((q : ℚ) / 32)

  let m := fixture
  let start : UInt64 := 212630486400000000
  let duration : UInt64 := 3600000000
  checkEq count "nonmidnight Julian date"
    (Implementation.Rational.PositionReconstruction.timeToRational start) 2461001
  checkEq count "reference day"
    (Implementation.Rational.PositionReconstruction.referenceDay m) (4922001/2)
  checkEq count "half-hour code"
    (Implementation.Rational.PositionReconstruction.validityHours m) 1
  -- X=2+2x+2x², Y=-3+4x², Z=x, encoded as 11 fixed-point coefficients.
  for (offset, x)
      in ([
            (0, -1),
            (900000000, -1/2),
            (1800000000, 0),
            (2700000000, 1/2),
            (3600000000, 1)
          ]
          : List (UInt64 × ℚ)) do
    checkEq count s!"normalized epoch at offset {offset}"
      (Implementation.Rational.PositionReconstruction.normalizedEpoch m (start + offset))
      x
    checkEq count s!"checked position at offset {offset}"
      (Implementation.Rational.PositionReconstruction.evaluate m (start + offset))
      (.ok ⟨2+2*x+2*x*x, -3+4*x*x, x⟩)
  checkEq count "single microsecond normalization"
    (Implementation.Rational.PositionReconstruction.normalizedEpoch m (start + 1))
    (-1 + 1/1800000000)
  let constant : Message := { m with coefficients := ⟨axis [224], axis [-96], axis [0]⟩ }
  for time in [start, start + 1, start + duration] do
    checkEq count "zero-padded constant uses the same degree-10 Message"
      (Implementation.Rational.PositionReconstruction.evaluate constant time)
      (.ok ⟨7, -3, 0⟩)
  let shifted := { m with dayOffset := 16383 }
  checkEq count "day-shift preserves relative position"
    (Implementation.Rational.PositionReconstruction.evaluate shifted
      (start + 16383 * 86400000000)) (.ok ⟨2, 1, -1⟩)
  let crossing := { constant with secondOfDay := 86399, validityCode := 7 }
  checkEq count "validity crosses midnight"
    (Implementation.Rational.PositionReconstruction.evaluate crossing
      (Message.startTick crossing + Message.durationTicks crossing))
    (.ok ⟨7, -3, 0⟩)
  let invalid : List (Message × UInt64 × ReceiverError) :=
    [
      (
        { m with dayOffset := 16384, secondOfDay := 86400, validityCode := 0 },
        0,
        .invalidDayOffset
      ),
      ({ m with secondOfDay := 86400, validityCode := 0 }, 0, .invalidSecondOfDay),
      (
        { m with validityCode := 0, coefficients := ⟨#[], #[], #[]⟩ },
        0,
        .invalidValidityCode
      ),
      ({ m with validityCode := 8 }, start, .invalidValidityCode),
      ({ m with coefficients := ⟨#[], #[], #[]⟩ }, 0, .coefficientCountMismatch),
      (
        { m with coefficients := ⟨(axis [0]).push 0, axis [0], axis [0]⟩ },
        0,
        .coefficientCountMismatch
      ),
      (
        { m with coefficients := ⟨axis [536870912], axis [0], axis [0]⟩ },
        0,
        .coefficientOutOfRange
      ),
      (m, start - 1, .outsideValidity),
      (m, start + duration + 1, .outsideValidity),
      (m, 0, .outsideValidity),
      (m, 18446744073709551615, .outsideValidity)
    ]
  for (message, time, error) in invalid do
    checkEq count s!"shared error: {repr error}"
      (Implementation.Rational.PositionReconstruction.evaluate message time)
      (.error error)
  IO.println s!"Ephemeris: {← count.get} rational Message regression checks passed."

#eval run
end Ephemeris.Tests.Rational.PositionReconstruction
