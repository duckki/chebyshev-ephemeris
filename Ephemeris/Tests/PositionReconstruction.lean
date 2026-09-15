import Ephemeris

/-! Native Float compared with independent explicit Float.Model execution.
Expected values use bit patterns or exact rational test calculations. These are
runtime/model conformance checks, not proofs of the pending uniform bound. -/

namespace Ephemeris.Tests.PositionReconstruction

private def compare (m : Message) (time : UInt64) : IO Unit := do
  let native :=
    (Ephemeris.Implementation.PositionReconstruction.evaluate m time).map
      (XYZ.map Float.toBits)
  let modeled :=
    (Implementation.Correctness.Float.modelEvaluate m time).map
      (XYZ.map Float.Model.toBits)
  unless native == modeled do
    throw (IO.userError s!"Native/model mismatch: {repr m}, {time}")

-- Arbitrary-precision integers here construct test values only; the evaluator
-- receives Int32 fields already constrained to the profile's signed widths.
private def coefficients (variant : Nat) : Array Int32 :=
  (Message.coefficientWidths.toList.zipIdx.map
    fun (width, i) =>
      let limit : Int := 2 ^ (width.toNat - 1)
      Int32.ofInt
        (match variant with
          | 0 => if i % 2 = 0 then -limit else limit - 1
          | 1 => ((i * 104729 + 9173 : Nat) : Int) % (2 * limit) - limit
          | _ => if i % 2 = 0 then 1 else -1)).toArray

private def run : IO Unit := do
  let mut count := 0
  for variant in [:3] do
    let a := coefficients variant
    let b := coefficients ((variant + 1) % 3)
    for day in ([0, 123, 16383] : List UInt16) do
      for seconds in ([0, 86399] : List UInt32) do
        for code in ([1, 2, 7] : List UInt8) do
          let m : Message := ⟨day, seconds, code, ⟨a, b, a⟩⟩
          let duration := Message.durationTicks m
          for offset in [0, 1, duration / 3, duration / 2, duration - 1, duration] do
            let time := Message.startTick m + offset
            compare m time
            unless (Ephemeris.Implementation.PositionReconstruction.evaluate m
                      time).isOk do
              throw (IO.userError "Valid fixed-point query rejected")
            count := count + 1
  -- Include the full carrier's extreme values to catch signed conversion overflow,
  -- as well as every selected coefficient width and a zero sign-bit check.
  let carrierEdges : List Int := [-2147483648, -2147483647, 2147483647]
  let fieldEdges :=
    Message.coefficientWidths.toList.flatMap
      fun width =>
        let limit : Int := 2 ^ (width.toNat - 1)
        [-limit, -1, 0, 1, limit - 1]
  for value in carrierEdges ++ fieldEdges do
    let q := Int32.ofInt value
    let actual := Ephemeris.Implementation.PositionReconstruction.coefficient q
    unless actual.toBits == (Implementation.Correctness.Float.modelCoefficient q).toBits
            && Definitions.Binary64Value.floatToRational actual
                == some ((value : ℚ) / 32) do
      throw (IO.userError s!"Coefficient conversion mismatch at {value}")
    count := count + 1
  let m : Message :=
    ⟨0, 0, 2, ⟨Array.replicate 11 0, Array.replicate 11 0, Array.replicate 11 0⟩⟩
  let hand :=
    {
      m with
        coefficients :=
          ⟨
            #[96, 64, 32] ++ Array.replicate 8 0,
            #[-32, 0, 64] ++ Array.replicate 8 0,
            #[0, 32] ++ Array.replicate 9 0
          ⟩
    }
  for (offset, expected)
      in ([(0, ⟨2, 1, -1⟩), (1800000000, ⟨2, -3, 0⟩), (3600000000, ⟨6, 1, 1⟩)]
          : List (UInt64 × XYZ Int)) do
    let time := Message.epochOriginTick + offset
    compare hand time
    let .ok result :=
      Ephemeris.Implementation.PositionReconstruction.evaluate hand time
    | throw (IO.userError "Hand polynomial rejected")
    unless result.map Float.toBits
            == (expected.map Float.Model.ofInt).map Float.Model.toBits do
      throw (IO.userError "Hand-derived polynomial result differs")
    count := count + 1
  let invalidMessages :=
    [
      { m with dayOffset := 16384 },
      { m with secondOfDay := 86400 },
      { m with validityCode := 0 },
      { m with coefficients.x := #[] },
      { m with coefficients.z := (Array.replicate 11 0).set! 10 16 }
    ]
  for bad in invalidMessages do
    compare bad (Message.startTick m)
    unless !(Ephemeris.Implementation.PositionReconstruction.evaluate bad
              (Message.startTick m)).isOk do
      throw (IO.userError "Invalid message accepted by native evaluator")
    count := count + 1
  for time
      in [
        0,
        Message.startTick m - 1,
        Message.startTick m + Message.durationTicks m + 1,
        18446744073709551615
      ] do
    compare m time
    unless Ephemeris.Implementation.PositionReconstruction.evaluate m time
            matches .error .outsideValidity do
      throw (IO.userError "Invalid query accepted or wrong error")
    count := count + 1
  IO.println s!"{count} native/model comparisons and independent float checks passed."

#eval run

end Ephemeris.Tests.PositionReconstruction
