import Ephemeris

/-! FP1/FP2/FP3 decoded-input tests. No transport encoding is involved.
Expected errors and tick coordinates are checked independently of float/model
agreement; both numerical evaluators share the validator. -/

namespace Ephemeris.Tests.Message

private def check (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError label)
  count.modify (· + 1)

private def expectError (count : IO.Ref Nat) (label : String)
    (error : ReceiverError) (result : Except ReceiverError α)
    : IO Unit :=
  match result with
  | .error actual => check count label (actual == error)
  | .ok _ => throw (IO.userError s!"{label}: expected rejection")

private def zeroMessage : Message :=
  ⟨0, 0, 2, ⟨Array.replicate 11 0, Array.replicate 11 0, Array.replicate 11 0⟩⟩

private def replaceAxis (m : Message) (axis : Nat) (values : Array Int32) : Message :=
  match axis with
  | 0 => { m with coefficients.x := values }
  | 1 => { m with coefficients.y := values }
  | _ => { m with coefficients.z := values }

private def run : IO Unit := do
  let count ← IO.mkRef 0
  check count "source allocation sum"
    (Definitions.Message.oneHourCoefficientWidths.sum
      == Definitions.Message.coordinateBits)
  check count "source scale" (Definitions.Message.coefficientFractionBits == 5)
  let m := zeroMessage
  check count "zero coefficients valid" (Message.validate m).isOk
  expectError count "day outside 14 bits" .invalidDayOffset
    (Message.validate { m with dayOffset := 16384 })
  expectError count "second at one day" .invalidSecondOfDay
    (Message.validate { m with secondOfDay := 86400 })
  for code in ([0, 8, 255] : List UInt8) do
    expectError count "invalid validity code" .invalidValidityCode
      (Message.validate { m with validityCode := code })
  expectError count "header before shape and query" .invalidDayOffset
    (Message.validateQuery
      { m with dayOffset := 16384, secondOfDay := 86400, coefficients.x := #[] } 0)
  expectError count "seconds before validity" .invalidSecondOfDay
    (Message.validate { m with secondOfDay := 86400, validityCode := 0 })
  expectError count "validity before shape" .invalidValidityCode
    (Message.validate { m with validityCode := 0, coefficients.x := #[] })
  expectError count "all shapes before coefficient ranges" .coefficientCountMismatch
    (Message.validate
      { m with coefficients.x := Array.replicate 11 2147483647, coefficients.y := #[] })
  for axis in [:3] do
    for size in [0, 10, 12] do
      expectError count "coefficient shape" .coefficientCountMismatch
        (Message.validate (replaceAxis m axis (Array.replicate size 0)))
    for i in [:11] do
      let width := (Message.coefficientWidths.getD i 5).toNat
      let limit : Int := 2 ^ (width - 1)
      for value in [-limit, -1, 0, 1, limit - 1] do
        let query :=
          replaceAxis m axis ((Array.replicate 11 0).set! i (Int32.ofInt value))
        check count "signed range accepts boundary" (Message.validate query).isOk
      for value in [-limit - 1, limit] do
        expectError count "reject signed field outside its range" .coefficientOutOfRange
          (Message.validate
            (replaceAxis m axis ((Array.replicate 11 0).set! i (Int32.ofInt value))))
  for day in ([0, 16383] : List UInt16) do
    for second in ([0, 86399] : List UInt32) do
      for validity in ([1, 2, 7] : List UInt8) do
        let query :=
          { m with dayOffset := day, secondOfDay := second, validityCode := validity }
        check count "metadata boundaries valid" (Message.validate query).isOk
        let expectedStart :=
          212630443200000000 + day.toNat * 86400000000 + second.toNat * 1000000
        check count "integer epoch exact"
          ((Message.startTick query).toNat == expectedStart)
        check count "integer duration exact"
          ((Message.durationTicks query).toNat == validity.toNat * 1800000000)
        check count "inclusive start"
          (Message.validateQuery query (Message.startTick query)).isOk
        check count "inclusive end"
          (Message.validateQuery query
            (Message.startTick query + Message.durationTicks query)).isOk
        expectError count "query before start" .outsideValidity
          (Message.validateQuery query (Message.startTick query - 1))
        expectError count "query after end" .outsideValidity
          (Message.validateQuery query
            (Message.startTick query + Message.durationTicks query + 1))
  expectError count "largest query tick" .outsideValidity
    (Message.validateQuery m 18446744073709551615)
  IO.println s!"{← count.get} decoded-message validation and tick checks passed."

#eval run
end Ephemeris.Tests.Message
