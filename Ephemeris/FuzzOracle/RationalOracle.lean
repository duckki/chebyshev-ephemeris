import Ephemeris.FuzzOracle.OracleProtocol
import Ephemeris.Implementation.Rational.PositionReconstruction

/-! Exact-rational oracle for the same P3 Message/tick requests as Float.
Successful coordinates use decimal numerator/denominator pairs. The adapter and
process I/O are tested infrastructure, outside the proved numerical kernel. -/

namespace Ephemeris.FuzzOracle.RationalOracle
open Lean OracleProtocol

private def encodeRat (q : ℚ) : Json :=
  .arr #[.str (toString q.num), .str (toString q.den)]

private def evaluateRequest (j : Json) : Except String Json := do
  unless (← (← j.getObjVal? "version").getNat?) == 3 do
    throw "expected P3"
  unless (← (← j.getObjVal? "operation").getStr?) == "evaluate" do
    throw "expected evaluate"
  let m ← parseMessage (← j.getObjVal? "message")
  let time ← boundedNat (← j.getObjVal? "time") 64
  return match Implementation.Rational.PositionReconstruction.evaluate m
                time.toUInt64 with
          | .ok v =>
              Json.mkObj
                [
                  ("ok", .bool true),
                  ("position", .arr #[encodeRat v.x, encodeRat v.y, encodeRat v.z])
                ]
          | .error e => Json.mkObj [("ok", .bool false), ("error", .str (errorCode e))]

private def respond (line : String) : Json :=
  match parseRequest line >>= evaluateRequest with
  | .ok response => response
  | .error _ => Json.mkObj [("ok", .bool false), ("error", .str "invalidProtocol")]

end Ephemeris.FuzzOracle.RationalOracle

/-- Line-oriented exact oracle; EOF terminates the process. -/
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then
      break
    output.putStrLn (Ephemeris.FuzzOracle.RationalOracle.respond line).compress
