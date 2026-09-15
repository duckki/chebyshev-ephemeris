import Ephemeris.Implementation.Correctness.Float
import Ephemeris.FuzzOracle.OracleProtocol

/-! P3 JSON-line oracle for the fixed-point receiver. By default it independently
executes the model functions in Correctness/Float. The explicit --native mode is a separate comparison
target that executes Implementation/PositionReconstruction. Carrier
parsing is outside the numerical kernel; profile errors retain their Lean codes. -/

namespace Ephemeris.FuzzOracle.FloatOracle
open Lean OracleProtocol

private def bits (value : Float.Model) : Json := .str (toString value.toBits)

private def execute (native : Bool) (j : Json) : Except String Json := do
  unless (← (← j.getObjVal? "version").getNat?) == 3 do
    throw "expected P3"
  match ← (← j.getObjVal? "operation").getStr? with
  | "coefficient" =>
      let q ← parseCoefficient (← j.getObjVal? "coefficient")
      let value :=
        if native then
          (Implementation.PositionReconstruction.coefficient q).toModel
        else
          Implementation.Correctness.Float.modelCoefficient q
      return Json.mkObj [("ok", .bool true), ("result", bits value)]
  | "evaluate" =>
      let m ← parseMessage (← j.getObjVal? "message")
      let time ← boundedNat (← j.getObjVal? "time") 64
      let result :=
        if native then
          (Implementation.PositionReconstruction.evaluate m time.toUInt64).map
            (XYZ.map Float.toModel)
        else
          Implementation.Correctness.Float.modelEvaluate m time.toUInt64
      match result with
      | .error error =>
          return Json.mkObj [("ok", .bool false), ("error", .str (errorCode error))]
      | .ok p =>
          return Json.mkObj
            [("ok", .bool true), ("result", .arr #[bits p.x, bits p.y, bits p.z])]
  | _ => throw "unknown operation"

private def respond (native : Bool) (line : String) : Json :=
  match parseRequest line >>= execute native with
  | .ok response => response
  | .error _ => Json.mkObj [("ok", .bool false), ("error", .str "invalidProtocol")]
end Ephemeris.FuzzOracle.FloatOracle

def main (args : List String) : IO Unit := do
  unless args = [] ∨ args = ["--native"] do
    throw (IO.userError "usage: ephemeris_float_oracle [--native]")
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then
      break
    output.putStrLn
      (Ephemeris.FuzzOracle.FloatOracle.respond (args == ["--native"]) line).compress
