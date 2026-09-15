import Ephemeris.Definitions.Message
import Lean.Data.Json

/-! P3 bounded Message/tick parsing and errors for the model/native Float oracle.
This tested process-boundary code is outside the proved numerical kernel. -/

namespace Ephemeris.FuzzOracle.OracleProtocol
open Lean

/-- P3 numbers use integer tokens: no decimal point, exponent, or negative zero.
Check spelling before JSON parsing, which can erase distinctions such as `1e0`.
Quoted text is skipped; the JSON parser checks the remaining syntax. -/
def parseRequest (line : String) : Except String Json := do
  let mut quoted := false
  let mut escaped := false
  let mut previous := ' '
  for c in line.toList do
    if quoted then
      if escaped then
        escaped := false
      else if c == '\\' then
        escaped := true
      else if c == '"' then
        quoted := false
    else if c == '"' then
      quoted := true
    else if
      c == '.'
      || ((c == 'e' || c == 'E') && previous.isDigit)
      || (c == '0' && previous == '-') then
      throw "expected integer token without negative zero"
    previous := c
  Json.parse line

def boundedNat (j : Json) (bits : Nat) : Except String Nat := do
  let n ← j.getNat?
  unless n < 2 ^ bits do
    throw "integer carrier overflow"
  return n

def parseCoefficient (j : Json) : Except String Int32 := do
  let q ← j.getInt?
  unless -(2 : Int) ^ 31 ≤ q ∧ q < (2 : Int) ^ 31 do
    throw "Int32 overflow"
  return Int32.ofInt q

def parseMessage (j : Json) : Except String Message := do
  let day ← boundedNat (← j.getObjVal? "day_offset") 16
  let seconds ← boundedNat (← j.getObjVal? "second_of_day") 32
  let validity ← boundedNat (← j.getObjVal? "validity_code") 8
  let axes ← (← j.getObjVal? "coefficients").getArr?
  unless axes.size == 3 do
    throw "expected three axes"
  let x ← (← axes[0]!.getArr?).mapM parseCoefficient
  let y ← (← axes[1]!.getArr?).mapM parseCoefficient
  let z ← (← axes[2]!.getArr?).mapM parseCoefficient
  return ⟨day.toUInt16, seconds.toUInt32, validity.toUInt8, ⟨x, y, z⟩⟩

def errorCode : ReceiverError → String
  | .invalidDayOffset => "invalidDayOffset"
  | .invalidSecondOfDay => "invalidSecondOfDay"
  | .invalidValidityCode => "invalidValidityCode"
  | .coefficientCountMismatch => "coefficientCountMismatch"
  | .coefficientOutOfRange => "coefficientOutOfRange"
  | .outsideValidity => "outsideValidity"
  | .nonfiniteComputation => "nonfiniteComputation"

end Ephemeris.FuzzOracle.OracleProtocol
