import Ephemeris.Definitions.Message
import Mathlib.Data.Int.Basic

/-! FP1/FP2/FP3: independent validity and query meaning for the sole Message.
These domain predicates appear in the Real and Float contracts. Proof-only
arithmetic helpers live in Proofs/Message; planned upstream quantization is documented
without an unimplemented Lean contract. -/

namespace Ephemeris.Implementation.Correctness.Message

/-- FP1: mathematical two's-complement field range, including the sign bit. -/
def CoefficientFits (value : Int32) (width : Nat) : Prop :=
  -(2 : ℤ) ^ (width - 1) ≤ value.toInt ∧ value.toInt < (2 : ℤ) ^ (width - 1)

/-- FP1/FP2: supported decoded messages; the fixed profile supplies degree/frame. -/
def ValidMessage (m : Message) : Prop :=
  m.dayOffset.toNat < 2 ^ Definitions.Message.dayBits
  ∧ m.secondOfDay.toNat < 86400
  ∧ 1 ≤ m.validityCode.toNat
  ∧ m.validityCode.toNat < 2 ^ Definitions.Message.validityBits
  ∧ ∀ axis ∈ [m.coefficients.x, m.coefficients.y, m.coefficients.z],
      axis.size = 11
      ∧ ∀ i < 11,
          CoefficientFits (axis.getD i 0)
            (Definitions.Message.oneHourCoefficientWidths.getD i 5)

/-- FP3: exact inclusive query domain, before any floating arithmetic. -/
def InWindow (m : Message) (time : UInt64) : Prop :=
  let start :=
    212630443200000000 + m.dayOffset.toNat * 86400000000 + m.secondOfDay.toNat * 1000000
  let duration := m.validityCode.toNat * 1800000000
  start ≤ time.toNat ∧ time.toNat ≤ start + duration

end Ephemeris.Implementation.Correctness.Message
