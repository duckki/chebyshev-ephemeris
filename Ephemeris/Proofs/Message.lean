import Ephemeris.Implementation.Correctness.Message
import Mathlib.Tactic.NormNum

/-! Exact integer interpretations of the bounded message arithmetic. -/

namespace Ephemeris.Proofs.Message
open Ephemeris.Implementation.Correctness.Message

/-- FP3: exact mathematical tick coordinate; not a second stored time field. -/
def startTickNat (m : Message) : Nat :=
  212630443200000000 + m.dayOffset.toNat * 86400000000 + m.secondOfDay.toNat * 1000000

/-- FP3: exact duration in microseconds. -/
def durationTicksNat (m : Message) : Nat := m.validityCode.toNat * 1800000000

theorem startTick_exact (m : Ephemeris.Message)
    : (Ephemeris.Message.startTick m).toNat = startTickNat m := by
  have hd := m.dayOffset.toNat_lt
  have hs := m.secondOfDay.toNat_lt
  simp [Ephemeris.Message.startTick, Ephemeris.Message.epochOriginTick, startTickNat,
    UInt64.toNat_add, UInt64.toNat_mul]
  omega

theorem durationTicks_exact (m : Ephemeris.Message)
    : (Ephemeris.Message.durationTicks m).toNat = durationTicksNat m := by
  have hv := m.validityCode.toNat_lt
  simp [Ephemeris.Message.durationTicks, durationTicksNat, UInt64.toNat_mul]
  omega

/-- Internal bridge: bounded ticks agree with the contract's exact arithmetic.
The public supported-domain and Float error statements use InWindow directly. -/
theorem tickArithmeticCorrect
    : ∀ m time,
        ValidMessage m
        → InWindow m time
        → (Ephemeris.Message.startTick m).toNat = startTickNat m
          ∧ (Ephemeris.Message.durationTicks m).toNat = durationTicksNat m
          ∧ startTickNat m + durationTicksNat m < 2 ^ 64
          ∧ (time - Ephemeris.Message.startTick m).toNat = time.toNat - startTickNat m
          ∧ (time - Ephemeris.Message.startTick m).toNat ≤ durationTicksNat m
          ∧ durationTicksNat m < 2 ^ 53 := by
  intro m time hm ht
  have hle : Ephemeris.Message.startTick m ≤ time := by
    rw [UInt64.le_iff_toNat_le, startTick_exact]
    exact ht.1
  simp only [startTick_exact, durationTicks_exact,
    UInt64.toNat_sub_of_le time _ hle, true_and]
  have hd := hm.1
  have hs := hm.2.1
  have hv := hm.2.2.2.1
  dsimp [Definitions.Message.dayBits] at hd
  dsimp [Definitions.Message.validityBits] at hv
  dsimp [InWindow, startTickNat, durationTicksNat] at *
  omega

set_option linter.unusedSimpArgs false in
section
private theorem checks (xs : List α) (p : α → Bool) (error : ReceiverError)
    : (forIn xs PUnit.unit
          (fun a _ =>
            if p a then
              Except.ok (.yield PUnit.unit)
            else
              Except.error error)
        : Except ReceiverError PUnit)
      = if xs.all p then .ok PUnit.unit else .error error := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;>
        simp [List.forIn_cons, h, throw, throwThe, MonadExceptOf.throw,
          Except.bind, Except.pure, bind, pure] at ih ⊢
      exact ih

private theorem coefficientCheck (q : Int32) (i : Nat) (hi : i < 11)
    : Ephemeris.Message.coefficientFits q (Ephemeris.Message.coefficientWidths[i]?.getD 5)
        = true
      ↔ Implementation.Correctness.Message.CoefficientFits q
          (Definitions.Message.oneHourCoefficientWidths[i]?.getD 5) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Ephemeris.Message.coefficientFits, Ephemeris.Message.coefficientWidths,
      Definitions.Message.oneHourCoefficientWidths, Implementation.Correctness.Message.CoefficientFits,
      Int32.le_iff_toInt_le, Int32.lt_iff_toInt_lt] <;> rfl

theorem validationCorrect : ∀ m, Message.validate m = .ok () ↔ ValidMessage m := by
  intro m
  simp only [Ephemeris.Message.validate, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [bind, pure, throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure,
    Functor.map, Except.map]
  simp only [checks]
  simp only [List.forIn_cons, List.forIn_nil]
  simp only [bind, pure, Except.bind, Except.pure]
  split_ifs <;> simp_all +contextual [Implementation.Correctness.Message.ValidMessage,
    Definitions.Message.dayBits, Definitions.Message.validityBits,
    UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt,
    UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj,
    coefficientCheck] <;> omega

private theorem checked_bind (a b : Except ReceiverError Unit)
    : (a >>= fun _ => b) = .ok () ↔ a = .ok () ∧ b = .ok () := by
  cases a with
  | error e => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, Except.bind]

theorem queryValidationCorrect
    : ∀ m time,
        Message.validateQuery m time = .ok () ↔ ValidMessage m ∧ InWindow m time := by
  intro m time
  unfold Ephemeris.Message.validateQuery
  rw [checked_bind, validationCorrect]
  apply and_congr_right
  intro _
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases hs : time < Ephemeris.Message.startTick m
  · have hs' : time.toNat < startTickNat m := by
      simpa only [UInt64.lt_iff_toNat_lt, startTick_exact] using hs
    simp only [hs, if_pos, InWindow, reduceCtorEq, false_iff]
    dsimp [startTickNat] at hs'
    omega
  · have hs' : Ephemeris.Message.startTick m ≤ time := by
      rw [UInt64.le_iff_toNat_le]
      rw [UInt64.lt_iff_toNat_lt] at hs
      omega
    simp only [hs, if_neg, InWindow, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_sub_of_le time _ hs', startTick_exact, durationTicks_exact]
    split_ifs <;> try simp_all only [reduceCtorEq, true_iff, false_iff]
    all_goals have := hs'
    all_goals rw [UInt64.le_iff_toNat_le, startTick_exact] at this
    all_goals dsimp [startTickNat, durationTicksNat] at *
    all_goals omega

end

end Ephemeris.Proofs.Message
