import Mathlib.Tactic.Ring
import Ephemeris.Proofs.Binary64Division
import Ephemeris.Proofs.Real.PositionReconstruction
import Mathlib.Tactic.FieldSimp

namespace Ephemeris.Proofs.EpochNormalization
open Ephemeris.Proofs.CoefficientDecoding
open Ephemeris.Proofs.Binary64Arithmetic Ephemeris.Proofs.Binary64Division

theorem normalized_epoch_ticks (m : Message) (time : UInt64)
    (hm : Implementation.Correctness.Message.ValidMessage m)
    (ht : Implementation.Correctness.Message.InWindow m time)
    : Definitions.PositionReconstruction.normalizedEpoch
        (Definitions.PositionReconstruction.referenceDay m)
        (Definitions.PositionReconstruction.secondOfDay m)
        (Definitions.PositionReconstruction.validityHours m)
        (Definitions.PositionReconstruction.timeToReal time)
      = 2
          * ((time.toNat - Ephemeris.Proofs.Message.startTickNat m : Nat) : ℝ)
          / (Ephemeris.Proofs.Message.durationTicksNat m : ℝ)
        - 1 := by
  have hvalid : (m.validityCode.toNat : ℝ) ≠ 0 := by
    have h := hm.2.2.1
    exact_mod_cast (show m.validityCode.toNat ≠ 0 by omega)
  have htime : Ephemeris.Proofs.Message.startTickNat m ≤ time.toNat := ht.1
  rw [Nat.cast_sub htime]
  dsimp [Definitions.PositionReconstruction.normalizedEpoch, Definitions.PositionReconstruction.normalizeEpoch,
    Definitions.PositionReconstruction.endEpoch, Definitions.PositionReconstruction.startEpoch,
    Definitions.PositionReconstruction.referenceDay, Definitions.PositionReconstruction.secondOfDay,
    Definitions.PositionReconstruction.validityHours, Definitions.PositionReconstruction.timeToReal,
    Ephemeris.Proofs.Message.startTickNat, Ephemeris.Proofs.Message.durationTicksNat,
    Definitions.Message.referenceDayTwice, Definitions.Message.validityFractionBits]
  push_cast
  field_simp
  ring

@[simp]
theorem model_zero_real
    : Definitions.Binary64Value.toReal (Float.Model.ofUInt8 0) = some (0 : ℝ) := by
  change some ((0 : Rat) : ℝ) = _
  norm_num

@[simp]
theorem model_one_real
    : Definitions.Binary64Value.toReal (Float.Model.ofUInt8 1) = some (1 : ℝ) := by
  change (Definitions.Binary64Value.toRational (Float.Model.ofNat 1)).map _ = _
  rw [ofNat_exact 1 (by norm_num)]
  norm_num

@[simp]
theorem model_two_real
    : Definitions.Binary64Value.toReal (Float.Model.ofUInt8 2) = some (2 : ℝ) := by
  change (Definitions.Binary64Value.toRational (Float.Model.ofNat 2)).map _ = _
  rw [ofNat_exact 2 (by norm_num)]
  norm_num

/-- Time normalization succeeds, and differs from the paper's real normalized epoch
by at most 3*2^-50. Integer subtraction precedes the first conversion. -/
theorem normalized_epoch_error (m : Message) (time : UInt64)
    (hm : Implementation.Correctness.Message.ValidMessage m)
    (ht : Implementation.Correctness.Message.InWindow m time)
    : ∃ v x,
        Implementation.Correctness.Float.modelNormalizedEpoch m time = some v
        ∧ Definitions.Binary64Value.toReal v = some x
        ∧ let exact :=
            Definitions.PositionReconstruction.normalizedEpoch
              (Definitions.PositionReconstruction.referenceDay m)
              (Definitions.PositionReconstruction.secondOfDay m)
              (Definitions.PositionReconstruction.validityHours m)
              (Definitions.PositionReconstruction.timeToReal time)
          |exact| ≤ 1 ∧ |x - exact| ≤ 3 * (2 : ℝ) ^ (-50 : Int) := by
  obtain ⟨hs, hd, _, hn, hnd, hb⟩ := Ephemeris.Proofs.Message.tickArithmeticCorrect m time hm ht
  let n := (time - Message.startTick m).toNat
  let d := (Message.durationTicks m).toNat
  have hdpos : 0 < d := by
    dsimp [d]
    rw [hd]
    have := hm.2.2.1
    dsimp [Ephemeris.Proofs.Message.durationTicksNat]
    omega
  have hnd' : n ≤ d := by simpa only [n, d, hd] using hnd
  have hb' : d < 2^53 := by simpa only [d, hd] using hb
  let exact := (n : ℝ) / (d : ℝ)
  have he0 : 0 ≤ exact := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)
  have he1 : exact ≤ 1 := (div_le_one (by exact_mod_cast hdpos)).mpr (by exact_mod_cast hnd')
  obtain ⟨r, hr, er⟩ := nat_div_error_real n d hdpos hnd' hb'
  have erb := abs_le.mp er
  have hrmag : |2 * r| ≤ (2 : ℝ)^(2 : Int) := by
    rw [show (2 : ℝ)^(2 : Int) = 4 by norm_num]
    norm_num at erb
    rw [abs_le]
    dsimp only [exact] at he0 he1
    constructor <;> linarith only [erb.1, erb.2, he0, he1]
  obtain ⟨s, hsval, es⟩ := mul_error_real (Float.Model.ofUInt8 2)
    (Float.Model.ofNat n / Float.Model.ofNat d) 2 r 2 model_two_real hr (by norm_num) (by norm_num) hrmag
  have esb := abs_le.mp es
  have hsmag : |s - 1| ≤ (2 : ℝ)^(2 : Int) := by
    norm_num at erb esb ⊢
    rw [abs_le]
    dsimp only [exact] at he0 he1
    constructor <;> linarith only [erb.1, erb.2, esb.1, esb.2, he0, he1]
  obtain ⟨x, hxval, ex⟩ := sub_error_real
    (Float.Model.ofUInt8 2 * (Float.Model.ofNat n / Float.Model.ofNat d)) (Float.Model.ofUInt8 1)
    s 1 2 hsval model_one_real (by norm_num) (by norm_num) hsmag
  let v := Float.Model.ofUInt8 2 * (Float.Model.ofNat n / Float.Model.ofNat d) - Float.Model.ofUInt8 1
  refine ⟨v, x, ?_, hxval, ?_⟩
  · unfold Implementation.Correctness.Float.modelNormalizedEpoch
    change (Implementation.Correctness.Float.modelFinite (Float.Model.ofNat n / Float.Model.ofNat d)).bind _ = _
    rewrite [finite_of_real _ _ hr]
    rewrite [Option.bind_some]
    change (Implementation.Correctness.Float.modelFinite
      (Float.Model.ofUInt8 2 * (Float.Model.ofNat n / Float.Model.ofNat d))).bind _ = _
    rewrite [finite_of_real _ _ hsval]
    rewrite [Option.bind_some]
    exact finite_of_real _ _ hxval
  · dsimp only
    rw [normalized_epoch_ticks m time hm ht, ← hn, ← hd]
    change |2 * (n : ℝ) / (d : ℝ) - 1| ≤ 1 ∧ |x - (2 * (n : ℝ) / (d : ℝ) - 1)| ≤ _
    have hexact : 2 * (n : ℝ) / (d : ℝ) - 1 = 2 * exact - 1 := by dsimp [exact]; ring
    rw [hexact]
    constructor
    · rw [abs_le]; constructor <;> linarith only [he0, he1]
    · rw [abs_le]
      have exb := abs_le.mp ex
      dsimp only [exact] at *
      norm_num at erb esb exb ⊢
      constructor <;> linarith only [erb.1, erb.2, esb.1, esb.2, exb.1, exb.2]
end Ephemeris.Proofs.EpochNormalization
