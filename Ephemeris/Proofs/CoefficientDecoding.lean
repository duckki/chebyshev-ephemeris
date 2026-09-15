import Ephemeris.Implementation.Correctness.Float
import Mathlib.Tactic.NormNum
import Std.Tactic.BVDecide

open Float.Model
open Float.Model.UnpackedFloat

/-!
# Binary64 coefficient conversion

Kernel-checked facts about the pinned Float.Model normalization and packing code.
These establish the native bounded signed-conversion adaptation and exact q/32
decoding for every Int32. They do not assume a general IEEE roundoff theorem.
-/

namespace Ephemeris.Proofs.CoefficientDecoding
theorem log2_shift (n k : Nat) (hn : 0 < n) : (n <<< k).log2 = n.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : n <<< k ≠ 0 := Nat.ne_of_gt (Nat.shiftLeft_pos_iff.mpr hn)
      have heq : n <<< (k + 1) = 2 * (n <<< k) := by
        simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq, Nat.log2_two_mul h, ih]
      omega

theorem shiftTarget_exact (s : Sign) (m : Nat) (e : Int)
    (hm : m.log2 = 52) (he : -1074 ≤ e)
    : roundWithAccuracy Format.binary64 s m e .exact
      = if h : m = 0 then .zero s else .finite s m e (Nat.pos_of_ne_zero h) := by
  have ht : Format.binary64.targetExponent (totalExponent m e) = e := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, hm, max_eq_left he]
  simp [roundWithAccuracy, shiftToTargetExponent, ht, shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, HShiftRight.hShiftRight,
    Nat.repeat]

private theorem round_small (s : Sign) (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : round Format.binary64 s n 0
      = .finite s (n <<< (52 - n.log2)) ((n.log2 : Int) - 52)
          (Nat.shiftLeft_pos_iff.mpr hn) := by
  have hk : n.log2 < 32 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  have ht : Format.binary64.targetExponent (totalExponent n 0) = (n.log2 : Int) - 52 := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hs : (0 - ((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
  have he : (0 : Int) - (52 - n.log2 : Nat) = (n.log2 : Int) - 52 := by omega
  have hm : (n <<< (52 - n.log2)).log2 = 52 := by rw [log2_shift n _ hn]; omega
  rw [round, ht, decreaseExponent, hs]
  dsimp only
  rw [he, shiftTarget_exact s _ _ hm (by omega)]
  simp [Nat.ne_of_gt (Nat.shiftLeft_pos_iff.mpr hn)]

theorem unpackSign_components (s : Sign) (e : BitVec 11) (m : BitVec 52)
    : unpackSign (packComponents Format.binary64 s e m) = s.toBitVec := by
  cases s <;> simp [unpackSign, packComponents, Sign.toBitVec] <;> bv_decide

theorem unpack_pack_normal (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = 52) (he : -1074 ≤ e) (he' : e ≤ 971)
    : (Float.Model.pack (.finite s m e hp)).unpack = .finite s m e hp := by
  have hbounds := (Nat.log2_eq_iff (Nat.ne_of_gt hp)).mp hm
  have hepos : 0 < (e + 1075).toNat := by omega
  have helim : (e + 1075).toNat < 2047 := by omega
  have hne : (BitVec.ofNat 11 (e + 1075).toNat) ≠ 0#11 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 1075).toNat % 2048 = 0 at hb
    omega
  have hni : (BitVec.ofNat 11 (e + 1075).toNat) ≠ -1#11 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 1075).toNat % 2048 = 2047 at hb
    omega
  have hexp : (((BitVec.ofNat 11 (e + 1075).toNat).toNat : Nat) : Int) - 1075 = e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmant : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    norm_num at hbounds ⊢
    omega
  unfold Float.Model.unpack Float.Model.pack
  simp only [UnpackedFloat.pack, Format.exponentBias,
    Format.binary64, Format.mantissaBits, hm]
  norm_num
  simp only [show e + 1023 + 52 = e + 1075 by omega,
    show ¬2048 ≤ (e + 1075).toNat + 1 by omega, ↓reduceIte]
  simp only [UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components, hne, hni, ↓reduceIte]
  change UnpackedFloat.finite (Sign.ofBitVec s.toBitVec) (1#1 ++ BitVec.ofNat 52 m).toNat
    ((BitVec.ofNat 11 (e + 1075).toNat).toNat - 1075) _ = _
  simp only [hexp, hmant]
  cases s <;> rfl

private theorem model_ofNat_small (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : Float.Model.ofNat n
      = Float.Model.pack
          (.finite .positive (n <<< (52 - n.log2)) ((n.log2 : Int) - 52)
            (Nat.shiftLeft_pos_iff.mpr hn)) := by
  unfold Float.Model.ofNat UnpackedFloat.ofNat UnpackedFloat.ofInt UnpackedFloat.normalize
  rw [Int.compare_eq_gt.mpr (by omega)]
  simp only [Int.toNat_natCast, round_small _ n hn hb]

private theorem model_ofInt_neg_small (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : Float.Model.ofInt (-(n : Int)) = -Float.Model.ofNat n := by
  have hk : n.log2 < 32 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  rw [model_ofNat_small n hn hb]
  change Float.Model.pack (UnpackedFloat.ofInt Format.binary64 (-(n : Int))) =
    Float.Model.pack ((Float.Model.pack _).unpack.neg)
  rw [unpack_pack_normal _ _ _ _ (by rw [log2_shift n _ hn]; omega) (by omega) (by omega)]
  unfold UnpackedFloat.ofInt UnpackedFloat.normalize
  rw [Int.compare_eq_lt.mpr (by omega)]
  simp only [Int.neg_neg, Int.toNat_natCast, round_small _ n hn hb]
  rfl

private theorem magnitude_toNat (q : Int32) (hq : q < 0)
    : ((-(q + 1)).toUInt32 + 1).toNat = (-q.toInt).toNat := by
  have hq' : q.toInt < 0 := Int32.lt_iff_toInt_lt.mp hq
  have hbound := q.toUInt32.toNat_lt
  have hint := BitVec.toInt_eq_toNat_cond q.toBitVec
  change q.toInt = if 2 * q.toUInt32.toNat < 4294967296 then
    (q.toUInt32.toNat : Int) else (q.toUInt32.toNat : Int) - 4294967296 at hint
  have hn : 0 < q.toUInt32.toNat := by split at hint <;> omega
  have hi : q.toInt = (q.toUInt32.toNat : Int) - 4294967296 := by split at hint <;> omega
  have hw : (-(q + 1)).toUInt32 + 1 = -q.toUInt32 := by
    simp only [Int32.toUInt32_neg, Int32.toUInt32_add]
    bv_decide
  rw [hw, UInt32.toNat_neg]
  change (4294967296 - q.toUInt32.toNat) % 4294967296 = _
  omega

private theorem model_signedConversion (q : Int32)
    : (if q < 0 then -((-(q + 1)).toUInt32 + 1).toFloat else q.toUInt32.toFloat).toModel
      = Float.Model.ofInt32 q := by
  split
  next hq =>
    change -Float.Model.ofNat ((-(q + 1)).toUInt32 + 1).toNat = Float.Model.ofInt q.toInt
    rw [magnitude_toNat q hq]
    have hq' : q.toInt < 0 := Int32.lt_iff_toInt_lt.mp hq
    have hlo := q.le_toInt
    have hn : 0 < (-q.toInt).toNat := by omega
    have hb : (-q.toInt).toNat < 2^32 := by omega
    have he : q.toInt = -((-q.toInt).toNat : Int) := by omega
    conv_rhs => rw [he]
    exact (model_ofInt_neg_small _ hn hb).symm
  next hq =>
    change Float.Model.ofInt (q.toUInt32.toNat : Int) = Float.Model.ofInt q.toInt
    congr 1
    have h : 0 ≤ q := by
      apply Int32.le_iff_toInt_le.mpr
      have hq' : ¬ q.toInt < 0 := fun h => hq (Int32.lt_iff_toInt_lt.mpr h)
      change 0 ≤ q.toInt
      omega
    rw [Int32.toNat_toUInt32_of_le h, Int32.toInt_eq_toNatClampNeg h]

/-- The bounded native conversion preserves the model bits for every signed carrier. -/
theorem coefficientModelsAgree
    : Ephemeris.Implementation.Correctness.Float.CoefficientModelsAgree := by
  intro q
  unfold Ephemeris.Implementation.PositionReconstruction.coefficient Ephemeris.Implementation.Correctness.Float.modelCoefficient
  change _ / (32.0 : Float).toModel = _
  rw [model_signedConversion]
  rfl

private theorem round_double (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = 52) (he : -1074 ≤ e)
    : roundWithAccuracy Format.binary64 s (2 * m) (e - 1) .exact = .finite s m e hp := by
  have ht : Format.binary64.targetExponent (totalExponent (2 * m) (e - 1)) = e := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent,
      Nat.log2_two_mul (Nat.ne_of_gt hp), hm]
    omega
  have ht' : Format.binary64.targetExponent (totalExponent m e) = e := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent,
      hm, max_eq_left he]
  have hd : (2 * m) / 2 = m := by omega
  have hr : (2 * m) % 2 = 0 := by omega
  simp [roundWithAccuracy, shiftToTargetExponent, ht, ht', shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.shiftRightOne, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven,
    HShiftRight.hShiftRight, Nat.repeat, hd, hr, Nat.ne_of_gt hp]

private theorem div_thirtyTwo (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = 52) (he : -1068 ≤ e) (he' : e ≤ 971)
    : Float.Model.pack (.finite s m e hp) / Float.Model.ofUInt8 32
      = Float.Model.pack (.finite s m (e - 5) hp) := by
  have hc : (Float.Model.ofUInt8 32).unpack =
      .finite .positive (2^52) (-47) (by decide) := by rfl
  change Float.Model.pack (UnpackedFloat.div Format.binary64
    ((Float.Model.pack _).unpack) ((Float.Model.ofUInt8 32).unpack)) = _
  rw [unpack_pack_normal s m e hp hm (by omega) he', hc]
  have ht : Format.binary64.targetExponent
      (totalExponent m e - totalExponent (2^52) (-47)) = e - 6 := by
    simp only [totalExponent, hm, Nat.log2_two_pow]
    norm_num [Format.targetExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hs : min (e - -47) (e - 6) = e - 6 := by omega
  have hmdiv : (m <<< 53) / 2^52 = 2 * m := by
    rw [Nat.shiftLeft_eq]
    have heq : m * 2^53 = (2*m) * 2^52 := by omega
    rw [heq, Nat.mul_div_cancel]
    decide
  have hmod : (m <<< 53) % 2^52 = 0 := by
    rw [Nat.shiftLeft_eq]
    have heq : m * 2^53 = (2*m) * 2^52 := by omega
    rw [heq, Nat.mul_mod_left]
  simp only [UnpackedFloat.div, divCore, ht, hs, show e - -47 - (e - 6) = 53 by omega]
  simp only [show (53 : Int).toNat = 53 by decide, hmdiv, hmod, accuracyOfFraction, ↓reduceIte]
  have hsign : s / Sign.positive = s := by cases s <;> rfl
  rw [hsign]
  have heq : e - 6 = (e - 5) - 1 := by omega
  rw [heq, round_double s m (e - 5) hp hm (by omega)]

private theorem model_ofInt_signed_small (s : Sign) (n : Nat) (hn : 0 < n)
    (hb : n < 2 ^ 32)
    : Float.Model.ofInt (s.apply (n : Int))
      = Float.Model.pack
          (.finite s (n <<< (52 - n.log2)) ((n.log2 : Int) - 52)
            (Nat.shiftLeft_pos_iff.mpr hn)) := by
  cases s with
  | positive => exact model_ofNat_small n hn hb
  | negative =>
      simp only [Sign.apply]
      unfold Float.Model.ofInt UnpackedFloat.ofInt UnpackedFloat.normalize
      rw [Int.compare_eq_lt.mpr (by omega)]
      simp only [Int.neg_neg, Int.toNat_natCast, round_small _ n hn hb]

private theorem scaled_coefficient_value (n : Nat) (hk : n.log2 ≤ 52)
    : ((n <<< (52 - n.log2) : Nat) : Rat) * (2 : Rat) ^ ((n.log2 : Int) - 52 - 5)
      = (n : Rat) / 32 := by
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [← zpow_natCast]
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  have he : ((52 - n.log2 : Nat) : Int) + ((n.log2 : Int) - 52 - 5) = -5 := by omega
  rw [he]
  norm_num [zpow_neg, div_eq_mul_inv]

private theorem coefficient_signed_value (s : Sign) (n : Nat) (hn : 0 < n)
    (hb : n < 2 ^ 32)
    : Definitions.Binary64Value.toRational
        (Float.Model.ofInt (s.apply (n : Int)) / Float.Model.ofUInt8 32)
      = some ((s.apply (n : Int) : Rat) / 32) := by
  have hk : n.log2 < 32 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  have hm : (n <<< (52 - n.log2)).log2 = 52 := by rw [log2_shift n _ hn]; omega
  rw [model_ofInt_signed_small s n hn hb, div_thirtyTwo s _ _ _ hm (by omega) (by omega)]
  unfold Definitions.Binary64Value.toRational
  rw [unpack_pack_normal s _ _ _ hm (by omega) (by omega)]
  simp only [Definitions.Binary64Value.unpackedToRational]
  have hvalue := scaled_coefficient_value n (by omega)
  cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, neg_div]
  · rw [hvalue]
  · rw [hvalue]

private theorem coefficient_rational_value (q : Int32)
    : Definitions.Binary64Value.toRational
        (Implementation.Correctness.Float.modelCoefficient q)
      = some ((q.toInt : Rat) / 32) := by
  change Definitions.Binary64Value.toRational (Float.Model.ofInt q.toInt / Float.Model.ofUInt8 32) = _
  have hlo := q.le_toInt
  have hhi := q.toInt_lt
  by_cases hz : q.toInt = 0
  · rw [hz]
    change some (0 : Rat) = _
    norm_num
  by_cases hneg : q.toInt < 0
  · have hn : 0 < (-q.toInt).toNat := by omega
    have hb : (-q.toInt).toNat < 2^32 := by omega
    have he : q.toInt = Sign.negative.apply ((-q.toInt).toNat : Int) := by
      simp only [Sign.apply]
      omega
    rw [he]
    exact coefficient_signed_value .negative _ hn hb
  · have hn : 0 < q.toInt.toNat := by omega
    have hb : q.toInt.toNat < 2^32 := by omega
    have he : q.toInt = Sign.positive.apply (q.toInt.toNat : Int) := by
      simp only [Sign.apply]
      omega
    rw [he]
    exact coefficient_signed_value .positive _ hn hb

/-- Decoding any Int32 coefficient at scale 2^-5 introduces no numerical error. -/
theorem coefficientDecodingExact
    : Implementation.Correctness.Float.CoefficientDecodingExact := by
  intro q
  unfold Definitions.Binary64Value.toReal
  rw [coefficient_rational_value]
  norm_num [Definitions.PositionReconstruction.coefficient, Definitions.Message.coefficientFractionBits]

end Ephemeris.Proofs.CoefficientDecoding
