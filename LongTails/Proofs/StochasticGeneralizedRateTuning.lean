import LongTails.Proofs.StochasticGeneralizedCounting

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma power_two_thirds_cube {a : ℝ} (ha : 0 ≤ a) : (a^(2/3 : ℝ))^3 = a^2 := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

lemma eight_power_two_thirds {a : ℝ} (ha : 0 ≤ a) : (8*a)^(2/3 : ℝ) = 4*a^(2/3 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) ha]
  have he : (8 : ℝ)^(2/3 : ℝ) = 4 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  rw [he]

lemma exceptional_log_bound {S a r B : ℝ} (hS : 0 ≤ S) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (hB : 0 ≤ B) (hbound : B ≤ 1+8192*S^2+4194304*a^2*r) :
    2*Real.log (1+32*Real.sqrt B) ≤ 47+2*S+3*a^(2/3 : ℝ)+Real.log r := by
  let t := a^(2/3 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg ha _
  have ht3 : t^3 = a^2 := power_two_thirds_cube ha
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsq : (1+32*Real.sqrt B)^2 ≤ 4096*(1+B) := by
    have he := Real.sq_sqrt hB
    nlinarith [sq_nonneg (Real.sqrt B-1)]
  have hprod : 1+B ≤ (2+8192*S^2)*(1+4194304*a^2*r) := by
    have hx := mul_nonneg (sq_nonneg S) (mul_nonneg (sq_nonneg a) hrp.le)
    nlinarith [mul_nonneg (sq_nonneg a) hrp.le]
  have hleft : 2+8192*S^2 ≤ 8192*(1+S)^2 := by nlinarith
  have hright : 1+4194304*a^2*r ≤ 4194304*r*(1+t)^3 := by
    have ht' : 1+a^2 ≤ (1+t)^3 := by nlinarith [sq_nonneg t]
    have hm := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 4194304*r by positivity)
    nlinarith only [hm, hr]
  have hdom : 1+B ≤ 8192*(1+S)^2*(4194304*r*(1+t)^3) :=
    hprod.trans (mul_le_mul hleft hright (by positivity) (by positivity))
  have hlog1 := Real.log_le_log (show 0 < (1+32*Real.sqrt B)^2 by positivity) hsq
  have hlog2 := Real.log_le_log (show 0 < 1+B by positivity) hdom
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hlog1
  have h4096 : Real.log (4096 : ℝ) = 12*Real.log 2 := by
    rw [show (4096 : ℝ) = 2^12 by norm_num, Real.log_pow]
    norm_num
  rw [h4096] at hlog1
  have hex : Real.log (8192*(1+S)^2*(4194304*r*(1+t)^3)) =
      35*Real.log 2+2*Real.log (1+S)+Real.log r+3*Real.log (1+t) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) hrp.ne', Real.log_pow, Real.log_pow,
      show (8192 : ℝ) = 2^13 by norm_num, show (4194304 : ℝ) = 2^22 by norm_num,
      Real.log_pow, Real.log_pow]
    norm_num
    ring
  rw [hex] at hlog2
  have hSlog := Real.log_le_sub_one_of_pos (show 0 < 1+S by positivity)
  have htlog := Real.log_le_sub_one_of_pos (show 0 < 1+t by positivity)
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  change _ ≤ 47+2*S+3*t+Real.log r
  norm_num only [Nat.cast_ofNat] at hlog1
  linarith

lemma ratio_tuning {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    let C := (⌈a^(2/3 : ℝ)⌉₊ : ℝ)
    let L := Real.log (4+4*r)
    1 ≤ C ∧ a^(2/3 : ℝ) ≤ C ∧ 3/2 ≤ L ∧ Real.log r ≤ L := by
  have ht : 0 < a^(2/3 : ℝ) := Real.rpow_pos_of_pos ha _
  have hC : 1 ≤ (⌈a^(2/3 : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr ht : 0 < ⌈a^(2/3 : ℝ)⌉₊)
  have hlog2 := GeneralizedAccelerated.count_exponent_lower
  refine ⟨hC, Nat.le_ceil _, ?_, ?_⟩
  · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (show 8 ≤ 4+4*r by linarith)
    rw [show (8 : ℝ)=2^3 by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  · exact Real.log_le_log (by linarith) (by linarith)

lemma up_power_count_raw {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) (j : ℕ)
    (hp : (16 : ℝ)^j ≤ 262144*a^2*r) :
    ((j+1 : ℕ) : ℝ) ≤ 10+3/2*a^(2/3 : ℝ)+1/2*Real.log r := by
  have hrp : 0 < r := by linarith
  have ht := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ha (2/3 : ℝ))
  rw [Real.log_rpow ha] at ht
  have hl := Real.log_le_log (show 0 < (16 : ℝ)^j by positivity) hp
  rw [Real.log_pow, Real.log_mul (by positivity) hrp.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, show (16 : ℝ)=2^4 by norm_num, show (262144 : ℝ)=2^18 by norm_num,
    Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog2 := GeneralizedAccelerated.count_exponent_lower
  have hlog2u := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have hj := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ Real.log 2 by linarith)
    (show 0 ≤ (j : ℝ) by positivity)
  have hjb : (j : ℝ)+1 ≤ 10+3/2*a^(2/3 : ℝ)+1/2*Real.log r := by nlinarith
  simpa only [Nat.cast_add, Nat.cast_one] using hjb

lemma startup_count_simplify {a r m : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (hm : m ≤ 10+3/2*a^(2/3 : ℝ)+1/2*Real.log r) :
    m ≤ 16*(⌈a^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*r) := by
  let C := (⌈a^(2/3 : ℝ)⌉₊ : ℝ)
  let L := Real.log (4+4*r)
  have htune := ratio_tuning ha hr
  change 1 ≤ C ∧ a^(2/3 : ℝ) ≤ C ∧ 3/2 ≤ L ∧ Real.log r ≤ L at htune
  have hCL := mul_le_mul_of_nonneg_right htune.1 (show 0 ≤ L by linarith [htune.2.2.1])
  have hLC := mul_le_mul_of_nonneg_left htune.2.2.1 (show 0 ≤ C by linarith [htune.1])
  change m ≤ 16*C*L
  nlinarith [htune.1, htune.2.1, htune.2.2.1, htune.2.2.2]

lemma up_power_count_le {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) (j : ℕ)
    (hp : (16 : ℝ)^j ≤ 262144*a^2*r) :
    ((j+1 : ℕ) : ℝ) ≤ 16*(⌈a^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*r) :=
  startup_count_simplify ha hr (up_power_count_raw ha hr j hp)

lemma exceptional_count_simplify {S a r B : ℝ} (hS : 0 ≤ S) (ha : 0 < a) (hr : 1 ≤ r)
    (hB : 0 ≤ B) (hbound : B ≤ 1+8192*S^2+4194304*a^2*r) :
    2*Real.log (1+32*Real.sqrt B) ≤ 2*S+40*(⌈a^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*r) := by
  have he := exceptional_log_bound hS ha.le hr hB hbound
  have ht := ratio_tuning ha hr
  have hCL := mul_le_mul_of_nonneg_right ht.1 (show 0 ≤ Real.log (4+4*r) by linarith [ht.2.2.1])
  have hLC := mul_le_mul_of_nonneg_left ht.2.2.1 (show 0 ≤ (⌈a^(2/3 : ℝ)⌉₊ : ℝ) by positivity)
  nlinarith [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]

lemma high_count_simplify {a r A0 A : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (hA0 : 0 < A0) (hA : A0 ≤ A) (hbound : 2*A/A0 ≤ 64*r) :
    384*(1+(8*a)^(2/3 : ℝ))*Real.log (2*A/A0) ≤
      9216*(⌈a^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*r) := by
  have ht := ratio_tuning ha hr
  have hlog := Real.log_le_log (show 0 < 2*A/A0 by have := hA0.trans_le hA; positivity) hbound
  have hrp : 0 < r := by linarith
  rw [Real.log_mul (by norm_num) hrp.ne', show (64 : ℝ)=2^6 by norm_num, Real.log_pow] at hlog
  have h8 := Real.log_le_log (by norm_num : (0 : ℝ)<8) (show 8 ≤ 4+4*r by linarith)
  rw [show (8 : ℝ)=2^3 by norm_num, Real.log_pow] at h8
  norm_num only [Nat.cast_ofNat] at h8 hlog
  have hlog' : Real.log (2*A/A0) ≤ 3*Real.log (4+4*r) := by linarith [ht.2.2.2]
  rw [eight_power_two_thirds ha.le]
  have hm := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ 384*(1+4*a^(2/3 : ℝ)) by positivity)
  have hc : 384*(1+4*a^(2/3 : ℝ)) ≤ 3072*(⌈a^(2/3 : ℝ)⌉₊ : ℝ) := by linarith [ht.1, ht.2.1]
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ 3*Real.log (4+4*r) by linarith [ht.2.2.1])
  nlinarith only [hm, hc']

end OracleTemplate.StochasticGeneralized
