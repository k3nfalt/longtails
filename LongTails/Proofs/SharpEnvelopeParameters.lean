import LongTails.Algorithms.SharpEnvelope
import LongTails.Proofs.SharpEnvelopeTuning
import LongTails.Proofs.InexactAcceleratedConvergence

namespace LongTails.Proofs.SharpEnvelopeParameters

open OracleTemplate LongTails.Algorithms.SharpEnvelope

lemma ratio_pos {b : ℕ} (hb : 1 ≤ b) : 0 < ratio b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (1 : ℝ) ≤ (b : ℝ) ^ 32 := one_le_pow₀ hbR
  unfold ratio
  linarith

lemma smoothness_pos {L : ℝ} (hL : 0 < L) {b : ℕ} (hb : 1 ≤ b) (i : ℕ) :
    0 < smoothness L b i := div_pos hL (pow_pos (ratio_pos hb) i)

lemma smoothness_succ (L : ℝ) {b : ℕ} (hb : 1 ≤ b) (i : ℕ) :
    smoothness L b i = ratio b * smoothness L b (i + 1) := by
  have hr := ne_of_gt (ratio_pos hb)
  unfold smoothness
  rw [pow_succ]
  field_simp

lemma precision_pos {b : ℕ} (hb : 1 ≤ b) (d i : ℕ) : 0 < precision b d i := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  unfold precision
  positivity

lemma precision_lower {b : ℕ} (hb : 1 ≤ b) (d i : ℕ) :
    1 / (100 * (b : ℝ) ^ 12) ≤ precision b d i := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  unfold precision
  gcongr
  have : 0 ≤ (i : ℝ) / (d + 1) := by positivity
  linarith

lemma precision_upper {b d i : ℕ} (hb : 1 ≤ b) (hi : i ≤ d) :
    precision b d i ≤ 1 / (50 * (b : ℝ) ^ 12) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hiR : (i : ℝ) ≤ d := by exact_mod_cast hi
  have hh : (i : ℝ) / (d + 1) ≤ 1 := (div_le_one hd).mpr (by linarith)
  unfold precision
  calc
    (1 + (i : ℝ) / (d + 1)) / (100 * (b : ℝ) ^ 12) ≤ 2 / (100 * (b : ℝ) ^ 12) := by
      gcongr
      linarith
    _ = _ := by ring

lemma precision_small {b d i : ℕ} (hb : 1 ≤ b) (hi : i ≤ d) :
    precision b d i ≤ 1 / 32 := by
  have hh := precision_upper hb hi
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (1 : ℝ) ≤ (b : ℝ) ^ 12 := one_le_pow₀ hbR
  have hle : 1 / (50 * (b : ℝ) ^ 12) ≤ 1 / 32 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  exact hh.trans hle

lemma precision_transfer {b d i : ℕ} (hb : 1 ≤ b) (hi : i ≤ d) :
    (1 + 2 * (1 / (8 * ((d : ℝ) + 1)))) * precision b d i ≤ precision b d (i + 1) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hiR : (i : ℝ) ≤ d := by exact_mod_cast hi
  unfold precision
  push_cast
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  field_simp
  nlinarith


lemma scaled_noise {b d i : ℕ} (hb : 1 ≤ b) (hi : i ≤ d) :
    precision b d i ^ 2 * (b : ℝ) ^ 32 ≤ (b : ℝ) ^ 16 / 2500 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hp := precision_upper hb hi
  have hz := (precision_pos hb d i).le
  have hprod : precision b d i * (b : ℝ) ^ 12 ≤ 1 / 50 := by
    rw [le_div_iff₀ (by positivity)] at hp
    nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ precision b d i * (b : ℝ) ^ 12) hprod 2
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ (b : ℝ) ^ 8 by positivity)
  have he : (precision b d i * (b : ℝ) ^ 12) ^ 2 * (b : ℝ) ^ 8 =
      precision b d i ^ 2 * (b : ℝ) ^ 32 := by ring
  rw [he] at hm
  have hpow : (b : ℝ) ^ 8 ≤ (b : ℝ) ^ 16 := pow_le_pow_right₀ hbR (by norm_num)
  nlinarith

lemma warm_momentum {L μ : ℝ} {b d i : ℕ} (hb : 1 ≤ b) (hi : i ≤ d)
    (hμ : 0 < μ) (hrel : L = ratio b * μ) :
    2 / InexactGradient.momentum (L + μ) μ (2 * precision b d i) ≤ 32 * (b : ℝ) ^ 16 := by
  let β := precision b d i
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hβ0 : 0 < β := precision_pos hb d i
  have hβ : β ≤ 1 / 32 := precision_small hb hi
  have hpow : (1 : ℝ) ≤ (b : ℝ) ^ 32 := one_le_pow₀ hbR
  have hsum : L + μ = 4 * (b : ℝ) ^ 32 * μ := by rw [hrel, ratio]; ring
  have hL : μ ≤ L + μ := by rw [hsum]; nlinarith
  have hd : 0 < μ * (1 - 2 * β) := mul_pos hμ (by linarith)
  obtain ⟨_, _, _, _, _, heq⟩ := InexactGradient.momentum_bounds hμ hL
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  rw [heq]
  have hr : (L + μ) / (μ * (1 - 2 * β)) ≤ 9 * ((b : ℝ) ^ 16) ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    rw [hsum]
    have hh : 1 / 2 ≤ 1 - 2 * β := by linarith
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ 9 * (b : ℝ) ^ 32 * μ by positivity)
    nlinarith only [hp, mul_nonneg (show 0 ≤ (b : ℝ) ^ 32 by positivity) hμ.le]
  have hs : Real.sqrt ((L + μ) / (μ * (1 - 2 * β))) ≤ 3 * (b : ℝ) ^ 16 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hr]
  have hn := scaled_noise hb hi
  change β ^ 2 * (b : ℝ) ^ 32 ≤ _ at hn
  have ht : 32 * (2 * β) ^ 2 * (L + μ) / (μ * (1 - 2 * β)) ≤ (b : ℝ) ^ 16 := by
    apply (div_le_iff₀ hd).mpr
    rw [hsum]
    have hh : 1 / 2 ≤ 1 - 2 * β := by linarith
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ (b : ℝ) ^ 16 * μ by positivity)
    have hnoise := mul_le_mul_of_nonneg_right hn hμ.le
    nlinarith only [hp, hnoise, mul_pos (pow_pos hb0 16) hμ]
  linarith only [hs, ht, pow_nonneg hb0.le 16]


lemma warm_logarithm {L μ : ℝ} {b d i : ℕ} (hb : 2 ≤ b)
    (hμ : 0 < μ) (hrel : L = ratio b * μ) :
    Real.log (1 + (L + μ) / (32 * precision b d i ^ 2 * μ)) ≤ 64 * (b : ℝ) := by
  let β := precision b d i
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hβ : 0 < β := precision_pos (by omega) d i
  have hp := precision_lower (by omega : 1 ≤ b) d i
  change 1 / (100 * (b : ℝ) ^ 12) ≤ β at hp
  have hprod : 1 / 100 ≤ β * (b : ℝ) ^ 12 := by
    rw [div_le_iff₀ (by positivity)] at hp
    nlinarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 100) hprod 2
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ (b : ℝ) ^ 32 by positivity)
  have hsum : L + μ = 4 * (b : ℝ) ^ 32 * μ := by rw [hrel, ratio]; ring
  have hid : (L + μ) / (32 * β ^ 2 * μ) = (b : ℝ) ^ 32 / (8 * β ^ 2) := by
    rw [hsum]
    field_simp
    norm_num
  have hratio : (b : ℝ) ^ 32 / (8 * β ^ 2) ≤ 1250 * (b : ℝ) ^ 56 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hm]
  have hb56 : (1 : ℝ) ≤ (b : ℝ) ^ 56 := one_le_pow₀ (by linarith)
  have hsum' : 1 + (b : ℝ) ^ 32 / (8 * β ^ 2) ≤ 2048 * (b : ℝ) ^ 56 := by
    linarith
  change Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) ≤ _
  rw [hid]
  have hlog := Real.log_le_log (by positivity : 0 < 1 + (b : ℝ) ^ 32 / (8 * β ^ 2)) hsum'
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl2048 : Real.log 2048 ≤ 11 := by
    have he : (2048 : ℝ) = 2 ^ 11 := by norm_num
    rw [he, Real.log_pow]
    norm_num
    linarith
  have hlb := Real.log_le_sub_one_of_pos hb0
  norm_num at hlog
  linarith

lemma warm_transient {L μ : ℝ} {b d i : ℕ} (hb : 16 ≤ b) (hi : i ≤ d)
    (hμ : 0 < μ) (hrel : L = ratio b * μ) :
    (1 - InexactGradient.momentum (L + μ) μ (2 * precision b d i) / 2) ^ (b ^ 20) * (L + μ) ≤
      32 * precision b d i ^ 2 * μ := by
  let β := precision b d i
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  have hβ : 0 < β := precision_pos (by omega) d i
  have hβsmall : β ≤ 1 / 32 := precision_small (by omega) hi
  have hL0 : 0 < L := by rw [hrel]; exact mul_pos (ratio_pos (by omega)) hμ
  have hL : μ ≤ L + μ := by linarith
  obtain ⟨ht0, ht1, _⟩ := InexactGradient.momentum_bounds hμ hL
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  refine PLGradient.geometric_budget 2 θ (L + μ) (32 * β ^ 2 * μ) ht0 (by linarith)
    (by linarith) (by positivity) (b ^ 20) ?_
  apply Nat.ceil_le.mpr
  have hc := warm_momentum (by omega : 1 ≤ b) hi hμ hrel
  have hl := warm_logarithm (d := d) (i := i) (by omega : 2 ≤ b) hμ hrel
  have hn : 0 ≤ Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) :=
    Real.log_nonneg (by
      have hp : 0 ≤ (L + μ) / (32 * β ^ 2 * μ) := by positivity
      linarith)
  have hh := mul_le_mul hc hl hn (by positivity : 0 ≤ 32 * (b : ℝ) ^ 16)
  have hbR : (16 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (2048 : ℝ) ≤ (b : ℝ) ^ 3 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hbR 3
    norm_num at ht
    linarith
  have hp' := mul_le_mul_of_nonneg_right hp (show 0 ≤ (b : ℝ) ^ 17 by positivity)
  change 2 / θ * Real.log (1 + (L + μ) / (32 * β ^ 2 * μ)) ≤ _ at hh
  push_cast
  dsimp [θ, β] at hh ⊢
  nlinarith only [hh, hp']


lemma sharp_scale {L μ : ℝ} {b : ℕ} (hb : 1 ≤ b) (hμ : 0 < μ)
    (hrel : L = ratio b * μ) : 1 / (4 * (L + μ)) = momentum b ^ 2 / μ := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hsum : L + μ = 4 * (b : ℝ) ^ 32 * μ := by rw [hrel, ratio]; ring
  rw [hsum, momentum]
  field_simp

lemma sharp_small {b d : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b) :
    momentum b ≤ (1 / (8 * ((d : ℝ) + 1))) / 8 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have hp : (b : ℝ) ≤ (b : ℝ) ^ 16 := by
    simpa using pow_le_pow_right₀ hbR (show 1 ≤ 16 by omega)
  have he : (1 / (8 * ((d : ℝ) + 1))) / 8 = 1 / (64 * ((d : ℝ) + 1)) := by
    field_simp
    ring
  rw [he, momentum]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma sharp_noise {b d i : ℕ} (hb : 16 ≤ b) (hi : i ≤ d)
    (hd : 16 * ((d : ℝ) + 1) ≤ b) :
    precision b d i ^ 2 ≤ (1 / (8 * ((d : ℝ) + 1))) * momentum b / 2 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have hp := precision_upper (by omega : 1 ≤ b) hi
  have hs := pow_le_pow_left₀ (precision_pos (by omega : 1 ≤ b) d i).le hp 2
  have he : (1 / (50 * (b : ℝ) ^ 12)) ^ 2 = 1 / (2500 * (b : ℝ) ^ 24) := by
    field_simp
    ring
  rw [he] at hs
  have hpow : (b : ℝ) ^ 17 ≤ (b : ℝ) ^ 24 := pow_le_pow_right₀ hbR (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ 4 * (b : ℝ) ^ 16 by positivity)
  have hd' : 64 * ((d : ℝ) + 1) * (b : ℝ) ^ 16 ≤ 2500 * (b : ℝ) ^ 24 := by
    nlinarith only [hh, hpow, pow_nonneg hb0.le 24]
  have hdiv := one_div_le_one_div_of_le
    (by positivity : 0 < 64 * ((d : ℝ) + 1) * (b : ℝ) ^ 16) hd'
  have he' : (1 / (8 * ((d : ℝ) + 1))) * momentum b / 2 =
      1 / (64 * ((d : ℝ) + 1) * (b : ℝ) ^ 16) := by
    unfold momentum
    field_simp
    ring
  rw [he']
  exact hs.trans hdiv

lemma sharp_average {b d : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b) :
    512 ≤ ((b ^ 20 : ℕ) : ℝ) * momentum b * (1 / (8 * ((d : ℝ) + 1))) := by
  have hbR : (16 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hp : (1024 : ℝ) ≤ (b : ℝ) ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hbR 3
    norm_num at hh
    linarith
  have hp' := mul_le_mul_of_nonneg_right hp hb0.le
  have he : ((b ^ 20 : ℕ) : ℝ) * momentum b * (1 / (8 * ((d : ℝ) + 1))) =
      (b : ℝ) ^ 4 / (32 * ((d : ℝ) + 1)) := by
    unfold momentum
    push_cast
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hp', hd]

end LongTails.Proofs.SharpEnvelopeParameters
