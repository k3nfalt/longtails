import LongTails.Algorithms.RecursiveEnvelope
import LongTails.Proofs.InexactAcceleratedConvergence

namespace LongTails.Proofs.RecursiveEnvelopeTuning

open LongTails.Algorithms.RecursiveEnvelope OracleTemplate

lemma levelSmoothness_pos {L : ℝ} (hL : 0 < L) (d i : ℕ) : 0 < levelSmoothness L d i := by
  unfold levelSmoothness
  positivity

lemma levelSmoothness_zero (L : ℝ) (d : ℕ) : levelSmoothness L d 0 = L := by
  simp [levelSmoothness]

lemma levelSmoothness_succ (L : ℝ) (d i : ℕ) :
    levelSmoothness L d i = (4 : ℝ) ^ d * levelSmoothness L d (i + 1) := by
  simp only [levelSmoothness, pow_succ]
  field_simp

lemma levelError_pos (d i : ℕ) : 0 < levelError d i := by
  unfold levelError
  positivity

lemma levelError_succ (d i : ℕ) : levelError d (i + 1) = 16 * levelError d i := by
  simp only [levelError, pow_succ]
  ring

lemma levelError_lower (d i : ℕ) : 1 / ((100 : ℝ) * 64 ^ d) ≤ levelError d i := by
  unfold levelError
  gcongr
  exact one_le_pow₀ (by norm_num)

lemma levelError_upper {d i : ℕ} (hi : i ≤ d) :
    levelError d i ≤ 1 / ((100 : ℝ) * 4 ^ d) := by
  have hp : (16 : ℝ) ^ i ≤ 16 ^ d := pow_le_pow_right₀ (by norm_num) hi
  have hid : (64 : ℝ) ^ d = 16 ^ d * 4 ^ d := by rw [← mul_pow]; norm_num
  unfold levelError
  rw [div_le_div_iff₀ (by positivity) (by positivity), hid]
  nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (100 : ℝ) * 4 ^ d)]

lemma levelError_small {d i : ℕ} (hi : i ≤ d) : levelError d i ≤ 1 / 32 := by
  have h1 := levelError_upper hi
  have hp : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have h2 : 1 / ((100 : ℝ) * 4 ^ d) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  exact h1.trans h2

lemma noise_condition {d i : ℕ} (hi : i ≤ d) :
    levelError d i ^ 2 * (1 + (4 : ℝ) ^ d) ≤ 2 / 10000 := by
  let β := levelError d i
  let u := (4 : ℝ) ^ d
  have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hb0 : 0 < β := levelError_pos d i
  have hb := levelError_upper hi
  change β ≤ 1 / (100 * u) at hb
  have hb1 : β * u ≤ 1 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hb
    nlinarith
  have hb2 : (β * u) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hb1 2
  have hu2 : 1 + u ≤ 2 * u ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hu2 (sq_nonneg β)
  change β ^ 2 * (1 + u) ≤ _
  nlinarith

lemma power_four (d : ℕ) : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

lemma power_sixtyfour (d : ℕ) : (64 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 6 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

lemma momentum_cost {L : ℝ} (hL : 0 < L) {d i : ℕ} (hi : i ≤ d) :
    2 / InexactGradient.momentum
      (levelSmoothness L d i + levelSmoothness L d (i + 1))
      (levelSmoothness L d (i + 1)) (2 * levelError d i) ≤ 40 * (2 : ℝ) ^ d := by
  let μ := levelSmoothness L d (i + 1)
  let β := levelError d i
  let u := (2 : ℝ) ^ d
  have hμ : 0 < μ := levelSmoothness_pos hL _ _
  have hβ0 : 0 < β := levelError_pos _ _
  have hβ : β ≤ 1 / 32 := levelError_small hi
  have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hLrel : levelSmoothness L d i = u ^ 2 * μ := by
    rw [levelSmoothness_succ L d i, power_four]
  obtain ⟨_, _, _, _, _, heq⟩ := InexactGradient.momentum_bounds hμ
    (show μ ≤ levelSmoothness L d i + μ by have := levelSmoothness_pos hL d i; linarith)
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  change 2 / InexactGradient.momentum (levelSmoothness L d i + μ) μ (2 * β) ≤ 40 * u
  rw [heq]
  have hden : 0 < μ * (1 - 2 * β) := mul_pos hμ (by linarith)
  have hratio : (levelSmoothness L d i + μ) / (μ * (1 - 2 * β)) ≤ 4 * u ^ 2 := by
    rw [div_le_iff₀ hden, hLrel]
    have hb : 1 / 2 ≤ 1 - 2 * β := by linarith
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * u ^ 2 * μ)
    nlinarith [sq_nonneg (u - 1)]
  have hs : Real.sqrt ((levelSmoothness L d i + μ) / (μ * (1 - 2 * β))) ≤ 2 * u := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have hn := noise_condition hi
  rw [power_four] at hn
  change β ^ 2 * (1 + u ^ 2) ≤ 2 / 10000 at hn
  have ht : 32 * (2 * β) ^ 2 * (levelSmoothness L d i + μ) / (μ * (1 - 2 * β)) ≤ 1 := by
    rw [div_le_iff₀ hden, hLrel]
    have hb : 256 * β ^ 2 * (1 + u ^ 2) ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hb hμ.le
    nlinarith
  linarith

lemma logarithm_cost {L : ℝ} (hL : 0 < L) {d i : ℕ} (hd : 1 ≤ d) :
    Real.log (1 + (levelSmoothness L d i + levelSmoothness L d (i + 1)) /
      (32 * levelError d i ^ 2 * levelSmoothness L d (i + 1))) ≤ 24 * d := by
  let μ := levelSmoothness L d (i + 1)
  let β := levelError d i
  let u := (2 : ℝ) ^ d
  have hμ : 0 < μ := levelSmoothness_pos hL _ _
  have hβ : 0 < β := levelError_pos _ _
  have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hl : levelSmoothness L d i = u ^ 2 * μ := by
    rw [levelSmoothness_succ L d i, power_four]
  have hb := levelError_lower d i
  rw [power_sixtyfour] at hb
  change 1 / (100 * u ^ 6) ≤ β at hb
  have hb1 : 1 / 100 ≤ β * u ^ 6 := by
    rw [div_le_iff₀ (by positivity)] at hb
    nlinarith
  have hb2 : (1 / 100 : ℝ) ^ 2 ≤ (β * u ^ 6) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hb1 2
  have hb3 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg u)
  have hr : (1 + u ^ 2) / (32 * β ^ 2) ≤ 625 * u ^ 14 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (u - 1)]
  have hid : (levelSmoothness L d i + μ) / (32 * β ^ 2 * μ) =
      (1 + u ^ 2) / (32 * β ^ 2) := by rw [hl]; field_simp; ring
  change Real.log (1 + (levelSmoothness L d i + μ) / (32 * β ^ 2 * μ)) ≤ _
  rw [hid]
  have hu14 : 1 ≤ u ^ 14 := one_le_pow₀ hu
  have hs : 1 + (1 + u ^ 2) / (32 * β ^ 2) ≤ (2 : ℝ) ^ (10 + 14 * d) := by
    have he : (2 : ℝ) ^ (10 + 14 * d) = 1024 * u ^ 14 := by
      rw [pow_add, Nat.mul_comm 14 d, pow_mul]
      norm_num [u]
    rw [he]
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + (1 + u ^ 2) / (32 * β ^ 2)) hs
  rw [Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ ((10 + 14 * d : ℕ) : ℝ))
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hlog hm
  nlinarith

lemma inner_transient {L : ℝ} (hL : 0 < L) {d i : ℕ} (hd : 1 ≤ d) (hi : i ≤ d) :
    (1 - InexactGradient.momentum
      (levelSmoothness L d i + levelSmoothness L d (i + 1))
      (levelSmoothness L d (i + 1)) (2 * levelError d i) / 2) ^ (2048 * d * 2 ^ d) *
      (levelSmoothness L d i + levelSmoothness L d (i + 1)) ≤
      32 * levelError d i ^ 2 * levelSmoothness L d (i + 1) := by
  let μ := levelSmoothness L d (i + 1)
  let β := levelError d i
  let A := levelSmoothness L d i + μ
  let θ := InexactGradient.momentum A μ (2 * β)
  have hμ : 0 < μ := levelSmoothness_pos hL _ _
  have hβ : 0 < β := levelError_pos _ _
  have hsmall : β ≤ 1 / 32 := levelError_small hi
  have hA : μ ≤ A := by have := levelSmoothness_pos hL d i; dsimp [A]; linarith
  obtain ⟨ht0, ht1, _⟩ := InexactGradient.momentum_bounds hμ hA
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  refine PLGradient.geometric_budget 2 θ A (32 * β ^ 2 * μ) ht0 (by linarith)
    (hμ.le.trans hA) (by positivity) (2048 * d * 2 ^ d) ?_
  apply Nat.ceil_le.mpr
  have hc := momentum_cost hL hi
  have hl := logarithm_cost (i := i) hL hd
  change 2 / θ ≤ 40 * (2 : ℝ) ^ d at hc
  change Real.log (1 + A / (32 * β ^ 2 * μ)) ≤ 24 * d at hl
  have hn : 0 ≤ Real.log (1 + A / (32 * β ^ 2 * μ)) :=
    Real.log_nonneg (by
      have hA0 : 0 ≤ A := hμ.le.trans hA
      have hfrac : 0 ≤ A / (32 * β ^ 2 * μ) := by positivity
      linarith)
  have hh := mul_le_mul hc hl hn (by positivity : 0 ≤ 40 * (2 : ℝ) ^ d)
  push_cast
  nlinarith [mul_nonneg (by positivity : 0 ≤ (d : ℝ)) (by positivity : 0 ≤ (2 : ℝ) ^ d)]

end LongTails.Proofs.RecursiveEnvelopeTuning
