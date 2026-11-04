import LongTails.Proofs.TensorFreeModelTuning
import LongTails.Algorithms.QuarticProximalTrial
import LongTails.Proofs.GradientOnlyExecution
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.QuarticStageTuning

lemma logarithm_cap {Q : ℝ} (hQ : 3 ≤ Q) :
    (1 + ⌈Real.log Q⌉₊ : ℝ) ≤ 2 * Q := by
  have hlog := Real.log_nonneg (show 1 ≤ Q by linarith)
  have hceil := Nat.ceil_lt_add_one hlog
  have hl := Real.log_le_sub_one_of_pos (show 0 < Q by linarith)
  linarith

lemma stage_contraction {Q : ℝ} (hQ : 3 ≤ Q) :
    (3 / 4 : ℝ) ^ (64 * (1 + ⌈Real.log Q⌉₊)) ≤ 1 / Q ^ 16 := by
  have hQpos : 0 < Q := by linarith
  have hceil := Nat.le_ceil (Real.log Q)
  have hh := GradientOnlyExecution.pow_le_exp (a := (1 / 4 : ℝ)) (by norm_num)
    (64 * (1 + ⌈Real.log Q⌉₊))
  norm_num only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hh
  apply hh.trans
  have he : Real.exp (-((16 : ℝ) * Real.log Q)) = 1 / Q ^ 16 := by
    rw [Real.exp_neg, show (16 : ℝ) = (16 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hQpos, one_div]
  rw [← he]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

lemma restart_contraction {Q : ℝ} (hQ : 3 ≤ Q) :
    (1 / 2 : ℝ) ^ (24 * (1 + ⌈Real.log Q⌉₊)) ≤ 1 / Q ^ 16 := by
  have hQpos : 0 < Q := by linarith
  have hceil := Nat.le_ceil (Real.log Q)
  have hlog := Real.log_nonneg (show 1 ≤ Q by linarith)
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : Real.exp (-((16 : ℝ) * Real.log Q)) = 1 / Q ^ 16 := by
    rw [Real.exp_neg, show (16 : ℝ) = (16 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hQpos, one_div]
  have he2 : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  rw [he2, ← Real.exp_nat_mul, ← he]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

lemma stage_failure_tuning {Q : ℝ} (hQ : 3 ≤ Q) {n N : ℕ} (hN : 0 < N)
    (hnQ : (n : ℝ) ≤ Q) (hNQ : (N : ℝ) ≤ 256 * Q) :
    (n : ℝ) * (1 / 2 : ℝ) ^ (24 * (1 + ⌈Real.log Q⌉₊)) ≤
      (1 / (4 * (64 * (1 + ⌈Real.log Q⌉₊ : ℝ)) * N)) / 2 := by
  have hQpos : 0 < Q := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hell := logarithm_cap hQ
  have h13 : (262144 : ℝ) ≤ Q ^ 13 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 13
    norm_num at hh
    linarith
  have hprod : 8 * (64 * (1 + ⌈Real.log Q⌉₊ : ℝ)) * N * n ≤ Q ^ 16 := by
    calc
      _ ≤ 8 * (64 * (2 * Q)) * (256 * Q) * Q := by gcongr
      _ = 262144 * Q ^ 3 := by ring
      _ ≤ Q ^ 13 * Q ^ 3 := mul_le_mul_of_nonneg_right h13 (by positivity)
      _ = Q ^ 16 := by ring
  calc
    _ ≤ (n : ℝ) * (1 / Q ^ 16) := mul_le_mul_of_nonneg_left (restart_contraction hQ) (by positivity)
    _ ≤ _ := by
      rw [div_div]
      apply (le_div_iff₀ (by positivity)).mpr
      have hh : (8 * (64 * (1 + ⌈Real.log Q⌉₊ : ℝ)) * N * n) / Q ^ 16 ≤ 1 :=
        (div_le_iff₀ (by positivity)).mpr (by simpa using hprod)
      convert hh using 1; ring


lemma terminal_gradient_bound {γ L r Δ gap a Q : ℝ}
    (hγ : 0 < γ) (hL : 0 ≤ L) (hr : 0 ≤ r) (hgap : 0 ≤ gap) (hQ : 3 ≤ Q)
    (hκ : L ≤ γ * Q ^ 2) (hinit : γ * Δ ^ 3 ≤ 1000 * L ^ 4 * r ^ 12)
    (hstage : gap ≤ Δ / Q ^ 16) (hmodel : a ^ 4 ≤ 2 * L * gap ^ 3) :
    a ≤ γ * r ^ 3 / 2048 := by
  have hQpos : 0 < Q := by linarith
  have hlarge : (2000 * 2048 ^ 4 : ℝ) ≤ Q ^ 38 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 38
    norm_num at hh ⊢
    linarith
  have hinit' : Δ ^ 3 ≤ 1000 * L ^ 4 * r ^ 12 / γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith [hinit]
  have ha : a ^ 4 ≤ (γ * r ^ 3 / 2048) ^ 4 := by
    calc
      a ^ 4 ≤ 2 * L * gap ^ 3 := hmodel
      _ ≤ 2 * L * (Δ / Q ^ 16) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgap hstage 3) (by positivity)
      _ = (2 * L / Q ^ 48) * Δ ^ 3 := by field_simp
      _ ≤ (2 * L / Q ^ 48) * (1000 * L ^ 4 * r ^ 12 / γ) := mul_le_mul_of_nonneg_left hinit' (by positivity)
      _ = (2000 * r ^ 12 / (γ * Q ^ 48)) * L ^ 5 := by ring
      _ ≤ (2000 * r ^ 12 / (γ * Q ^ 48)) * (γ * Q ^ 2) ^ 5 := by gcongr
      _ = 2000 * (γ ^ 4 * r ^ 12) / Q ^ 38 := by field_simp
      _ ≤ (γ ^ 4 * r ^ 12) / 2048 ^ 4 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hlarge (show 0 ≤ γ ^ 4 * r ^ 12 by positivity)]
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity) ha


lemma epoch_count_suffices {n : ℕ} [NeZero n] {L γ : ℝ} (hγ : 0 < γ)
    (hL : L ≤ (n : ℝ) * γ) :
    2 * ((n : ℝ) + 6144 * (L + 6 * γ) / γ) ≤
      (n * LongTails.Algorithms.QuarticProximalTrial.epochCount : ℕ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hratio : (L + 6 * γ) / γ ≤ (n : ℝ) + 6 := by
    apply (div_le_iff₀ hγ).mpr
    nlinarith
  norm_num [LongTails.Algorithms.QuarticProximalTrial.epochCount]
  rw [mul_div_assoc]
  nlinarith

lemma trial_query_count (n ell : ℕ) (hell : 1 ≤ ell) :
    3 * ((n + (n + n)) * (5000 * ell + 1) + n) +
      (((n + n) * LongTails.Algorithms.QuarticProximalTrial.epochCount) * (24 * ell + 1)) * (64 * ell) ≤
        2 ^ 29 * n * ell ^ 2 := by
  have he : ell ≤ ell ^ 2 := by nlinarith
  have hne := Nat.mul_le_mul_left n he
  have hn : n ≤ n * ell := by nlinarith
  norm_num [LongTails.Algorithms.QuarticProximalTrial.epochCount]
  nlinarith

end LongTails.Proofs.QuarticStageTuning
