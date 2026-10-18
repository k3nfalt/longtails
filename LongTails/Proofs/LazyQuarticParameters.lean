import LongTails.Algorithms.LazyQuarticMetric
import LongTails.Proofs.QuarticStageGuarantee

namespace LongTails.Proofs.LazyQuarticParameters

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric

lemma beta_pos (p : Params) (hp : spec.valid p) : 0 < beta p :=
  Real.sqrt_pos.mpr (mul_pos hp.1 hp.2.1)

lemma beta_square (p : Params) (hp : spec.valid p) : beta p ^ 2 = p.L₃ * p.Δ :=
  Real.sq_sqrt (mul_pos hp.1 hp.2.1).le

lemma alpha_pos (p : Params) (hp : spec.valid p) : 0 < alpha p := by
  apply lt_min
  · exact div_pos (beta_pos p hp) (by norm_num)
  · exact Real.rpow_pos_of_pos (mul_pos hp.1 (sq_pos_of_pos hp.2.2.2)) _

lemma alpha_cap (p : Params) : alpha p ≤ beta p / 2 ^ 24 := min_le_left _ _

lemma alpha_cube (p : Params) (hp : spec.valid p) : alpha p ^ 3 ≤ p.L₃ * p.ε ^ 2 := by
  have hh := pow_le_pow_left₀ (alpha_pos p hp).le
    (min_le_right (beta p / 2 ^ 24) ((p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ))) 3
  have he : ((p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = p.L₃ * p.ε ^ 2 := by
    rw [← Real.rpow_mul_natCast (mul_pos hp.1 (sq_pos_of_pos hp.2.2.2)).le]
    norm_num
  exact hh.trans_eq he

lemma condition_lower (p : Params) (hp : spec.valid p) : (2 : ℝ) ^ 24 ≤ condition p := by
  apply (le_div_iff₀ (alpha_pos p hp)).mpr
  have hh := alpha_cap p
  norm_num at hh ⊢
  linarith

lemma decrease_pos (p : Params) (hp : spec.valid p) : 0 < decrease p :=
  div_pos (sq_pos_of_pos (alpha_pos p hp)) (mul_pos (by norm_num) hp.1)

lemma radius_pos (p : Params) (hp : spec.valid p) : 0 < radius p :=
  div_pos (Real.sqrt_pos.mpr hp.2.1) (by norm_num)

lemma decrease_condition (p : Params) (hp : spec.valid p) :
    decrease p * (3072 * condition p ^ 2) = p.Δ := by
  unfold decrease condition
  have ha := (alpha_pos p hp).ne'
  have hL := hp.1.ne'
  rw [div_pow, beta_square p hp]
  field_simp

lemma logarithmArgument_ge_two (p : Params) (hp : spec.valid p) : 2 ≤ logarithmArgument p := by
  have h₁ : 0 ≤ p.H₀ * p.Δ / p.ε ^ 2 := div_nonneg (mul_nonneg hp.2.2.1 hp.2.1.le) (sq_nonneg _)
  have h₂ : 0 ≤ p.L₃ * p.Δ ^ 3 / p.ε ^ 4 := div_nonneg (mul_nonneg hp.1.le (pow_nonneg hp.2.1.le _)) (by positivity)
  unfold logarithmArgument
  linarith

lemma innerSteps_pos (p : Params) (hp : spec.valid p) : 0 < innerSteps p := by
  apply Nat.ceil_pos.mpr
  have hk : 0 < condition p := lt_of_lt_of_le (by norm_num) (condition_lower p hp)
  have hg : 0 < Real.log (logarithmArgument p) := Real.log_pos (lt_of_lt_of_le (by norm_num) (logarithmArgument_ge_two p hp))
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hk)) hg

lemma stages_sufficient (p : Params) (hp : spec.valid p) : p.Δ < (stages p : ℝ) * decrease p := by
  have hh := Nat.le_ceil (3072 * condition p ^ 2)
  have hd := mul_lt_mul_of_pos_right (show 3072 * condition p ^ 2 < (stages p : ℝ) by
    simp only [stages, Nat.cast_add, Nat.cast_one]
    linarith) (decrease_pos p hp)
  rw [mul_comm (3072 * condition p ^ 2), decrease_condition p hp] at hd
  exact hd

end LongTails.Proofs.LazyQuarticParameters
