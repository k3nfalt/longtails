import LongTails.Proofs.StochasticGeneralizedWeights
import LongTails.Algorithms.StochasticGeneralizedAccelerated

open OracleTemplate.GeneralizedAccelerated
open LongTails.Setups.GeneralizedSmoothAndConvex

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma confidence_log_gt_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 < Real.log (Real.exp 1/δ) := by
  rw [Real.log_div (Real.exp_ne_zero _) hδ.ne', Real.log_exp]
  linarith [Real.log_neg hδ hδ1]

lemma batchSize_pos {E : Type*} (σ ε δ : ℝ) (s : Iterate E) : 0 < batchSize σ ε δ s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma batchSize_noise_scale {E : Type*} {σ ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) (s : Iterate E) (hG : 0 < s.guess) :
    32*σ^2/(batchSize σ ε δ s : ℝ) ≤
      (ε/(32768*Real.log (Real.exp 1/δ)))/tentativeWeight s := by
  have ha : 0 < tentativeWeight s := by unfold tentativeWeight; positivity
  have hℓ : 0 < Real.log (Real.exp 1/δ) := lt_trans zero_lt_one (confidence_log_gt_one hδ hδ1)
  have hm : 0 < (batchSize σ ε δ s : ℝ) := by exact_mod_cast batchSize_pos σ ε δ s
  have hceil := Nat.le_ceil (1048576*σ^2*tentativeWeight s*Real.log (Real.exp 1/δ)/ε)
  have hmax : (⌈1048576*σ^2*tentativeWeight s*Real.log (Real.exp 1/δ)/ε⌉₊ : ℝ) ≤
      (batchSize σ ε δ s : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  have hbound := hceil.trans hmax
  have hc := (div_le_iff₀ hε).mp hbound
  apply (div_le_div_iff₀ hm ha).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 32768*Real.log (Real.exp 1/δ) by positivity)).mpr
  nlinarith only [hc]

lemma tuning_small {R ε ℓ a : ℝ} (hR : 0 < R) (hε : 0 < ε) (hℓ : 0 < ℓ)
     (hab : a ≤ 32*(16*R^2/ε)) :
    12*(ℓ/R^2)*(ε/(32768*ℓ))*a ≤ 1 := by
  have hm := mul_le_mul_of_nonneg_left hab (show 0 ≤ 12*(ℓ/R^2)*(ε/(32768*ℓ)) by positivity)
  have he : 12*(ℓ/R^2)*(ε/(32768*ℓ))*(32*(16*R^2/ε)) = (3/16 : ℝ) := by
    field_simp; ring
  rw [he] at hm
  linarith

lemma tuning_compensator {R ε ℓ : ℝ} (hR : 0 < R) (hε : 0 < ε) (hℓ : 1 ≤ ℓ) :
    (14*(ℓ/R^2)*(ε/(32768*ℓ))+32*(ℓ/R^2)^2*(ε/(32768*ℓ))*R^2)*
      (32*(16*R^2/ε)) ≤ ℓ := by
  have hℓpos : 0 < ℓ := by linarith
  have he : (14*(ℓ/R^2)*(ε/(32768*ℓ))+32*(ℓ/R^2)^2*(ε/(32768*ℓ))*R^2)*
      (32*(16*R^2/ε)) = 7/32+ℓ/2 := by
    field_simp; ring
  rw [he]
  linarith

end OracleTemplate.StochasticGeneralized
