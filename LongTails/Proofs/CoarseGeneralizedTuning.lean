import LongTails.Algorithms.CoarseGeneralizedAccelerated
import LongTails.Proofs.GuardedHessianTuning

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

lemma coarseTolerance_pos (p : Params) (hp : spec.valid p) : 0 < coarseTolerance p := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  unfold coarseTolerance
  positivity

lemma warmCurvature_pos (p : Params) (hp : spec.valid p) : 0 < warmCurvature p := by
  have hζ := coarseTolerance_pos p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  unfold warmCurvature
  positivity

lemma warmCurvature_inflation (p : Params) (hp : spec.valid p) :
    p.L1 ^ 2 * p.R * coarseTolerance p ≤ warmCurvature p := by
  have hζ := coarseTolerance_pos p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  unfold warmCurvature
  have hn : 0 ≤ p.L1 ^ 2 * p.R * coarseTolerance p := by positivity
  nlinarith only [hn, hL0]

lemma restartGap_pos (p : Params) (hp : spec.valid p) : 0 < restartGap p := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  unfold restartGap
  positivity

lemma restartParams_valid (p : Params) (hp : spec.valid p) (x : p.E) :
    spec.valid (restartParams p x) := by
  have hB := restartGap_pos p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  exact ⟨hL0, hL1, hR, hB, hσ, hε, by dsimp [restartParams]; positivity,
    by dsimp [restartParams]; linarith⟩

lemma warm_depth_bound (p : Params) (hp : spec.valid p) :
    (1 / 2 : ℝ) ^ (warmTuning p).depth ≤ 1 / (2 ^ 20 * (1 + p.L1 * p.R) ^ 2) := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  apply LongTails.Proofs.GuardedHessianTuning.dyadic_log_bound (by positivity)
  have hh := Nat.le_ceil (Real.log (2 ^ 20 * (1 + p.L1 * p.R) ^ 2) / Real.log 2)
  dsimp [warmTuning]
  push_cast
  linarith

lemma warm_depth_geometry (p : Params) (hp : spec.valid p) :
    8 * (p.L1 * p.R) * (1 / 2 : ℝ) ^ (warmTuning p).depth ≤ 1 ∧
      65536 * (p.L1 * p.R) ^ 2 * (1 / 2 : ℝ) ^ (warmTuning p).depth ≤ 1 := by
  have hb := warm_depth_bound p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hL1 hR.le
  have hρ : 0 ≤ (1 / 2 : ℝ) ^ (warmTuning p).depth := by positivity
  have hd : 0 < (2 : ℝ) ^ 20 * (1 + p.L1 * p.R) ^ 2 := by positivity
  have hm := (le_div_iff₀ hd).mp hb
  have hc1 : 8 * (p.L1 * p.R) ≤ (2 : ℝ) ^ 20 * (1 + p.L1 * p.R) ^ 2 := by nlinarith [sq_nonneg (p.L1 * p.R)]
  have hc2 : 65536 * (p.L1 * p.R) ^ 2 ≤ (2 : ℝ) ^ 20 * (1 + p.L1 * p.R) ^ 2 := by nlinarith [sq_nonneg (p.L1 * p.R)]
  constructor
  · have ht := mul_le_mul_of_nonneg_right hc1 hρ
    nlinarith only [ht, hm]
  · have ht := mul_le_mul_of_nonneg_right hc2 hρ
    nlinarith only [ht, hm]

lemma warm_groups_bound (p : Params) (hp : spec.valid p) :
    (1 / 2 : ℝ) ^ warmGroups p ≤ p.δ / (4 * (1 + warmCalls p)) := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  have hb : (1 / 2 : ℝ) ^ warmGroups p ≤ 1 / (4 * (1 + warmCalls p) / p.δ) := by
    apply LongTails.Proofs.GuardedHessianTuning.dyadic_log_bound (by positivity)
    have hh := Nat.le_ceil (Real.log (4 * (1 + warmCalls p) / p.δ) / Real.log 2)
    unfold warmGroups
    push_cast
    linarith
  convert hb using 1
  field_simp

lemma warm_mean_variance (p : Params) (hp : spec.valid p) :
    (p.σ ^ 2 / 576) / (2 * coarseTolerance p / 6) ^ 2 ≤ 1 / 16 := by
  have hζ := coarseTolerance_pos p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  have hs : p.σ ≤ coarseTolerance p := by unfold coarseTolerance; linarith [mul_pos hL0 hR]
  have hsq := pow_le_pow_left₀ hσ hs 2
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr
  nlinarith only [hsq]

lemma warm_failure_bound (p : Params) (hp : spec.valid p) :
    (warmCalls p : ℝ) * (1 / 2 : ℝ) ^ warmGroups p ≤ p.δ / 4 := by
  have hb := warm_groups_bound p hp
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (warmCalls p))
  apply hm.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

lemma warm_rounds_large (p : Params) (hR : 1 ≤ p.L1 * p.R) :
    2050 * (p.L1 * p.R) < (warmTuning p).rounds := by
  have hh := Nat.le_ceil (p.L1 * p.R)
  dsimp [warmTuning]
  push_cast
  linarith

lemma warm_depth_pos (p : Params) : 0 < (warmTuning p).depth := by
  simp [warmTuning]

lemma low_gap_le_restart (p : Params) (hp : spec.valid p) (hR : 1 ≤ p.L1 * p.R) :
    4097 * p.R * warmCurvature p / p.L1 ≤ restartGap p := by
  rcases hp with ⟨hL0, hL1, hRp, hΔ, hσ, hε, hδ, hδ1⟩
  have hL1p : 0 < p.L1 := by nlinarith
  apply (div_le_iff₀ hL1p).mpr
  unfold warmCurvature coarseTolerance restartGap
  have hbase := mul_le_mul_of_nonneg_right hR (show 0 ≤ p.R * p.L0 by positivity)
  have ha : 0 ≤ p.L1 * p.R ^ 2 * p.L0 := by positivity
  have hb : 0 ≤ p.L1 ^ 2 * p.R ^ 3 * p.L0 := by positivity
  have hc : 0 ≤ p.L1 ^ 2 * p.R ^ 2 * p.σ := by positivity
  nlinarith only [hbase, ha, hb, hc]

lemma basic_gap_le_restart (p : Params) (hp : spec.valid p) :
    3 * p.L0 * p.R ^ 2 ≤ restartGap p := by
  rcases hp with ⟨hL0, hL1, hRp, hΔ, hσ, hε, hδ, hδ1⟩
  unfold restartGap
  have ha : 0 ≤ p.L0 * p.R ^ 2 := by positivity
  have hb : 0 ≤ p.L1 * p.R ^ 3 * p.L0 := by positivity
  have hc : 0 ≤ p.R ^ 2 * p.L1 * p.σ := by positivity
  nlinarith only [ha, hb, hc]

lemma warmCalls_pos (p : Params) (hR : 1 ≤ p.L1 * p.R) : 0 < warmCalls p := by
  have hr := warm_rounds_large p hR
  have hp : 0 < (warmTuning p).rounds := by exact_mod_cast (show (0 : ℝ) < (warmTuning p).rounds by linarith)
  unfold warmCalls
  rw [ite_eq_right (not_lt.mpr hR)]
  exact Nat.mul_pos hp (by omega)

end OracleTemplate.CoarseGeneralized
