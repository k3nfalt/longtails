import LongTails.Proofs.CoarseGeneralizedTuning
import LongTails.Proofs.RobustGeneralizedBudget

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

noncomputable def complexityScale (p : Params) : ℝ :=
  2 + p.L0 * p.R ^ 2 / p.ε + p.L1 * p.R + p.σ * p.R / p.ε

noncomputable def complexityLog (p : Params) : ℝ :=
  Real.log (Real.exp 1 * complexityScale p / p.δ)

lemma complexityScale_ge_two (p : Params) (hp : spec.valid p) : 2 ≤ complexityScale p := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  have hT : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by positivity
  have hh : 0 ≤ p.L1 * p.R := by positivity
  have hS : 0 ≤ p.σ * p.R / p.ε := by positivity
  unfold complexityScale
  linarith

lemma complexityLog_formula (p : Params) (hp : spec.valid p) :
    complexityLog p = 1 + Real.log (complexityScale p) - Real.log p.δ := by
  have hQ : 0 < complexityScale p := by linarith [complexityScale_ge_two p hp]
  unfold complexityLog
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hQ.ne') hp.2.2.2.2.2.2.1.ne',
    Real.log_mul (Real.exp_ne_zero _) hQ.ne', Real.log_exp]

lemma complexityLog_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ complexityLog p := by
  rw [complexityLog_formula p hp]
  have hQ := Real.log_nonneg (show 1 ≤ complexityScale p by linarith [complexityScale_ge_two p hp])
  have hd := Real.log_nonpos hp.2.2.2.2.2.2.1.le hp.2.2.2.2.2.2.2.le
  linarith

lemma complexityLog_components (p : Params) (hp : spec.valid p) :
    Real.log (complexityScale p) ≤ complexityLog p ∧ -Real.log p.δ ≤ complexityLog p := by
  rw [complexityLog_formula p hp]
  have hQ := Real.log_nonneg (show 1 ≤ complexityScale p by linarith [complexityScale_ge_two p hp])
  have hd := Real.log_nonpos hp.2.2.2.2.2.2.1.le hp.2.2.2.2.2.2.2.le
  constructor <;> linarith

lemma restart_confidence_le (p : Params) (hp : spec.valid p) (x : p.E) :
    RobustGeneralized.confidence (restartParams p x) ≤ 2 * complexityLog p := by
  have hδ := hp.2.2.2.2.2.2.1
  have hd : Real.log p.δ ≤ 0 := Real.log_nonpos hδ.le hp.2.2.2.2.2.2.2.le
  have hQ := Real.log_nonneg (show 1 ≤ complexityScale p by linarith [complexityScale_ge_two p hp])
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold RobustGeneralized.confidence
  dsimp only [restartParams]
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt (by positivity)), Real.log_exp,
    Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0), complexityLog_formula p hp]
  linarith

lemma restartGap_scaled (p : Params) (hp : spec.valid p) :
    restartGap p / p.ε ≤ 2 ^ 35 * (complexityScale p) ^ 2 := by
  have hε := hp.2.2.2.2.2.1
  have hT : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by have hL := hp.1; positivity
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hS : 0 ≤ p.σ * p.R / p.ε := by
    have hσ := hp.2.2.2.2.1
    have hR := hp.2.2.1
    positivity
  have he : restartGap p / p.ε = 2 ^ 35 *
      ((1 + p.L1 * p.R) * (p.L0 * p.R ^ 2 / p.ε) + (p.L1 * p.R) * (p.σ * p.R / p.ε)) := by
    unfold restartGap
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold complexityScale
  nlinarith [mul_nonneg hh hT, mul_nonneg hh hS, mul_nonneg hT hS]

lemma restart_gap_log_le (p : Params) (hp : spec.valid p) :
    Real.log (4 + 4 * restartGap p / p.ε) ≤ 41 * complexityLog p := by
  have hB := restartGap_scaled p hp
  have hQ := complexityScale_ge_two p hp
  have hQp : 0 < complexityScale p := by linarith
  have hε := hp.2.2.2.2.2.1
  have hBp := restartGap_pos p hp
  have ha : 0 < 4 + 4 * restartGap p / p.ε := by positivity
  have hb : 4 + 4 * restartGap p / p.ε ≤ (2 : ℝ) ^ 39 * (complexityScale p) ^ 2 := by
    rw [mul_div_assoc]
    nlinarith
  have hl := Real.log_le_log ha hb
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 39 ≠ 0) (pow_ne_zero _ hQp.ne'),
    Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog := (complexityLog_components p hp).1
  have hone := complexityLog_ge_one p hp
  linarith

lemma rpow_two_thirds_le_one_add {z : ℝ} (hz : 0 ≤ z) : z ^ (2 / 3 : ℝ) ≤ 1 + z := by
  by_cases h : z ≤ 1
  · have hh := Real.rpow_le_one hz h (by norm_num : (0 : ℝ) ≤ 2 / 3)
    linarith
  · have hh := Real.rpow_le_self_of_one_le (le_of_not_ge h) (by norm_num : (2 / 3 : ℝ) ≤ 1)
    linarith

lemma restart_shape_le (p : Params) (hp : spec.valid p) (x : p.E) :
    RobustGeneralized.shape (restartParams p x) ≤
      84 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) * complexityLog p := by
  have hlog := restart_gap_log_le p hp
  have hell := complexityLog_ge_one p hp
  have hB := restartGap_pos p hp
  have hε := hp.2.2.2.2.2.1
  have hln : 0 ≤ Real.log (4 + 4 * restartGap p / p.ε) := Real.log_nonneg (by
    have hh : 0 ≤ restartGap p / p.ε := by positivity
    rw [mul_div_assoc]
    linarith)
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
  have hr := rpow_two_thirds_le_one_add (mul_nonneg hh hln)
  have hm := mul_le_mul_of_nonneg_left hlog hh
  have hhs := mul_nonneg hh (sub_nonneg.mpr hell)
  have hss := mul_nonneg hs (sub_nonneg.mpr hell)
  dsimp [RobustGeneralized.shape, restartParams]
  nlinarith only [hlog, hell, hh, hs, hr, hm, hhs, hss]

lemma complexityScale_le_exp (p : Params) (hp : spec.valid p) :
    complexityScale p ≤ Real.exp (complexityLog p) := by
  have hQ : 0 < complexityScale p := by linarith [complexityScale_ge_two p hp]
  have hδ := hp.2.2.2.2.2.2.1
  unfold complexityLog
  rw [Real.exp_log (by positivity)]
  apply (le_div_iff₀ hδ).mpr
  have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have h1 := mul_le_mul_of_nonneg_left hp.2.2.2.2.2.2.2.le hQ.le
  have h2 := mul_le_mul_of_nonneg_right he hQ.le
  nlinarith only [h1, h2]

lemma restart_logScale_le (p : Params) (hp : spec.valid p) (x : p.E) :
    RobustGeneralized.logScale (restartParams p x) ≤ 64 * complexityLog p := by
  have hδ := hp.2.2.2.2.2.2.1
  have hell := complexityLog_ge_one p hp
  have hlog := restart_gap_log_le p hp
  have hQe := complexityScale_le_exp p hp
  have hle := Real.add_one_le_exp (complexityLog p)
  have hS : 0 ≤ p.σ * p.R / p.ε := by
    have hσ := hp.2.2.2.2.1
    have hR := hp.2.2.1
    have hε := hp.2.2.2.2.2.1
    positivity
  have hc : RobustGeneralized.comparisonScale (restartParams p x) ≤
      42 * Real.exp (complexityLog p) := by
    dsimp [RobustGeneralized.comparisonScale, restartParams]
    unfold complexityScale at hQe
    linarith
  have hcp : 0 < RobustGeneralized.comparisonScale (restartParams p x) := by
    linarith [RobustGeneralized.comparisonScale_ge_one (restartParams p x) (restartParams_valid p hp x)]
  have hl := Real.log_le_log hcp hc
  rw [Real.log_mul (by norm_num : (42 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hl
  have h42 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 42)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hd := (complexityLog_components p hp).2
  unfold RobustGeneralized.logScale
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hcp.ne')
    (show (restartParams p x).δ ≠ 0 by dsimp [restartParams]; positivity),
    Real.log_mul (Real.exp_ne_zero _) hcp.ne', Real.log_exp]
  change 1 + Real.log (RobustGeneralized.comparisonScale (restartParams p x)) - Real.log (p.δ / 2) ≤ _
  rw [Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

lemma warm_depth_le (p : Params) (hp : spec.valid p) :
    ((warmTuning p).depth : ℝ) ≤ 32 * complexityLog p := by
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hell := complexityLog_ge_one p hp
  have hT : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by
    have hL := hp.1
    have hε := hp.2.2.2.2.2.1
    positivity
  have hS : 0 ≤ p.σ * p.R / p.ε := by
    have hσ := hp.2.2.2.2.1
    have hR := hp.2.2.1
    have hε := hp.2.2.2.2.2.1
    positivity
  have hlog : Real.log (1 + p.L1 * p.R) ≤ complexityLog p :=
    (Real.log_le_log (by positivity) (show 1 + p.L1 * p.R ≤ complexityScale p by
      unfold complexityScale; linarith)).trans (complexityLog_components p hp).1
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h2
  have h2p : 0 < Real.log 2 := by linarith
  have harg : 1 ≤ (2 : ℝ) ^ 20 * (1 + p.L1 * p.R) ^ 2 := by nlinarith
  have hargp : 0 < (2 : ℝ) ^ 20 * (1 + p.L1 * p.R) ^ 2 := by linarith
  have hratio : Real.log (2 ^ 20 * (1 + p.L1 * p.R) ^ 2) / Real.log 2 ≤
      20 + 4 * complexityLog p := by
    apply (div_le_iff₀ h2p).mpr
    rw [Real.log_mul (by positivity : (2 : ℝ) ^ 20 ≠ 0) (by positivity), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hm := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * complexityLog p by linarith)
    nlinarith only [hm, hlog]
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg harg) h2p.le)
  dsimp [warmTuning]
  push_cast
  linarith

lemma warm_calls_le (p : Params) (hp : spec.valid p) :
    (warmCalls p : ℝ) ≤ 2 ^ 18 * (1 + p.L1 * p.R) * complexityLog p := by
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hell := complexityLog_ge_one p hp
  have hd := warm_depth_le p hp
  have hceil := Nat.ceil_lt_add_one hh
  have hr : ((warmTuning p).rounds : ℝ) ≤ 4096 * (1 + p.L1 * p.R) := by
    dsimp [warmTuning]
    push_cast
    linarith
  have hd' : ((warmTuning p).depth + 2 : ℝ) ≤ 64 * complexityLog p := by linarith
  unfold warmCalls
  split_ifs
  · simp only [Nat.cast_zero]
    positivity
  · push_cast
    have hm := mul_le_mul hr hd' (by positivity : (0 : ℝ) ≤ (warmTuning p).depth + 2)
      (by positivity : 0 ≤ 4096 * (1 + p.L1 * p.R))
    nlinarith only [hm]

lemma curvatureScale_le_complexityScale (p : Params) (hp : spec.valid p) :
    1 + p.L1 * p.R ≤ complexityScale p := by
  have hL := hp.1
  have hR := hp.2.2.1
  have hσ := hp.2.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hT : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by positivity
  have hS : 0 ≤ p.σ * p.R / p.ε := by positivity
  unfold complexityScale
  linarith

lemma warm_groups_le (p : Params) (hp : spec.valid p) :
    (warmGroups p : ℝ) ≤ 128 * complexityLog p := by
  have hell := complexityLog_ge_one p hp
  have hell0 : 0 ≤ complexityLog p := by linarith
  have hδ := hp.2.2.2.2.2.2.1
  have hδ1 := hp.2.2.2.2.2.2.2
  have hM := warm_calls_le p hp
  have hh := (curvatureScale_le_complexityScale p hp).trans (complexityScale_le_exp p hp)
  have he := Real.add_one_le_exp (complexityLog p)
  have he1 := Real.one_le_exp hell0
  have hprod := mul_le_mul hh (show complexityLog p ≤ Real.exp (complexityLog p) by linarith)
    hell0 (Real.exp_nonneg _)
  have hMb : 1 + (warmCalls p : ℝ) ≤ (2 : ℝ) ^ 19 * Real.exp (complexityLog p) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2 ^ 18)
    nlinarith only [hM, hm, he1, sq_nonneg (Real.exp (complexityLog p) - 1)]
  have harg : 1 ≤ 4 * (1 + (warmCalls p : ℝ)) / p.δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [show (0 : ℝ) ≤ warmCalls p from Nat.cast_nonneg _]
  have hargp : 0 < 4 * (1 + (warmCalls p : ℝ)) / p.δ := by positivity
  have hargb : 4 * (1 + (warmCalls p : ℝ)) / p.δ ≤
      (2 : ℝ) ^ 21 * Real.exp (complexityLog p) ^ 2 / p.δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith only [hMb]
  have hl := Real.log_le_log hargp hargb
  rw [Real.log_div (show (2 : ℝ) ^ 21 * Real.exp (complexityLog p) ^ 2 ≠ 0 by positivity) hδ.ne',
    Real.log_mul (show (2 : ℝ) ^ 21 ≠ 0 by positivity)
      (pow_ne_zero _ (Real.exp_ne_zero _)), Real.log_pow, Real.log_pow, Real.log_exp] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have h2lo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h2hi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h2lo h2hi
  have h2p : 0 < Real.log 2 := by linarith
  have hd := (complexityLog_components p hp).2
  have hlb : Real.log (4 * (1 + (warmCalls p : ℝ)) / p.δ) ≤ 24 * complexityLog p := by
    linarith
  have hratio : Real.log (4 * (1 + (warmCalls p : ℝ)) / p.δ) / Real.log 2 ≤
      48 * complexityLog p := by
    apply (div_le_iff₀ h2p).mpr
    have hm := mul_le_mul_of_nonneg_left h2lo (show 0 ≤ 48 * complexityLog p by positivity)
    nlinarith only [hm, hlb]
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg harg) h2p.le)
  unfold warmGroups
  push_cast
  linarith

lemma warm_cost_le (p : Params) (hp : spec.valid p) :
    (warmCost p : ℝ) ≤ 2 ^ 35 * (1 + p.L1 * p.R) * complexityLog p ^ 2 := by
  have hc := warm_calls_le p hp
  have hg := warm_groups_le p hp
  have hh : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hell : 0 ≤ complexityLog p := le_trans (by norm_num) (complexityLog_ge_one p hp)
  have hb : (warmBatch p : ℝ) ≤ 2 ^ 17 * complexityLog p := by
    unfold warmBatch
    push_cast
    nlinarith only [hg, hell]
  unfold warmCost
  push_cast
  have hm := mul_le_mul hc hb (Nat.cast_nonneg (warmBatch p))
    (show 0 ≤ 2 ^ 18 * (1 + p.L1 * p.R) * complexityLog p by positivity)
  nlinarith only [hm]

lemma total_cost_le (p : Params) (hp : spec.valid p) (x : p.E) :
    (warmCost p : ℝ) +
      (4194304 * RobustGeneralized.shape (restartParams p x) +
        140737488355328 * (p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2)) *
        RobustGeneralized.logScale (restartParams p x) ≤
      2 ^ 70 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) *
        complexityLog p ^ 3 := by
  let A := 1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)
  let V := p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2
  let ell := complexityLog p
  have hA : 0 ≤ A := by dsimp [A]; have hh := mul_nonneg hp.2.1 hp.2.2.1.le; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have he : 1 ≤ ell := complexityLog_ge_one p hp
  have he0 : 0 ≤ ell := by linarith
  have hq := restartParams_valid p hp x
  have hcpos : 0 ≤ RobustGeneralized.confidence (restartParams p x) := by
    have hh := StochasticGeneralized.confidence_log_gt_one hq.2.2.2.2.2.2.1 hq.2.2.2.2.2.2.2
    change 0 ≤ Real.log (Real.exp 1 / (restartParams p x).δ)
    linarith
  have hcsq := pow_le_pow_left₀ hcpos (restart_confidence_le p hp x) 2
  have hlogpos : 0 ≤ RobustGeneralized.logScale (restartParams p x) := by
    linarith [RobustGeneralized.logScale_ge_one (restartParams p x) hq]
  have hshape := restart_shape_le p hp x
  have hlog := restart_logScale_le p hp x
  have hnum : 4194304 * RobustGeneralized.shape (restartParams p x) +
      140737488355328 * (p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2) ≤
      4194304 * 84 * A * ell + 140737488355328 * V * (4 * ell ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hcsq hV
    have hid : p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2 =
        V * RobustGeneralized.confidence (restartParams p x) ^ 2 := by dsimp [V]; ring
    rw [hid]
    change RobustGeneralized.shape (restartParams p x) ≤ 84 * A * ell at hshape
    change V * RobustGeneralized.confidence (restartParams p x) ^ 2 ≤ V * (2 * ell) ^ 2 at hm
    nlinarith only [hm, hshape]
  have hm := mul_le_mul hnum hlog hlogpos
    (show 0 ≤ 4194304 * 84 * A * ell + 140737488355328 * V * (4 * ell ^ 2) by positivity)
  have hw := warm_cost_le p hp
  have hbase : 1 + p.L1 * p.R ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]
  have hw' := mul_le_mul_of_nonneg_right hbase (sq_nonneg ell)
  have he23 : ell ^ 2 ≤ ell ^ 3 := by nlinarith [mul_nonneg (sq_nonneg ell) (sub_nonneg.mpr he)]
  have hAE := mul_le_mul_of_nonneg_left he23 hA
  have hAE0 : 0 ≤ A * ell ^ 3 := by positivity
  have hVE0 : 0 ≤ V * ell ^ 3 := by positivity
  change (warmCost p : ℝ) + _ ≤ 2 ^ 70 * (A + V) * ell ^ 3
  change (warmCost p : ℝ) ≤ 2 ^ 35 * (1 + p.L1 * p.R) * ell ^ 2 at hw
  change _ ≤ (4194304 * 84 * A * ell + 140737488355328 * V * (4 * ell ^ 2)) * (64 * ell) at hm
  nlinarith only [hm, hw, hw', hAE, hAE0, hVE0]

lemma simplified_budget_suffices (p : Params) (hp : spec.valid p) :
    let K := ⌈2 ^ 70 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * complexityLog p ^ 3⌉₊
    warmCost p ≤ K ∧ ∀ x : p.E,
      (4194304 * RobustGeneralized.shape (restartParams p x) +
        140737488355328 * (p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2)) *
        RobustGeneralized.logScale (restartParams p x) ≤ (K - warmCost p : ℕ) := by
  dsimp only
  let K := ⌈2 ^ 70 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * complexityLog p ^ 3⌉₊
  have hcost (x : p.E) : 0 ≤
      (4194304 * RobustGeneralized.shape (restartParams p x) +
        140737488355328 * (p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2)) *
        RobustGeneralized.logScale (restartParams p x) := by
    have hq := restartParams_valid p hp x
    have hs := RobustGeneralized.shape_ge_one (restartParams p x) hq
    have hl := RobustGeneralized.logScale_ge_one (restartParams p x) hq
    positivity
  have ht (x : p.E) := (total_cost_le p hp x).trans (Nat.le_ceil _)
  change ∀ x : p.E, _ ≤ (K : ℝ) at ht
  have hK : warmCost p ≤ K := by
    have hh := ht p.x0
    have hn := hcost p.x0
    exact_mod_cast (show (warmCost p : ℝ) ≤ K by linarith)
  refine ⟨hK, ?_⟩
  intro x
  change _ ≤ ((K - warmCost p : ℕ) : ℝ)
  rw [Nat.cast_sub hK]
  linarith [ht x]

end OracleTemplate.CoarseGeneralized
