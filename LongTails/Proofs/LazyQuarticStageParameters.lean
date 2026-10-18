import LongTails.Proofs.LazyQuarticParameters

namespace LongTails.Proofs.LazyQuarticStageParameters

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric

noncomputable def metricRadius (p : Params) : ℝ :=
  Real.sqrt (2 * decrease p / (alpha p / (64 * beta p)))

noncomputable def euclideanRadius (p : Params) : ℝ := Real.sqrt (decrease p / alpha p)

lemma basic_scales (p : Params) (hp : spec.valid p) (st : State p) :
    0 < (parameters p st).μ ∧ 0 ≤ (parameters p st).a ∧ (parameters p st).a ≤ 1 ∧
      (parameters p st).a ^ 2 * (parameters p st).L = (parameters p st).μ ∧
      (parameters p st).μ ≤ 1 / 8 ∧ (parameters p st).μ * beta p = alpha p / 64 := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hc := LazyQuarticParameters.alpha_cap p
  have hs := Real.sq_sqrt (show 0 ≤ alpha p / (256 * beta p) by positivity)
  have ham : alpha p ≤ beta p := by norm_num at hc; linarith
  change 0 < alpha p / (64 * beta p) ∧ 0 ≤ Real.sqrt (alpha p / (256 * beta p)) ∧
    Real.sqrt (alpha p / (256 * beta p)) ≤ 1 ∧
    Real.sqrt (alpha p / (256 * beta p)) ^ 2 * 4 = alpha p / (64 * beta p) ∧
    alpha p / (64 * beta p) ≤ 1 / 8 ∧ alpha p / (64 * beta p) * beta p = alpha p / 64
  refine ⟨by positivity, Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 256 * beta p)).mpr
    nlinarith
  · rw [hs]
    ring
  · apply (div_le_iff₀ (by positivity : 0 < 64 * beta p)).mpr
    linarith
  · field_simp

lemma radii_square (p : Params) (hp : spec.valid p) (st : State p) :
    metricRadius p ^ 2 = 2 * (parameters p st).q / (parameters p st).μ ∧
      (parameters p st).α * euclideanRadius p ^ 2 = (parameters p st).q := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hq := LazyQuarticParameters.decrease_pos p hp
  constructor
  · exact Real.sq_sqrt (by positivity)
  · change alpha p * (Real.sqrt (decrease p / alpha p)) ^ 2 = decrease p
    rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma escape_square (p : Params) (hp : spec.valid p) (st : State p) :
    (parameters p st).η ^ 2 = alpha p / (16 * p.L₃) := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  exact Real.sq_sqrt (div_nonneg ha.le (mul_pos (by norm_num) hp.1).le)

lemma accuracy_scale (p : Params) (hp : spec.valid p) : decrease p ≤ p.ε ^ 2 / (16 * alpha p) := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hc := LazyQuarticParameters.alpha_cube p hp
  unfold decrease
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hp.1) (by positivity : 0 < 16 * alpha p)).mpr
  have he : 0 ≤ p.L₃ * p.ε ^ 2 := mul_nonneg hp.1.le (sq_nonneg _)
  nlinarith

lemma escape_scales (p : Params) (hp : spec.valid p) (st : State p) :
    p.L₃ * (parameters p st).η ^ 2 = alpha p / 16 ∧
      15 * decrease p ≤ alpha p * (parameters p st).η ^ 2 / 4 ∧
      (parameters p st).μ * (8 * metricRadius p ^ 2 + 40 * beta p * (parameters p st).η ^ 2) ≤ 256 * decrease p := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hL := hp.1
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hA := (radii_square p hp st).1
  have hη := escape_square p hp st
  have hμ := (basic_scales p hp st).1
  have hμb := (basic_scales p hp st).2.2.2.2.2
  have hA' : (parameters p st).μ * metricRadius p ^ 2 = 2 * decrease p := by
    have hh := (eq_div_iff hμ.ne').mp hA
    change metricRadius p ^ 2 * (parameters p st).μ = 2 * decrease p at hh
    nlinarith only [hh]
  have hη' : p.L₃ * (parameters p st).η ^ 2 = alpha p / 16 := by rw [hη]; field_simp
  have hq' : alpha p * (parameters p st).η ^ 2 / 4 = 48 * decrease p := by
    rw [hη]
    unfold decrease
    ring
  refine ⟨hη', by linarith, ?_⟩
  have hh := congrArg (fun x : ℝ => x * (parameters p st).η ^ 2) hμb
  nlinarith only [hA', hq', hh, hq]

lemma short_scales (p : Params) (hp : spec.valid p) :
    384 * p.L₃ * euclideanRadius p ^ 4 ≤ decrease p ∧
      48 * p.L₃ * euclideanRadius p ^ 2 ≤ alpha p / 4 := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hL := hp.1
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hs : euclideanRadius p ^ 2 = decrease p / alpha p := Real.sq_sqrt (by positivity)
  have hs₄ : euclideanRadius p ^ 4 = (decrease p / alpha p) ^ 2 := by nlinarith only [congrArg (fun x : ℝ => x ^ 2) hs]
  have he₁ : 384 * p.L₃ * euclideanRadius p ^ 4 = decrease p / 8 := by
    rw [hs₄]
    unfold decrease
    field_simp
    ring
  have he₂ : 48 * p.L₃ * euclideanRadius p ^ 2 = alpha p / 64 := by
    rw [hs]
    unfold decrease
    field_simp
    ring
  rw [he₁, he₂]
  constructor <;> linarith

lemma guard_scales (p : Params) (hp : spec.valid p) :
    metricRadius p ≤ radius p / 8 ∧ decrease p ≤ radius p ^ 2 / 4 := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hL := hp.1
  have hβ := LazyQuarticParameters.beta_square p hp
  have hc := LazyQuarticParameters.alpha_cap p
  have hr := LazyQuarticParameters.radius_pos p hp
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hA : 24 * p.L₃ * metricRadius p ^ 2 = beta p * alpha p := by
    unfold metricRadius
    rw [Real.sq_sqrt (by positivity)]
    unfold decrease
    field_simp
    ring
  have hR : 65536 * radius p ^ 2 = p.Δ := by
    unfold radius
    rw [div_pow, Real.sq_sqrt hp.2.1.le]
    ring
  have hR' := congrArg (fun x : ℝ => p.L₃ * x) hR
  have hq' : 3072 * p.L₃ * decrease p = alpha p ^ 2 := by unfold decrease; field_simp
  norm_num at hc
  have hcap := mul_le_mul_of_nonneg_left hc hb.le
  have hcoarse : 16 * alpha p ≤ beta p := by linarith
  have hcoarse₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * alpha p) hcoarse 2
  constructor
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ radius p / 8)).mp
    apply (mul_le_mul_iff_right₀ hL).mp
    change p.L₃ * metricRadius p ^ 2 ≤ p.L₃ * (radius p / 8) ^ 2
    nlinarith only [hA, hR', hβ, hcap, mul_pos hb ha]
  · apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hq', hR', hβ, hcoarse₂]

end LongTails.Proofs.LazyQuarticStageParameters
