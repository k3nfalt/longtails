import LongTails.Proofs.LazyQuarticCurvature
import LongTails.Proofs.LazyQuarticStageParameters

namespace LongTails.Proofs.LazyQuarticDecay

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.LazyQuarticCurvature

lemma geometric_decay {a Γ : ℝ} {N : ℕ} (ha : a ≤ 1) (hΓ : 0 < Γ)
    (hN : 128 * Real.log Γ ≤ a * N) : (1 - a) ^ N ≤ 1 / Γ ^ (128 : ℕ) := by
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr ha) (Real.one_sub_le_exp_neg a) N
  rw [← Real.exp_nat_mul] at hh
  have he : Real.exp ((N : ℝ) * -a) ≤ Real.exp (-(128 * Real.log Γ)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hN])
  have hid : Real.exp (128 * Real.log Γ) = Γ ^ (128 : ℕ) := by
    rw [show (128 : ℝ) = (128 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hΓ]
  rw [Real.exp_neg, hid] at he
  exact hh.trans (by simpa only [one_div] using he)

lemma acceleration_condition (p : Params) (hp : spec.valid p) (st : State p) :
    (parameters p st).a * Real.sqrt (condition p) = 1 / 16 := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hk : 0 < condition p := div_pos hb ha
  have hs := Real.sq_sqrt hk.le
  have ht := Real.sq_sqrt (show 0 ≤ alpha p / (256 * beta p) by positivity)
  have he : ((parameters p st).a * Real.sqrt (condition p)) ^ 2 = (1 / 16 : ℝ) ^ 2 := by
    rw [mul_pow]
    change (Real.sqrt (alpha p / (256 * beta p))) ^ 2 * (Real.sqrt (condition p)) ^ 2 = _
    rw [ht, hs]
    unfold condition
    field_simp
    norm_num
  have hn : 0 ≤ (parameters p st).a * Real.sqrt (condition p) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

lemma scheduled_decay (p : Params) (hp : spec.valid p) (st : State p) :
    (1 - (parameters p st).a) ^ innerSteps p ≤ 1 / logarithmArgument p ^ (128 : ℕ) := by
  have hs := LazyQuarticStageParameters.basic_scales p hp st
  have hΓ : 0 < logarithmArgument p := lt_of_lt_of_le (by norm_num) (LazyQuarticParameters.logarithmArgument_ge_two p hp)
  apply geometric_decay hs.2.2.1 hΓ
  have hn := Nat.le_ceil (2 ^ 11 * Real.sqrt (condition p) * Real.log (logarithmArgument p))
  have hh := mul_le_mul_of_nonneg_left hn hs.2.1
  have he := acceleration_condition p hp st
  change (parameters p st).a * (2 ^ 11 * Real.sqrt (condition p) * Real.log (logarithmArgument p)) ≤
    (parameters p st).a * (innerSteps p : ℝ) at hh
  have hid : (parameters p st).a * (2 ^ 11 * Real.sqrt (condition p) * Real.log (logarithmArgument p)) =
      128 * Real.log (logarithmArgument p) := by
    calc
      _ = 2 ^ 11 * ((parameters p st).a * Real.sqrt (condition p)) * Real.log (logarithmArgument p) := by ring
      _ = _ := by rw [he]; ring
  rwa [hid] at hh

lemma curvature_ratio (p : Params) (hp : spec.valid p) :
    64 * p.Δ * curvatureCap p ≤ p.ε ^ 2 * logarithmArgument p ^ (128 : ℕ) := by
  have hb := LazyQuarticParameters.beta_pos p hp
  have hβ := LazyQuarticParameters.beta_square p hp
  have hε := hp.2.2.2
  have hΔ := hp.2.1
  have hL := hp.1
  have hH := hp.2.2.1
  let U := p.H₀ * p.Δ / p.ε ^ 2
  let V := p.L₃ * p.Δ ^ 3 / p.ε ^ 4
  let W := beta p * p.Δ / p.ε ^ 2
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hW₂ : W ^ 2 = V := by
    dsimp [W, V]
    rw [div_pow, mul_pow, hβ]
    ring
  have hsmall : W ≤ 1 + V := by nlinarith [sq_nonneg (W - 1)]
  have hΓ := LazyQuarticParameters.logarithmArgument_ge_two p hp
  have hpow : (2 : ℝ) ^ 127 * logarithmArgument p ≤ logarithmArgument p ^ (128 : ℕ) := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hΓ 127) (by linarith : 0 ≤ logarithmArgument p)
    simpa only [pow_succ] using hh
  have hratio : 64 * p.Δ * curvatureCap p / p.ε ^ 2 = 2 ^ 110 * (U + W + V) := by
    dsimp [curvatureCap, U, W, V]
    field_simp
    ring
  have hsum : U + W + V ≤ 2 * logarithmArgument p := by
    change U + W + V ≤ 2 * (2 + U + V)
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 ^ 110 by positivity)
  have hbound : 64 * p.Δ * curvatureCap p / p.ε ^ 2 ≤ logarithmArgument p ^ (128 : ℕ) := by
    rw [hratio]
    norm_num at h₁ hpow ⊢
    nlinarith only [h₁, hpow, hΓ]
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hbound
  nlinarith only [hh]

lemma certificate_decay (p : Params) (hp : spec.valid p) (st : State p) :
    curvatureCap p * (2 * (parameters p st).L * (1 - (parameters p st).a) ^ innerSteps p *
      (p.Δ + 4 * (parameters p st).q)) ≤ (p.ε / 2) ^ 2 := by
  have hd := scheduled_decay p hp st
  have hr := curvature_ratio p hp
  have hs := LazyQuarticStageParameters.basic_scales p hp st
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hk := LazyQuarticParameters.condition_lower p hp
  have he := LazyQuarticParameters.decrease_condition p hp
  have hk₂ : 1 ≤ condition p ^ 2 := by norm_num at hk; nlinarith
  have hq' : 4 * decrease p ≤ p.Δ := by
    have hh := mul_le_mul_of_nonneg_left hk₂ hq.le
    nlinarith only [hh, he, hq]
  have hM : 0 ≤ curvatureCap p := by
    have hH := hp.2.2.1
    have hb := (LazyQuarticParameters.beta_pos p hp).le
    have hL := hp.1.le
    unfold curvatureCap
    positivity
  have hΔ := hp.2.1.le
  have hΓ : 0 < logarithmArgument p := lt_of_lt_of_le (by norm_num) (LazyQuarticParameters.logarithmArgument_ge_two p hp)
  have hdn : 0 ≤ (1 - (parameters p st).a) ^ innerSteps p := pow_nonneg (sub_nonneg.mpr hs.2.2.1) _
  have h₁ := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 8 * curvatureCap p * (1 - (parameters p st).a) ^ innerSteps p by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hd (show 0 ≤ 16 * p.Δ * curvatureCap p by positivity)
  have h₃ : 16 * p.Δ * curvatureCap p / logarithmArgument p ^ (128 : ℕ) ≤ (p.ε / 2) ^ 2 := by
    apply (div_le_iff₀ (pow_pos hΓ 128)).mpr
    nlinarith only [hr]
  change curvatureCap p * (2 * 4 * (1 - (parameters p st).a) ^ innerSteps p * (p.Δ + 4 * decrease p)) ≤ _
  have h₂' : 16 * p.Δ * curvatureCap p * (1 - (parameters p st).a) ^ innerSteps p ≤
      16 * p.Δ * curvatureCap p / logarithmArgument p ^ (128 : ℕ) := by
    convert h₂ using 1; ring
  nlinarith only [h₁, h₂', h₃]

end LongTails.Proofs.LazyQuarticDecay
