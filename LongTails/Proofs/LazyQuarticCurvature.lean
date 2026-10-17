import LongTails.Proofs.LazyQuarticSnapshot
import LongTails.Proofs.ThirdOrderOperatorBounds
import LongTails.Proofs.QuarticPrefixPath

namespace LongTails.Proofs.LazyQuarticCurvature

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open scoped RealInnerProductSpace

noncomputable def pathCap (p : Params) : ℝ :=
  2 ^ 26 * p.Δ ^ 2 / p.ε ^ 2 + 2 ^ 98 * p.Δ / beta p

noncomputable def curvatureCap (p : Params) : ℝ :=
  2 ^ 104 * (p.H₀ + beta p + p.L₃ * p.Δ ^ 2 / p.ε ^ 2)

lemma stages_upper (p : Params) (hp : spec.valid p) : (stages p : ℝ) ≤ 2 ^ 12 * condition p ^ 2 := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 3072 * condition p ^ 2 by positivity)
  have hk := LazyQuarticParameters.condition_lower p hp
  have hs : 1 ≤ condition p ^ 2 := by norm_num at hk; nlinarith
  simp only [stages, Nat.cast_add, Nat.cast_one]
  norm_num
  nlinarith

lemma path_cap (p : Params) (hp : spec.valid p) {d : ℝ}
    (hd : alpha p ^ 3 * d ^ 2 ≤ 2 ^ 26 * p.Δ * beta p ^ 2) : d ^ 2 ≤ pathCap p := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hL := hp.1
  have hε := hp.2.2.2
  have hΔ := hp.2.1
  have hβ := LazyQuarticParameters.beta_square p hp
  have h₁ : 0 ≤ 2 ^ 26 * p.Δ ^ 2 / p.ε ^ 2 := by positivity
  have h₂ : 0 ≤ 2 ^ 98 * p.Δ / beta p := by positivity
  by_cases hc : beta p / 2 ^ 24 ≤ (p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ)
  · have he : alpha p = beta p / 2 ^ 24 := min_eq_left hc
    have hid : alpha p ^ 3 * (2 ^ 98 * p.Δ / beta p) = 2 ^ 26 * p.Δ * beta p ^ 2 := by
      rw [he]
      field_simp
    have hh : d ^ 2 ≤ 2 ^ 98 * p.Δ / beta p :=
      (mul_le_mul_iff_right₀ (pow_pos ha 3)).mp (hd.trans_eq hid.symm)
    unfold pathCap
    linarith
  · have he : alpha p = (p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ) := min_eq_right (le_of_not_ge hc)
    have hcub : alpha p ^ 3 = p.L₃ * p.ε ^ 2 := by
      rw [he, ← Real.rpow_mul_natCast (mul_pos hL (sq_pos_of_pos hε)).le]
      norm_num
    have hid : alpha p ^ 3 * (2 ^ 26 * p.Δ ^ 2 / p.ε ^ 2) = 2 ^ 26 * p.Δ * beta p ^ 2 := by
      rw [hcub, hβ]
      field_simp
    have hh : d ^ 2 ≤ 2 ^ 26 * p.Δ ^ 2 / p.ε ^ 2 :=
      (mul_le_mul_iff_right₀ (pow_pos ha 3)).mp (hd.trans_eq hid.symm)
    unfold pathCap
    linarith

lemma curvature_scalar_cap (p : Params) (hp : spec.valid p) {d : ℝ} (hd : d ^ 2 ≤ pathCap p) :
    28 * p.H₀ + 116 * beta p + 28 * p.L₃ * d ^ 2 ≤ curvatureCap p := by
  have hb := LazyQuarticParameters.beta_pos p hp
  have hβ := LazyQuarticParameters.beta_square p hp
  have hL := hp.1
  have hH := hp.2.2.1
  have hΔ := hp.2.1
  have hε := hp.2.2.2
  have he : p.L₃ * p.Δ / beta p = beta p := (div_eq_iff hb.ne').mpr (by nlinarith only [hβ])
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 28 * p.L₃ by positivity)
  have hid : 28 * p.L₃ * pathCap p =
      28 * 2 ^ 26 * (p.L₃ * p.Δ ^ 2 / p.ε ^ 2) + 28 * 2 ^ 98 * beta p := by
    unfold pathCap
    calc
      _ = 28 * 2 ^ 26 * (p.L₃ * p.Δ ^ 2 / p.ε ^ 2) + 28 * 2 ^ 98 * (p.L₃ * p.Δ / beta p) := by ring
      _ = _ := by rw [he]
  rw [hid] at hh
  have hn : 0 ≤ p.L₃ * p.Δ ^ 2 / p.ε ^ 2 := by positivity
  unfold curvatureCap
  norm_num at hh ⊢
  nlinarith only [hh, hn, hH, hb]

lemma metric_cap (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ p.L₃ * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hH : ‖fderiv ℝ (_root_.gradient f) p.x0‖ ≤ p.H₀)
    (x : p.E) (hx : f x ≤ f p.x0) (hpath : ‖x - p.x0‖ ^ 2 ≤ pathCap p) (v : p.E) :
    ‖coordinates p (fderiv ℝ (_root_.gradient f) x) v‖ ^ 2 ≤ curvatureCap p * ‖v‖ ^ 2 := by
  have hs := LazyQuarticSnapshot.sigma_relations p hp
  have hh := ThirdOrderOperatorBounds.hessian_growth hf hp.1 hs.1 hp.2.2.1 hs.2.1 hT p.x0 x hgap hH
  have he : 108 * p.L₃ * (beta p / p.L₃) = 108 * beta p := by rw [mul_assoc, hs.2.2]
  rw [he] at hh
  have hc := curvature_scalar_cap p hp hpath
  have hnewgap (y : p.E) : f x - f y ≤ p.Δ := by linarith [hgap y]
  rw [LazyQuarticSnapshot.coordinates_metric p hp f hf hT x hnewgap v]
  have hi : ⟪fderiv ℝ (_root_.gradient f) x v, v⟫ ≤
      ‖fderiv ℝ (_root_.gradient f) x‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ (_root_.gradient f) x v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ (_root_.gradient f) x‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  have hn := mul_le_mul_of_nonneg_right (show ‖fderiv ℝ (_root_.gradient f) x‖ + 8 * beta p ≤ curvatureCap p by linarith) (sq_nonneg ‖v‖)
  nlinarith only [hi, hn]

end LongTails.Proofs.LazyQuarticCurvature
