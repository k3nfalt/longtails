import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Algorithms.GuardedMetricAcceleration

namespace LongTails.Proofs.QuarticEscapeGeometry

lemma endpoint_curvature {a b c D L α δ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hdeficit : D ≤ -α * δ ^ 2 / 2)
    (hvalue : a * δ ^ 2 / 2 + b * δ ^ 3 / 6 ≤ D + L * δ ^ 4)
    (hhessian : c ≤ a + b * δ + L * δ ^ 2) :
    min a c ≤ -α + 3 * L * δ ^ 2 := by
  have hh := mul_le_mul_of_nonneg_right hhessian (sq_nonneg δ)
  have hp : (2 * a + c) * δ ^ 2 ≤ (-3 * α + 7 * L * δ ^ 2) * δ ^ 2 := by
    nlinarith
  have hsum := (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp hp
  by_cases ha : a ≤ -α + 3 * L * δ ^ 2
  · exact (min_le_left _ _).trans ha
  · have hc : c ≤ -α + 3 * L * δ ^ 2 := by
      have hLδ : 0 ≤ L * δ ^ 2 := mul_nonneg hL (sq_nonneg δ)
      linarith
    exact (min_le_right _ _).trans hc

lemma symmetric_escape {fp fm f₀ g H T L α η : ℝ}
    (hα : 0 ≤ α) (hH : H ≤ -(3 / 4) * α) (hη : L * η ^ 2 ≤ α / 16)
    (hp : fp ≤ f₀ + g * η + H * η ^ 2 / 2 + T * η ^ 3 / 6 + L * η ^ 4)
    (hm : fm ≤ f₀ - g * η + H * η ^ 2 / 2 - T * η ^ 3 / 6 + L * η ^ 4) :
    min fp fm ≤ f₀ - α * η ^ 2 / 4 := by
  have hc := mul_le_mul_of_nonneg_right hH (sq_nonneg η)
  have hd := mul_le_mul_of_nonneg_right hη (sq_nonneg η)
  have hmin₁ := min_le_left fp fm
  have hmin₂ := min_le_right fp fm
  nlinarith [mul_nonneg hα (sq_nonneg η)]

lemma interpolation_identity (p₀ p₁ p₂ p₃ t : ℝ) :
    p₀ + p₁ * t + p₂ * t ^ 2 + p₃ * t ^ 3 =
      ((t + 3) * (t + 1) * (2 * t + 1) / 3) * p₀ +
      (t * (t + 3) * (2 * t + 1) / 2) * (p₀ - p₁ + p₂ - p₃) -
      (8 * t * (t + 3) * (t + 1) / 5) * (p₀ - p₁ / 2 + p₂ / 4 - p₃ / 8) -
      (t * (t + 1) * (2 * t + 1) / 30) * (p₀ - 3 * p₁ + 9 * p₂ - 27 * p₃) := by
  ring

lemma interpolation_bound {h : ℝ → ℝ} {p₀ p₁ p₂ p₃ M q t : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (happrox : ∀ s, |h s - (p₀ + p₁ * s + p₂ * s ^ 2 + p₃ * s ^ 3)| ≤ M * s ^ 4)
    (hzero : h 0 ≤ 0) (hone : h (-1) ≤ 0)
    (hhalf : -q ≤ h (-(1 / 2))) (hthree : -q ≤ h (-3)) :
    h t ≤ 13 * q + 24 * M := by
  let w₀ := (t + 3) * (t + 1) * (2 * t + 1) / 3
  let w₁ := t * (t + 3) * (2 * t + 1) / 2
  let w₂ := 8 * t * (t + 3) * (t + 1) / 5
  let w₃ := t * (t + 1) * (2 * t + 1) / 30
  have hw₀ : 0 ≤ w₀ := by dsimp [w₀]; positivity
  have hw₁ : 0 ≤ w₁ := by dsimp [w₁]; positivity
  have hw₂ : 0 ≤ w₂ := by dsimp [w₂]; positivity
  have hw₃ : 0 ≤ w₃ := by dsimp [w₃]; positivity
  have hw₁' : w₁ ≤ 6 := by
    calc
      w₁ ≤ (1 : ℝ) * (1 + 3) * (2 * 1 + 1) / 2 := by dsimp [w₁]; gcongr
      _ = _ := by norm_num
  have hw₂' : w₂ ≤ 64 / 5 := by
    calc
      w₂ ≤ (8 : ℝ) * 1 * (1 + 3) * (1 + 1) / 5 := by dsimp [w₂]; gcongr
      _ = _ := by norm_num
  have hw₃' : w₃ ≤ 1 / 5 := by
    calc
      w₃ ≤ (1 : ℝ) * (1 + 1) * (2 * 1 + 1) / 30 := by dsimp [w₃]; gcongr
      _ = _ := by norm_num
  have hz := (abs_le.mp (happrox 0)).1
  have h₁ := (abs_le.mp (happrox (-1))).1
  have h₂ := (abs_le.mp (happrox (-(1 / 2)))).2
  have h₃ := (abs_le.mp (happrox (-3))).2
  have h₀bound : p₀ ≤ 0 := by nlinarith
  have h₁bound : p₀ - p₁ + p₂ - p₃ ≤ M := by nlinarith
  have h₂bound : -q - M / 16 ≤ p₀ - p₁ / 2 + p₂ / 4 - p₃ / 8 := by nlinarith
  have h₃bound : -q - 81 * M ≤ p₀ - 3 * p₁ + 9 * p₂ - 27 * p₃ := by nlinarith
  have e₀ := mul_le_mul_of_nonneg_left h₀bound hw₀
  have e₁ := mul_le_mul_of_nonneg_left h₁bound hw₁
  have e₂ := mul_le_mul_of_nonneg_left h₂bound hw₂
  have e₃ := mul_le_mul_of_nonneg_left h₃bound hw₃
  have e₁' := mul_le_mul_of_nonneg_right hw₁' hM
  have e₂' := mul_le_mul_of_nonneg_right hw₂' (by positivity : 0 ≤ q + M / 16)
  have e₃' := mul_le_mul_of_nonneg_right hw₃' (by positivity : 0 ≤ q + 81 * M)
  have hid := interpolation_identity p₀ p₁ p₂ p₃ t
  change p₀ + p₁ * t + p₂ * t ^ 2 + p₃ * t ^ 3 =
    w₀ * p₀ + w₁ * (p₀ - p₁ + p₂ - p₃) -
      w₂ * (p₀ - p₁ / 2 + p₂ / 4 - p₃ / 8) -
      w₃ * (p₀ - 3 * p₁ + 9 * p₂ - 27 * p₃) at hid
  have ht := (abs_le.mp (happrox t)).2
  have ht' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀ ht₁ 4) hM
  nlinarith

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma directional_hessian_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (v e : E) (he : ‖e‖ = 1) (t : ℝ) :
    |⟪fderiv ℝ (gradient f) (v + t • e) e, e⟫ -
      ⟪fderiv ℝ (gradient f) v e, e⟫ - t *
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) v e e, e⟫| ≤ L * t ^ 2 := by
  let A := fderiv ℝ (gradient f) (v + t • e) - fderiv ℝ (gradient f) v -
    fderiv ℝ (fderiv ℝ (gradient f)) v (t • e)
  have ha : ‖A‖ ≤ L * t ^ 2 := by
    simpa [A, norm_smul, Real.norm_eq_abs, he, sq_abs] using
      ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT v (v + t • e)
  have hb : |⟪A e, e⟫| ≤ ‖A‖ := by
    calc
      _ ≤ ‖A e‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖e‖) * ‖e‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by rw [he]; ring
  simpa only [A, sub_apply, map_smul, smul_apply, inner_sub_left, real_inner_smul_left] using hb.trans ha

lemma line_endpoint_curvature {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L α δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (v e : E) (he : ‖e‖ = 1)
    (hdeficit : f (v + δ • e) - f v - ⟪gradient f v, e⟫ * δ ≤ -α * δ ^ 2 / 2) :
    min ⟪fderiv ℝ (gradient f) v e, e⟫
      ⟪fderiv ℝ (gradient f) (v + δ • e) e, e⟫ ≤ -α + 3 * L * δ ^ 2 := by
  have hv := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT v e δ
  simp only [he, one_pow, mul_one, abs_of_pos hδ] at hv
  have hh := directional_hessian_remainder hf hL hT v e he δ
  apply endpoint_curvature (b := ⟪fderiv ℝ (fderiv ℝ (gradient f)) v e e, e⟫) hδ hL hdeficit
  · have hh' := (abs_le.mp hv).1
    linarith
  · have hh' := (abs_le.mp hh).2
    linarith

lemma line_symmetric_escape {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L α η : ℝ} (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (v e : E) (he : ‖e‖ = 1)
    (hH : ⟪fderiv ℝ (gradient f) v e, e⟫ ≤ -(3 / 4) * α)
    (hη : L * η ^ 2 ≤ α / 16) :
    min (f (v + η • e)) (f (v - η • e)) ≤ f v - α * η ^ 2 / 4 := by
  have hp := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT v e η
  have hm := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT v e (-η)
  have heven (t : ℝ) : |t| ^ 4 = t ^ 4 := by nlinarith [sq_abs t, sq_nonneg (t ^ 2)]
  simp only [he, one_pow, mul_one, heven, neg_smul, ← sub_eq_add_neg] at hp hm
  rw [show (-η) ^ 2 = η ^ 2 by ring, show (-η) ^ 3 = -(η ^ 3) by ring,
    show (-η) ^ 4 = η ^ 4 by ring] at hm
  apply symmetric_escape (g := ⟪gradient f v, e⟫)
    (H := ⟪fderiv ℝ (gradient f) v e, e⟫)
    (T := ⟪fderiv ℝ (fderiv ℝ (gradient f)) v e e, e⟫) hα hH hη
  · have hh := (abs_le.mp hp).2
    linarith
  · have hh := (abs_le.mp hm).2
    linarith

lemma four_point_escape {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L α δ η : ℝ} (hL : 0 ≤ L) (hα : 0 ≤ α) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (v e : E) (he : ‖e‖ = 1)
    (hdeficit : f (v + δ • e) - f v - ⟪gradient f v, e⟫ * δ ≤ -α * δ ^ 2 / 2)
    (hshort : 3 * L * δ ^ 2 ≤ α / 4) (hη : L * η ^ 2 ≤ α / 16) :
    min (min (f (v + η • e)) (f (v - η • e)))
      (min (f (v + δ • e + η • e)) (f (v + δ • e - η • e))) ≤
      max (f v) (f (v + δ • e)) - α * η ^ 2 / 4 := by
  have hc := line_endpoint_curvature hf hL hδ hT v e he hdeficit
  have hcurv : min ⟪fderiv ℝ (gradient f) v e, e⟫
      ⟪fderiv ℝ (gradient f) (v + δ • e) e, e⟫ ≤ -(3 / 4) * α := by linarith
  rcases le_total ⟪fderiv ℝ (gradient f) v e, e⟫
    ⟪fderiv ℝ (gradient f) (v + δ • e) e, e⟫ with h | h
  · rw [min_eq_left h] at hcurv
    have hh := line_symmetric_escape hf hL hα hT v e he hcurv hη
    have hmin := min_le_left (min (f (v + η • e)) (f (v - η • e)))
      (min (f (v + δ • e + η • e)) (f (v + δ • e - η • e)))
    have hmax := le_max_left (f v) (f (v + δ • e))
    linarith
  · rw [min_eq_right h] at hcurv
    have hh := line_symmetric_escape hf hL hα hT (v + δ • e) e he hcurv hη
    have hmin := min_le_right (min (f (v + η • e)) (f (v - η • e)))
      (min (f (v + δ • e + η • e)) (f (v + δ • e - η • e)))
    have hmax := le_max_right (f v) (f (v + δ • e))
    linarith

end LongTails.Proofs.QuarticEscapeGeometry
