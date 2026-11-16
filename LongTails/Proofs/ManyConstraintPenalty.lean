import LongTails.Proofs.ManyConstraintGeometry

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintPenalty

open LongTails.Proofs.ManyConstraintGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def half (P : E → E) (x : E) : ℝ := ‖x - P x‖ ^ 2 / 2

lemma half_bregman_eq (P : E → E) (x y : E) :
    half P y - half P x - ⟪x - P x, y - x⟫ =
      ‖(y - P y) - (x - P x)‖ ^ 2 / 2 - ⟪x - P x, P y - P x⟫ := by
  unfold half
  have hy : y - x = ((y - P y) - (x - P x)) + (P y - P x) := by abel
  rw [hy, inner_add_right]
  have hn : ‖y - P y‖ ^ 2 = ‖((y - P y) - (x - P x)) + (x - P x)‖ ^ 2 := by
    rw [sub_add_cancel]
  rw [hn, norm_add_sq_real, real_inner_comm (x - P x)]
  ring

variable {K : Set E} {P : E → E}

lemma half_bregman_lower (hP : ∀ z, IsProj K z (P z)) (x y : E) :
    ‖(y - P y) - (x - P x)‖ ^ 2 / 2 ≤ half P y - half P x - ⟪x - P x, y - x⟫ := by
  rw [half_bregman_eq]
  have := (hP x).2 (P y) (hP y).1
  linarith

lemma half_bregman_upper (hP : ∀ z, IsProj K z (P z)) (x y : E) :
    half P y - half P x - ⟪x - P x, y - x⟫ ≤ ‖y - x‖ ^ 2 / 2 := by
  have hmin : ‖y - P y‖ ≤ ‖y - P x‖ := by
    rw [proj_eq_infDist (hP y), ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (hP x).1
  have hsq : ‖y - P y‖ ^ 2 ≤ ‖y - P x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmin 2
  have hexp : ‖y - P x‖ ^ 2 = ‖x - P x‖ ^ 2 + 2 * ⟪x - P x, y - x⟫ + ‖y - x‖ ^ 2 := by
    have : y - P x = (x - P x) + (y - x) := by abel
    rw [this, norm_add_sq_real]
  unfold half
  linarith

noncomputable def pen (β : ℝ) (P : E → E) (x : E) : ℝ := β * half P x

noncomputable def penGrad (β : ℝ) (P : E → E) (x : E) : E := β • (x - P x)

lemma pen_support (hP : ∀ z, IsProj K z (P z)) {β : ℝ} (hβ : 0 ≤ β) (x y : E) :
    pen β P x + ⟪penGrad β P x, y - x⟫ ≤ pen β P y := by
  have h := half_bregman_lower hP x y
  have h0 : 0 ≤ ‖(y - P y) - (x - P x)‖ ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left (h0.trans h) hβ
  simp only [pen, penGrad, real_inner_smul_left]
  nlinarith

lemma pen_upper (hP : ∀ z, IsProj K z (P z)) {β : ℝ} (hβ : 0 ≤ β) (x y : E) :
    pen β P y ≤ pen β P x + ⟪penGrad β P x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 := by
  have := mul_le_mul_of_nonneg_left (half_bregman_upper hP x y) hβ
  simp only [pen, penGrad, real_inner_smul_left]
  nlinarith

lemma pen_cocoercive (hP : ∀ z, IsProj K z (P z)) {β : ℝ} (hβ : 0 < β) (x y : E) :
    ‖penGrad β P y - penGrad β P x‖ ^ 2 ≤
      2 * β * (pen β P y - pen β P x - ⟪penGrad β P x, y - x⟫) := by
  have h := half_bregman_lower hP x y
  have hg : penGrad β P y - penGrad β P x = β • ((y - P y) - (x - P x)) := by
    simp only [penGrad, smul_sub]
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ, mul_pow]
  simp only [pen, penGrad, real_inner_smul_left]
  have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * β ^ 2)
  nlinarith

omit [InnerProductSpace ℝ E] in
lemma pen_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : E) : 0 ≤ pen β P x := by
  unfold pen half; positivity

lemma pen_zero_of_mem (hP : ∀ z, IsProj K z (P z)) {β : ℝ} {x : E} (hx : x ∈ K) :
    pen β P x = 0 := by
  have h := proj_eq_infDist (hP x)
  rw [Metric.infDist_zero_of_mem hx] at h
  simp [pen, half, h]

lemma pen_eq_infDist (hP : ∀ z, IsProj K z (P z)) (β : ℝ) (x : E) :
    pen β P x = β / 2 * Metric.infDist x K ^ 2 := by
  simp only [pen, half, proj_eq_infDist (hP x)]; ring

end LongTails.Proofs.ManyConstraintPenalty
