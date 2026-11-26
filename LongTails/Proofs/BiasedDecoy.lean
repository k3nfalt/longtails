import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace LongTails.Proofs.BiasedDecoy

noncomputable def pr (w t : ℝ) : ℝ := Real.sqrt (t ^ 2 + w ^ 2)

noncomputable def dpr (w t : ℝ) : ℝ := t / Real.sqrt (t ^ 2 + w ^ 2)

section

variable {w : ℝ}

lemma base_pos (hw : 0 < w) (t : ℝ) : 0 < t ^ 2 + w ^ 2 := by positivity

lemma sqrt_base_pos (hw : 0 < w) (t : ℝ) : 0 < Real.sqrt (t ^ 2 + w ^ 2) :=
  Real.sqrt_pos.mpr (base_pos hw t)

lemma w_le_sqrt (t : ℝ) : w ≤ Real.sqrt (t ^ 2 + w ^ 2) :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])

lemma abs_le_sqrt_base (t : ℝ) : |t| ≤ Real.sqrt (t ^ 2 + w ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w])

lemma hasDerivAt_sqrt_base (hw : 0 < w) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + w ^ 2)) (dpr w t) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + w ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).add_const (w ^ 2))
  have h2 := h1.sqrt (base_pos hw t).ne'
  have hs := sqrt_base_pos hw t
  unfold dpr
  convert h2 using 1
  field_simp

lemma hasDerivAt_pr (hw : 0 < w) (t : ℝ) : HasDerivAt (pr w) (dpr w t) t :=
  hasDerivAt_sqrt_base hw t

lemma abs_dpr_le (hw : 0 < w) (t : ℝ) : |dpr w t| ≤ 1 := by
  have hs := sqrt_base_pos hw t
  unfold dpr
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact abs_le_sqrt_base t

lemma pr_ge (t : ℝ) : w ≤ pr w t := w_le_sqrt t

lemma pr_zero (hw : 0 < w) : pr w 0 = w := by
  unfold pr
  rw [show (0 : ℝ) ^ 2 + w ^ 2 = w ^ 2 by ring, Real.sqrt_sq hw.le]

lemma pr_le (hw : 0 < w) (t : ℝ) : pr w t ≤ |t| + w := by
  unfold pr
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs t, abs_nonneg t]

lemma hasDerivAt_dpr (hw : 0 < w) (t : ℝ) :
    HasDerivAt (dpr w) (w ^ 2 / ((t ^ 2 + w ^ 2) * Real.sqrt (t ^ 2 + w ^ 2))) t := by
  have h2 := hasDerivAt_sqrt_base hw t
  have hs := sqrt_base_pos hw t
  have h3 := (hasDerivAt_id' t).div h2 hs.ne'
  unfold dpr
  convert h3 using 1
  unfold dpr
  have hsq : Real.sqrt (t ^ 2 + w ^ 2) ^ 2 = t ^ 2 + w ^ 2 := Real.sq_sqrt (base_pos hw t).le
  field_simp
  rw [hsq]
  ring

lemma deriv_dpr_le (hw : 0 < w) (t : ℝ) :
    w ^ 2 / ((t ^ 2 + w ^ 2) * Real.sqrt (t ^ 2 + w ^ 2)) ≤ 1 / w := by
  have hs := w_le_sqrt (w := w) t
  have hb : w ^ 2 ≤ t ^ 2 + w ^ 2 := by nlinarith [sq_nonneg t]
  rw [div_le_div_iff₀ (by positivity) hw]
  have : w ^ 2 * w ≤ (t ^ 2 + w ^ 2) * Real.sqrt (t ^ 2 + w ^ 2) :=
    mul_le_mul hb hs hw.le (by positivity)
  linarith

lemma dpr_lip (hw : 0 < w) (a b : ℝ) : |dpr w a - dpr w b| ≤ |a - b| / w := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (dpr w) x :=
    fun x _ => (hasDerivAt_dpr hw x).differentiableAt
  have hbd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (dpr w) x‖ ≤ 1 / w := by
    intro x _
    rw [(hasDerivAt_dpr hw x).deriv, Real.norm_of_nonneg (by positivity)]
    exact deriv_dpr_le hw x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
  simp only [Real.norm_eq_abs] at h
  rw [div_eq_mul_one_div, mul_comm]
  exact h

lemma dpr_continuous (hw : 0 < w) : Continuous (dpr w) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_dpr hw t).continuousAt

lemma pr_continuous (hw : 0 < w) : Continuous (pr w) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pr hw t).continuousAt

lemma abs_dpr_far (hw : 0 < w) {t : ℝ} (ht : t ≤ -(100 * w)) : 99 / 100 ≤ |dpr w t| := by
  have hs := sqrt_base_pos hw t
  have htn : t < 0 := by linarith
  unfold dpr
  rw [abs_div, abs_of_pos hs, abs_of_neg htn, le_div_iff₀ hs]
  have hsq : Real.sqrt (t ^ 2 + w ^ 2) ^ 2 = t ^ 2 + w ^ 2 := Real.sq_sqrt (base_pos hw t).le
  have ht2 : 10000 * w ^ 2 ≤ t ^ 2 := by nlinarith
  have key : (99 / 100 * Real.sqrt (t ^ 2 + w ^ 2)) ^ 2 ≤ (-t) ^ 2 := by
    rw [mul_pow, hsq]; nlinarith
  have := (pow_le_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).mp key
  linarith

lemma sign_sum_ge (hw : 0 < w) (z : ℝ) :
    99 / 100 ≤ |dpr w (z - 100 * w)| + |dpr w (-z - 100 * w)| := by
  rcases le_total 0 z with hz | hz
  · have := abs_dpr_far hw (t := -z - 100 * w) (by linarith)
    linarith [abs_nonneg (dpr w (z - 100 * w))]
  · have := abs_dpr_far hw (t := z - 100 * w) (by linarith)
    linarith [abs_nonneg (dpr w (-z - 100 * w))]

end

end LongTails.Proofs.BiasedDecoy
