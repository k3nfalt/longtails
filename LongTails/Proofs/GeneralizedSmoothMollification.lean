import LongTails.Proofs.CompactConjugate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothMollification

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω]

lemma integral_norm_bound_of_pairwise (P : ProbabilityMeasure Ω) (g : Ω → E)
    (hg : Integrable g (P : Measure Ω)) (a b : ℝ) (hb : b < 1)
    (h : ∀ u v, ‖g u - g v‖ ≤ b * (a + ‖g v‖)) :
    (∫ u, ‖g u‖ ∂(P : Measure Ω)) ≤
      (‖∫ u, g u ∂(P : Measure Ω)‖ + b * a) / (1 - b) := by
  let m := ∫ u, g u ∂(P : Measure Ω)
  let s := ∫ u, ‖g u‖ ∂(P : Measure Ω)
  have hp (u : Ω) : ‖g u - m‖ ≤ b * (a + s) := by
    have hi : Integrable (fun v => g u - g v) (P : Measure Ω) :=
      (integrable_const (g u)).sub hg
    have he : g u - m = ∫ v, g u - g v ∂(P : Measure Ω) := by
      rw [integral_sub (integrable_const _) hg, integral_const]
      simp only [probReal_univ, one_smul, m]
    rw [he]
    apply (norm_integral_le_integral_norm _).trans
    have hm := integral_mono hi.norm (((integrable_const a).add hg.norm).const_mul b)
      (fun v => h u v)
    simpa only [Pi.add_apply, integral_const_mul, integral_add (integrable_const a) hg.norm,
      integral_const, probReal_univ, smul_eq_mul, one_mul, s] using hm
  have hu (u : Ω) : ‖g u‖ ≤ ‖m‖ + b * (a + s) := by
    have hn := norm_sub_le (g u - m) (-m)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
    linarith [hp u]
  have hav := integral_mono hg.norm (integrable_const (‖m‖ + b * (a + s))) hu
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hav
  change s ≤ (‖m‖ + b * a) / (1 - b)
  apply (le_div_iff₀ (by linarith : 0 < 1 - b)).mpr
  change s ≤ ‖m‖ + b * (a + s) at hav
  nlinarith

lemma integral_curvature_bound_of_pairwise
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : ProbabilityMeasure Ω) (g : Ω → E) (H : Ω → F)
    (hg : Integrable g (P : Measure Ω)) (hH : Integrable H (P : Measure Ω))
    (L₀ L₁ b : ℝ) (hL₁ : 0 < L₁) (hb : b < 1)
    (hpair : ∀ u v, ‖g u - g v‖ ≤ b * (L₀ / L₁ + ‖g v‖))
    (hcurv : ∀ u, ‖H u‖ ≤ L₀ + L₁ * ‖g u‖) :
    ‖∫ u, H u ∂(P : Measure Ω)‖ ≤
      (L₀ + L₁ * ‖∫ u, g u ∂(P : Measure Ω)‖) / (1 - b) := by
  have hp := integral_norm_bound_of_pairwise P g hg (L₀ / L₁) b hb hpair
  have hi := integral_mono hH.norm
    ((integrable_const L₀).add (hg.norm.const_mul L₁)) hcurv
  simp only [Pi.add_apply, integral_add (integrable_const L₀) (hg.norm.const_mul L₁),
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hn := (norm_integral_le_integral_norm H).trans hi
  have hm := mul_le_mul_of_nonneg_left hp hL₁.le
  have he : L₀ + L₁ *
      ((‖∫ u, g u ∂(P : Measure Ω)‖ + b * (L₀ / L₁)) / (1 - b)) =
      (L₀ + L₁ * ‖∫ u, g u ∂(P : Measure Ω)‖) / (1 - b) := by
    field_simp [ne_of_gt hL₁, ne_of_gt (sub_pos.mpr hb)]
    ring
  rw [← he]
  linarith

omit [CompleteSpace E] in
lemma derivative_bound_of_quadratic_increment
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (A : E →L[ℝ] F) (C B : ℝ)
    (hf : HasFDerivAt f A x) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h : ∀ y, ‖f y - f x‖ ≤ (C + B * ‖y - x‖) * ‖y - x‖) : ‖A‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro η hη
  apply hf.le_of_lip' (by positivity)
  have hd : 0 < η / (B + 1) := div_pos hη (by linarith)
  filter_upwards [Metric.ball_mem_nhds x hd] with y hy
  have hy' : ‖y - x‖ < η / (B + 1) := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hm := (lt_div_iff₀ (by linarith : 0 < B + 1)).mp hy'
  have hc : C + B * ‖y - x‖ ≤ C + η := by nlinarith [norm_nonneg (y - x)]
  exact (h y).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma endpoint_to_increment (g : E → E) (L₀ L₁ G : ℝ) (hL₁ : 0 ≤ L₁)
    (hG : ∀ x, ‖g x‖ ≤ G)
    (hpair : ∀ x y, ‖g x - g y‖ ≤
      (L₀ + L₁ * max ‖g x‖ ‖g y‖) * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ≤ (L₀ + L₁ * ‖g y‖ + L₁ * (L₀ + L₁ * G) * ‖x - y‖) * ‖x - y‖ := by
  have hglobal : ‖g x - g y‖ ≤ (L₀ + L₁ * G) * ‖x - y‖ := by
    apply (hpair x y).trans
    gcongr
    exact max_le (hG x) (hG y)
  have hn := norm_sub_norm_le (g x) (g y)
  have hmax : max ‖g x‖ ‖g y‖ ≤ ‖g y‖ + (L₀ + L₁ * G) * ‖x - y‖ := by
    apply max_le
    · linarith
    · linarith [norm_nonneg (g x - g y)]
  have hh := mul_le_mul_of_nonneg_left hmax hL₁
  have hc : L₀ + L₁ * max ‖g x‖ ‖g y‖ ≤
      L₀ + L₁ * ‖g y‖ + L₁ * (L₀ + L₁ * G) * ‖x - y‖ := by nlinarith only [hh]
  exact (hpair x y).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma endpoint_to_local_pair (g : E → E) (L₀ L₁ r : ℝ)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 < L₁) (hr : L₁ * r < 1)
    (hpair : ∀ x y, ‖g x - g y‖ ≤
      (L₀ + L₁ * max ‖g x‖ ‖g y‖) * ‖x - y‖)
    (x y : E) (hxy : ‖x - y‖ ≤ r) :
    ‖g x - g y‖ ≤ L₁ * r / (1 - L₁ * r) * (L₀ / L₁ + ‖g y‖) := by
  have ht := norm_sub_norm_le (g x) (g y)
  have hm : max ‖g x‖ ‖g y‖ ≤ ‖g y‖ + ‖g x - g y‖ := by
    apply max_le <;> linarith [norm_nonneg (g x - g y)]
  have hn : 0 ≤ L₀ + L₁ * max ‖g x‖ ‖g y‖ := by positivity
  have ha := (hpair x y).trans (mul_le_mul_of_nonneg_left hxy hn)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hL₁.le)
    ((norm_nonneg _).trans hxy)
  have hc : ‖g x - g y‖ * (1 - L₁ * r) ≤ r * (L₀ + L₁ * ‖g y‖) := by
    nlinarith only [ha, hb]
  have he : L₁ * r / (1 - L₁ * r) * (L₀ / L₁ + ‖g y‖) =
      r * (L₀ + L₁ * ‖g y‖) / (1 - L₁ * r) := by
    field_simp [hL₁.ne', ne_of_gt (sub_pos.mpr hr)]
  rw [he]
  exact (le_div_iff₀ (sub_pos.mpr hr)).mpr hc

lemma averaged_endpoint_increment (P : ProbabilityMeasure Ω) (z : Ω → E) (g : E → E)
    (L₀ L₁ G b : ℝ) (hL₁ : 0 < L₁) (hb : b < 1)
    (hG : ∀ x, ‖g x‖ ≤ G)
    (hpair : ∀ x y, ‖g x - g y‖ ≤
      (L₀ + L₁ * max ‖g x‖ ‖g y‖) * ‖x - y‖)
    (hi : ∀ x, Integrable (fun u => g (x - z u)) (P : Measure Ω))
    (hloc : ∀ x u v, ‖g (x - z u) - g (x - z v)‖ ≤
      b * (L₀ / L₁ + ‖g (x - z v)‖)) (x y : E) :
    ‖(∫ u, g (y - z u) ∂(P : Measure Ω)) - (∫ u, g (x - z u) ∂(P : Measure Ω))‖ ≤
      ((L₀ + L₁ * ‖∫ u, g (x - z u) ∂(P : Measure Ω)‖) / (1 - b) +
        L₁ * (L₀ + L₁ * G) * ‖y - x‖) * ‖y - x‖ := by
  have hp := integral_norm_bound_of_pairwise P (fun u => g (x - z u)) (hi x)
    (L₀ / L₁) b hb (hloc x)
  have hd (u : Ω) := endpoint_to_increment g L₀ L₁ G hL₁.le hG hpair (y - z u) (x - z u)
  simp only [sub_sub_sub_cancel_right] at hd
  have hint := (((integrable_const L₀).add ((hi x).norm.const_mul L₁)).add
    (integrable_const (L₁ * (L₀ + L₁ * G) * ‖y - x‖))).mul_const ‖y - x‖
  have hbnd := integral_mono ((hi y).sub (hi x)).norm hint hd
  simp only [Pi.add_apply, integral_mul_const] at hbnd
  have hA := integral_add ((integrable_const L₀).add ((hi x).norm.const_mul L₁))
    (integrable_const (L₁ * (L₀ + L₁ * G) * ‖y - x‖))
  have hB := integral_add (integrable_const L₀) ((hi x).norm.const_mul L₁)
  simp only [Pi.add_apply] at hA hB
  rw [hA, hB] at hbnd
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hbnd
  rw [← integral_sub (hi y) (hi x)]
  apply (norm_integral_le_integral_norm _).trans (hbnd.trans _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have ht := mul_le_mul_of_nonneg_left hp hL₁.le
  have he : L₀ + L₁ *
      ((‖∫ u, g (x - z u) ∂(P : Measure Ω)‖ + b * (L₀ / L₁)) / (1 - b)) =
      (L₀ + L₁ * ‖∫ u, g (x - z u) ∂(P : Measure Ω)‖) / (1 - b) := by
    field_simp [hL₁.ne', ne_of_gt (sub_pos.mpr hb)]
    ring
  rw [← he]
  linarith

lemma average_hasGradient_of_remainder
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (P : ProbabilityMeasure Ω) (z : Ω → V) (f : V → ℝ) (g : V → V) (K : ℝ)
    (hf : ∀ x, Integrable (fun u => f (x - z u)) (P : Measure Ω))
    (hg : ∀ x, Integrable (fun u => g (x - z u)) (P : Measure Ω))
    (hrem : ∀ x y, 0 ≤ f y - f x - ⟪g x, y - x⟫ ∧
      f y - f x - ⟪g x, y - x⟫ ≤ K * ‖y - x‖ ^ 2) (x : V) :
    HasGradientAt (fun y => ∫ u, f (y - z u) ∂(P : Measure Ω))
      (∫ u, g (x - z u) ∂(P : Measure Ω)) x := by
  apply CompactConjugate.hasGradientAt_of_quadratic_remainder _ _ _ K
  intro y
  have hi : Integrable (fun u => ⟪y - x, g (x - z u)⟫) (P : Measure Ω) :=
    (innerSL ℝ (y - x)).integrable_comp (hg x)
  have hr : Integrable (fun u => f (y - z u) - f (x - z u) - ⟪y - x, g (x - z u)⟫)
      (P : Measure Ω) := ((hf y).sub (hf x)).sub hi
  have hb (u : Ω) : 0 ≤ f (y - z u) - f (x - z u) - ⟪y - x, g (x - z u)⟫ ∧
      f (y - z u) - f (x - z u) - ⟪y - x, g (x - z u)⟫ ≤ K * ‖y - x‖ ^ 2 := by
    simpa only [sub_sub_sub_cancel_right, real_inner_comm (g (x - z u))] using
      hrem (x - z u) (y - z u)
  have hlo : 0 ≤ ∫ u, f (y - z u) - f (x - z u) - ⟪y - x, g (x - z u)⟫ ∂(P : Measure Ω) :=
    integral_nonneg (fun u => (hb u).1)
  have hhi := integral_mono hr (integrable_const (K * ‖y - x‖ ^ 2)) (fun u => (hb u).2)
  have he := integral_sub ((hf y).sub (hf x)) hi
  have he' := integral_sub (hf y) (hf x)
  simp only [Pi.sub_apply] at he he'
  have heinner := (innerSL ℝ (y - x)).integral_comp_comm (hg x)
  simp only [innerSL_apply_apply] at heinner
  rw [he, he', heinner] at hlo hhi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hhi
  rw [real_inner_comm]
  exact ⟨hlo, hhi⟩

end LongTails.Proofs.GeneralizedSmoothMollification
