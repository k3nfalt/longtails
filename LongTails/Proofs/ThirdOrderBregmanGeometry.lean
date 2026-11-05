import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Proofs.HeavyTailedPLStep

namespace LongTails.Proofs.ThirdOrderBregmanGeometry

open scoped RealInnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def residual (f : E → ℝ) (s x : E) : E :=
  gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s

noncomputable def translatedGap (f : E → ℝ) (s x : E) : ℝ :=
  f (x + s) - f x - ⟪gradient f x, s⟫

lemma translatedGap_gradient {f : E → ℝ} (hf : ContDiff ℝ 3 f) (s x : E) :
    HasGradientAt (translatedGap f s) (residual f s x) x := by
  have hd := GradientDependentLocal.derivative_chain hf
  have hshift := (hd.1 (x + s)).comp x ((hasFDerivAt_id x).add_const s)
  have hi := (hd.2.1 x).inner ℝ (hasFDerivAt_const s x)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hshift.sub (hd.1 x)).sub hi using 1
  · rfl
  · ext v
    simp [residual]
    rw [real_inner_comm s]
    exact OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) x s v

lemma translatedGap_nonneg {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) (s x : E) : 0 ≤ translatedGap f s x := by
  have hh := OracleTemplate.Gradient.convex_support hc
    (fun z => (hf.differentiable (by norm_num) z).hasGradientAt) x (x + s)
  simpa [translatedGap, sub_nonneg] using hh

lemma residual_derivative {f : E → ℝ} (hf : ContDiff ℝ 3 f) (s x : E) :
    HasFDerivAt (residual f s)
      (fderiv ℝ (gradient f) (x + s) - fderiv ℝ (gradient f) x -
        fderiv ℝ (fderiv ℝ (gradient f)) x s) x := by
  have hd := GradientDependentLocal.derivative_chain hf
  have hshift := (hd.2.1 (x + s)).comp x ((hasFDerivAt_id x).add_const s)
  have happ := (hd.2.2 x).clm_apply (hasFDerivAt_const s x)
  convert (hshift.sub (hd.2.1 x)).sub happ using 1
  · rfl
  · ext v
    simpa using congrArg (fun z => fderiv ℝ (gradient f) (x + s) v -
      fderiv ℝ (gradient f) x v - z)
      (ThirdOrderObjectiveGeometry.third_swap_first hf x s v)

lemma residual_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (s x y : E) :
    ‖residual f s y - residual f s x‖ ≤ L * ‖s‖ ^ 2 * ‖y - x‖ := by
  apply (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (residual_derivative hf s z).hasFDerivWithinAt)
    (fun z _ => ?_) (mem_univ x) (mem_univ y)
  simpa only [add_sub_cancel_left] using
    ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT z (z + s)

lemma residual_self_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (s x : E) :
    ‖residual f s x‖ ^ 2 ≤ 2 * L * ‖s‖ ^ 2 * translatedGap f s x := by
  by_cases hs : s = 0
  · simp [hs, residual]
  have hp : 0 < L * ‖s‖ ^ 2 := mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr hs))
  have hd := OracleTemplate.Gradient.descent hp (translatedGap_gradient hf s)
    (fun a b => residual_lipschitz hf hL.le hT s b a) x
  have hn := translatedGap_nonneg hf hc s
    (x - (1 / (L * ‖s‖ ^ 2)) • residual f s x)
  have hh : ‖residual f s x‖ ^ 2 / (2 * (L * ‖s‖ ^ 2)) ≤
      translatedGap f s x := by linarith
  have h := (div_le_iff₀ (show 0 < 2 * (L * ‖s‖ ^ 2) by positivity)).mp hh
  nlinarith

lemma reversal_algebra {a b c f₀ f₁ f₂ fneg Drev M : ℝ}
    (h₁ : |f₁ - f₀ - c - a / 2 - b / 6| ≤ M)
    (h₂ : |f₂ - f₀ - 2 * c - 2 * a - 4 * b / 3| ≤ 16 * M)
    (hneg : |fneg - f₀ + 2 * c - 2 * a + 4 * b / 3| ≤ 16 * M)
    (hs₂ : 2 * c ≤ f₂ - f₀) (hsneg : -(2 * c) ≤ fneg - f₀)
    (hr : Drev ≤ f₂ - 2 * f₁ + f₀) :
    Drev ≤ 10 * (f₁ - f₀ - c) + 60 * M := by
  have h1 := (abs_le.mp h₁)
  have h2 := (abs_le.mp h₂)
  have hn := (abs_le.mp hneg)
  linarith

lemma translatedGap_reverse {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (s x : E) :
    translatedGap f (-s) (x + s) ≤
      10 * translatedGap f s x + 60 * (L * ‖s‖ ^ 4) := by
  have hg := fun z => (hf.differentiable (by norm_num) z).hasGradientAt
  have h1 := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT x s 1
  have h2 := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT x s 2
  have hn := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT x s (-2)
  have hs2 := OracleTemplate.Gradient.convex_support hc hg x (x + (2 : ℝ) • s)
  have hsn := OracleTemplate.Gradient.convex_support hc hg x (x + (-2 : ℝ) • s)
  have hsr := OracleTemplate.Gradient.convex_support hc hg (x + s) (x + (2 : ℝ) • s)
  have he : x + (2 : ℝ) • s - (x + s) = s := by module
  rw [he] at hsr
  simp only [add_sub_cancel_left, inner_smul_right] at hs2 hsn
  norm_num at h1 h2 hn
  have hr : translatedGap f (-s) (x + s) ≤
      f (x + (2 : ℝ) • s) - 2 * f (x + s) + f x := by
    simp only [translatedGap, add_neg_cancel_right, inner_neg_right, sub_neg_eq_add]
    linarith
  have hgrad : (fderiv ℝ f x) s = ⟪gradient f x, s⟫ := by
    rw [← toDual_gradient]
    rfl
  rw [hgrad] at h1 h2 hn
  change translatedGap f (-s) (x + s) ≤
    10 * (f (x + s) - f x - ⟪gradient f x, s⟫) + 60 * (L * ‖s‖ ^ 4)
  apply reversal_algebra h1 ?_ ?_ hs2 (by simpa using hsn) hr
  · convert h2 using 1 <;> ring_nf
  · convert hn using 1 <;> ring_nf

lemma convex_hessian_nonneg {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) (x v : E) :
    0 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫ := by
  have hg := (GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)
  have hs : ∀ a b, f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    intro a b
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun z => (hf.differentiable (by norm_num) z).hasGradientAt) a b
    linarith
  simpa using OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound hg hs x v

lemma hessian_form_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (x s v : E) :
    |⟪fderiv ℝ (gradient f) (x + s) v, v⟫ - ⟪fderiv ℝ (gradient f) x v, v⟫ -
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x s v, v⟫| ≤ L * ‖s‖ ^ 2 * ‖v‖ ^ 2 := by
  let A := fderiv ℝ (gradient f) (x + s) - fderiv ℝ (gradient f) x -
    fderiv ℝ (fderiv ℝ (gradient f)) x s
  have hA : ‖A‖ ≤ L * ‖s‖ ^ 2 := by
    simpa only [A, add_sub_cancel_left] using
      ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT x (x + s)
  have he : |⟪A v, v⟫| ≤ L * ‖s‖ ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _)
      _ ≤ (L * ‖s‖ ^ 2 * ‖v‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  simpa only [A, sub_apply, inner_sub_left] using he

lemma third_mixed_convex_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (x s v : E) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) x s v, v⟫| ≤
      (1 / 2) * ⟪fderiv ℝ (gradient f) x v, v⟫ + 2 * L * ‖s‖ ^ 2 * ‖v‖ ^ 2 := by
  have hp := (abs_le.mp (hessian_form_remainder hf hL hT x ((2 : ℝ) • s) v)).2
  have hm := (abs_le.mp (hessian_form_remainder hf hL hT x ((-2 : ℝ) • s) v)).2
  have hnp := convex_hessian_nonneg hf hc (x + (2 : ℝ) • s) v
  have hnm := convex_hessian_nonneg hf hc (x + (-2 : ℝ) • s) v
  simp only [map_smul, smul_apply, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs] at hp hm
  norm_num at hp hm
  simp only [neg_smul] at hnm
  apply abs_le.mpr
  constructor <;> nlinarith

lemma convex_value_upper {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (x s : E) :
    f (x + s) ≤ f x + ⟪gradient f x, s⟫ +
      (3 / 4) * ⟪fderiv ℝ (gradient f) x s, s⟫ + 2 * L * ‖s‖ ^ 4 := by
  have hr := (abs_le.mp
    (ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT x s 1)).2
  have ht := (abs_le.mp (third_mixed_convex_bound hf hc hL hT x s s)).2
  have hh := convex_hessian_nonneg hf hc x s
  have hn := mul_nonneg hL (pow_nonneg (norm_nonneg s) 4)
  norm_num only [one_smul, one_pow, abs_one, mul_one] at hr
  nlinarith [sq_nonneg (‖s‖ ^ 2)]

end LongTails.Proofs.ThirdOrderBregmanGeometry
