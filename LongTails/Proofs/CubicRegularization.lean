import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

namespace LongTails.Proofs.CubicRegularization

open scoped RealInnerProductSpace Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def cubic (x : E) : ℝ := ‖x‖ ^ 3 / 3

noncomputable def cubicGradient (x : E) : E := ‖x‖ • x

noncomputable def cubicHessian (x : E) : E →L[ℝ] E :=
  ‖x‖ • ContinuousLinearMap.id ℝ E +
    ‖x‖⁻¹ • (innerSL ℝ x).smulRight x

lemma cubic_hasFDerivAt (x : E) :
    HasFDerivAt cubic (innerSL ℝ (cubicGradient x)) x := by
  have h := (hasFDerivAt_norm_rpow x (by norm_num : (1 : ℝ) < 3)).const_mul (1 / 3)
  convert h using 1
  · ext y
    simp [cubic]
    ring
  · ext y
    norm_num [cubicGradient, real_inner_smul_left]
    ring

lemma cubicGradient_strong_monotone (x y : E) :
    ‖x - y‖ ^ 3 / 2 ≤ ⟪cubicGradient x - cubicGradient y, x - y⟫ := by
  have hn : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have he : ⟪cubicGradient x - cubicGradient y, x - y⟫ =
      (‖x‖ + ‖y‖) / 2 * ‖x - y‖ ^ 2 +
        (‖x‖ + ‖y‖) / 2 * (‖x‖ - ‖y‖) ^ 2 := by
    simp only [cubicGradient, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm y x]
    ring
  rw [he]
  have h₁ := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖x - y‖)
  have h₂ := mul_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))
    (sq_nonneg (‖x‖ - ‖y‖))
  nlinarith

lemma cubic_bregman_lower (x y : E) :
    ‖x - y‖ ^ 3 / 6 ≤ cubic x - cubic y - ⟪cubicGradient y, x - y⟫ := by
  have ht := abs_real_inner_le_norm x y
  have hlo := (abs_le.mp ht).1
  have hup := (abs_le.mp ht).2
  have hd := norm_sub_sq_real x y
  have hn := norm_sub_le x y
  have ha := norm_nonneg x
  have hb := norm_nonneg y
  have he : cubic x - cubic y - ⟪cubicGradient y, x - y⟫ =
      ‖x‖ ^ 3 / 3 + 2 * ‖y‖ ^ 3 / 3 - ‖y‖ * ⟪x, y⟫ := by
    simp only [cubic, cubicGradient, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm y x]
    ring
  rw [he]
  have hbase : (‖x‖ + ‖y‖) * ‖x - y‖ ^ 2 ≤
      2 * ‖x‖ ^ 3 + 4 * ‖y‖ ^ 3 - 6 * ‖y‖ * ⟪x, y⟫ := by
    rw [hd]
    by_cases hh : 2 * ‖y‖ ≤ ‖x‖
    · have hp := mul_nonneg (by linarith : 0 ≤ ‖x‖ - 2 * ‖y‖)
        (by linarith : 0 ≤ ⟪x, y⟫ + ‖x‖ * ‖y‖)
      have hc : 0 ≤ (‖x‖ - ‖y‖) ^ 3 := pow_nonneg (by linarith) _
      have hb3 : 0 ≤ ‖y‖ ^ 3 := pow_nonneg hb _
      nlinarith
    · have hp := mul_nonneg (by linarith : 0 ≤ 2 * ‖y‖ - ‖x‖)
        (by linarith : 0 ≤ ‖x‖ * ‖y‖ - ⟪x, y⟫)
      have hc := mul_nonneg (sq_nonneg (‖x‖ - ‖y‖))
        (by linarith : 0 ≤ ‖x‖ + 3 * ‖y‖)
      nlinarith
  have hm := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖x - y‖)
  nlinarith

lemma cubicGradient_hasFDerivAt_zero :
    HasFDerivAt (cubicGradient : E → E) (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  have he : (fun x : E => ‖x - 0‖⁻¹ *
      ‖cubicGradient x - cubicGradient 0 - (0 : E →L[ℝ] E) (x - 0)‖) =
      fun x => ‖x‖ := by
    ext x
    simp only [cubicGradient, norm_zero, zero_smul, sub_zero,
      zero_apply, norm_smul, Real.norm_eq_abs, abs_norm]
    by_cases hx : ‖x‖ = 0
    · simp [hx]
    · field_simp
  rw [he]
  simpa using (continuous_norm.tendsto (0 : E))

lemma cubicGradient_hasFDerivAt (x : E) :
    HasFDerivAt cubicGradient (cubicHessian x) x := by
  by_cases hx : x = 0
  · subst x
    simpa [cubicHessian] using cubicGradient_hasFDerivAt_zero (E := E)
  · have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by simpa using hx)
    have h := hn.smul (hasFDerivAt_id x)
    convert h using 1
    · ext y
      simp [cubicGradient]
    · ext y
      simp [cubicHessian, Real.sqrt_sq (norm_nonneg x)]
      module

lemma normalized_distance (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have he : ‖x‖ • (‖x‖⁻¹ • x - ‖y‖⁻¹ • y) =
      (x - y) + ((1 - ‖x‖ / ‖y‖) • y) := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hx0, one_smul, div_eq_mul_inv]
    module
  have hn := norm_add_le (x - y) ((1 - ‖x‖ / ‖y‖) • y)
  have hab : |1 - ‖x‖ / ‖y‖| * ‖y‖ = |‖y‖ - ‖x‖| := by
    calc
      _ = |(1 - ‖x‖ / ‖y‖) * ‖y‖| := by rw [abs_mul, abs_norm]
      _ = _ := by congr 1; field_simp
  rw [← he, norm_smul, Real.norm_eq_abs, abs_norm] at hn
  rw [norm_smul, Real.norm_eq_abs, hab] at hn
  have hr := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hr
  linarith

noncomputable def radialRank (x : E) : E →L[ℝ] E :=
  (innerSL ℝ (‖x‖⁻¹ • x)).smulRight x

lemma radialRank_norm (x : E) : ‖radialRank x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [radialRank, hx]
  · rw [radialRank, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp

lemma radialRank_lipschitz_ordered (x y : E) (hxy : ‖y‖ ≤ ‖x‖) :
    ‖radialRank x - radialRank y‖ ≤ 3 * ‖x - y‖ := by
  by_cases hy : y = 0
  · have hzero : radialRank (0 : E) = 0 := by simp [radialRank]
    rw [hy, hzero, sub_zero, sub_zero, radialRank_norm]
    nlinarith [norm_nonneg x]
  have hx : x ≠ 0 := by
    intro hh
    simp only [hh, norm_zero, norm_le_zero_iff] at hxy
    exact hy hxy
  have he : radialRank x - radialRank y =
      (innerSL ℝ (‖x‖⁻¹ • x)).smulRight (x - y) +
      (innerSL ℝ (‖x‖⁻¹ • x - ‖y‖⁻¹ • y)).smulRight y := by
    ext v
    simp only [radialRank, sub_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, sub_apply]
    module
  rw [he]
  have hn := norm_add_le
    ((innerSL ℝ (‖x‖⁻¹ • x)).smulRight (x - y))
    ((innerSL ℝ (‖x‖⁻¹ • x - ‖y‖⁻¹ • y)).smulRight y)
  simp only [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm] at hn
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  rw [hu, one_mul] at hn
  have hd := normalized_distance x y hx hy
  have hm := mul_le_mul_of_nonneg_left hxy
    (norm_nonneg (‖x‖⁻¹ • x - ‖y‖⁻¹ • y))
  nlinarith

lemma radialRank_lipschitz (x y : E) :
    ‖radialRank x - radialRank y‖ ≤ 3 * ‖x - y‖ := by
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact radialRank_lipschitz_ordered x y h
  · simpa only [norm_sub_rev] using radialRank_lipschitz_ordered y x h

lemma cubicHessian_lipschitz (x y : E) :
    ‖cubicHessian x - cubicHessian y‖ ≤ 4 * ‖x - y‖ := by
  have he (z : E) : cubicHessian z =
      ‖z‖ • ContinuousLinearMap.id ℝ E + radialRank z := by
    ext v
    simp [cubicHessian, radialRank]
    module
  rw [he x, he y]
  have heq : ‖x‖ • ContinuousLinearMap.id ℝ E + radialRank x -
      (‖y‖ • ContinuousLinearMap.id ℝ E + radialRank y) =
      (‖x‖ - ‖y‖) • ContinuousLinearMap.id ℝ E + (radialRank x - radialRank y) := by
    module
  rw [heq]
  have hn := norm_add_le ((‖x‖ - ‖y‖) • ContinuousLinearMap.id ℝ E)
    (radialRank x - radialRank y)
  rw [norm_smul, Real.norm_eq_abs] at hn
  have hm := mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    (abs_nonneg (‖x‖ - ‖y‖))
  have hr := abs_norm_sub_norm_le x y
  have hq := radialRank_lipschitz x y
  nlinarith

lemma cubic_convex : ConvexOn ℝ Set.univ (cubic : E → ℝ) := by
  have h := (convexOn_univ_norm (E := E)).pow (fun x _ => norm_nonneg x) 3
  convert h.smul (by norm_num : (0 : ℝ) ≤ 1 / 3) using 1
  ext x
  simp [cubic]
  ring

lemma cubicHessian_symmetric (z x y : E) :
    ⟪x, cubicHessian z y⟫ = ⟪cubicHessian z x, y⟫ := by
  simp only [cubicHessian, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right]
  change ‖z‖ * ⟪x, y⟫ + ‖z‖⁻¹ * (⟪z, y⟫ * ⟪x, z⟫) =
    ‖z‖ * ⟪x, y⟫ + ‖z‖⁻¹ * (⟪z, x⟫ * ⟪z, y⟫)
  rw [real_inner_comm z x]
  ring

lemma cubicHessian_nonneg (z x : E) : 0 ≤ ⟪x, cubicHessian z x⟫ := by
  simp only [cubicHessian, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    inner_add_right, inner_smul_right]
  change 0 ≤ ‖z‖ * ⟪x, x⟫ + ‖z‖⁻¹ * (⟪z, x⟫ * ⟪x, z⟫)
  rw [real_inner_comm z x, real_inner_self_eq_norm_sq, ← sq]
  positivity

lemma cubicHessian_continuous : Continuous (cubicHessian : E → E →L[ℝ] E) := by
  have h : LipschitzWith 4 (cubicHessian : E → E →L[ℝ] E) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using cubicHessian_lipschitz x y
  exact h.continuous

lemma cubicGradient_contDiff : ContDiff ℝ 1 (cubicGradient : E → E) := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨cubicHessian, cubicHessian_continuous, cubicGradient_hasFDerivAt⟩

lemma cubic_contDiff : ContDiff ℝ 2 (cubic : E → ℝ) := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun x => innerSL ℝ (cubicGradient x), ?_, cubic_hasFDerivAt⟩
  exact (innerSL ℝ).contDiff.comp cubicGradient_contDiff

lemma cubic_gradient [CompleteSpace E] (x : E) : gradient cubic x = cubicGradient x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  exact cubic_hasFDerivAt x

lemma cubic_hessian [CompleteSpace E] (x : E) :
    fderiv ℝ (gradient cubic) x = cubicHessian x := by
  have he : gradient (cubic : E → ℝ) = cubicGradient := funext cubic_gradient
  rw [he]
  exact (cubicGradient_hasFDerivAt x).fderiv

lemma gradient_taylor {g : E → E} {A : E → E →L[ℝ] E} {H : ℝ}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (x d : E) :
    ‖g (x + d) - g x - A x d‖ ≤ H * ‖d‖ ^ 2 / 2 := by
  let R : ℝ → E := fun t => g (x + t • d) - g x - t • A x d
  let D : ℝ → E := fun t => (A (x + t • d) - A x) d
  have hd (t : ℝ) : HasDerivAt R (D t) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have ht := ((hg (x + t • d)).comp_hasDerivAt t hline).sub_const (g x)
    convert ht.sub ((hasDerivAt_id t).smul_const (A x d)) using 1
    · ext t
      rfl
    · simp [D]
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => H * ‖d‖ ^ 2 / 2 * t ^ 2)
      (H * ‖d‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (H * ‖d‖ ^ 2 / 2) using 1
    · ext t
      rfl
    · simp
      ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖D t‖ ≤ H * ‖d‖ ^ 2 * t := by
    have h₁ := (A (x + t • d) - A x).le_opNorm d
    have h₂ := hLip (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h₂
    have h₃ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg d)
    dsimp [D]
    nlinarith only [h₁, h₃]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := R) (f' := D)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (B := fun t => H * ‖d‖ ^ 2 / 2 * t ^ 2)
    (by simp [R]) hB hb (x := 1) (by norm_num)
  simpa [R] using h

lemma objective_taylor {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E} {H : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (x d : E) :
    |f (x + d) - f x - ⟪g x, d⟫ - ⟪d, A x d⟫ / 2| ≤ H * ‖d‖ ^ 3 / 6 := by
  let R : ℝ → ℝ := fun t => f (x + t • d) - f x - t * ⟪g x, d⟫ - t ^ 2 * ⟪d, A x d⟫ / 2
  let D : ℝ → ℝ := fun t => ⟪g (x + t • d) - g x - t • A x d, d⟫
  have hd (t : ℝ) : HasDerivAt R (D t) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h₀ := ((hf (x + t • d)).comp_hasDerivAt t hline).sub_const (f x)
    have h₁ := h₀.sub ((hasDerivAt_id t).mul_const ⟪g x, d⟫)
    have h₂ := ((hasDerivAt_id t).pow 2).mul_const (⟪d, A x d⟫ / 2)
    convert h₁.sub h₂ using 1
    · ext t
      simp [R]
      ring
    · simp [D, inner_sub_left, real_inner_smul_left, real_inner_comm d (A x d)]
      ring
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => H * ‖d‖ ^ 3 / 6 * t ^ 3)
      (H * ‖d‖ ^ 3 / 2 * t ^ 2) t := by
    convert ((hasDerivAt_id t).pow 3).const_mul (H * ‖d‖ ^ 3 / 6) using 1
    · ext t
      rfl
    · simp
      ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖D t‖ ≤ H * ‖d‖ ^ 3 / 2 * t ^ 2 := by
    have h₁ := gradient_taylor hg hLip x (t • d)
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h₁
    have h₂ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg d)
    have h₃ := norm_inner_le_norm (𝕜 := ℝ) (g (x + t • d) - g x - t • A x d) d
    calc
      ‖D t‖ ≤ H * (t * ‖d‖) ^ 2 / 2 * ‖d‖ := h₃.trans h₂
      _ = _ := by ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := R) (f' := D)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (B := fun t => H * ‖d‖ ^ 3 / 6 * t ^ 3)
    (by simp [R]) hB hb (x := 1) (by norm_num)
  simpa [R, Real.norm_eq_abs] using h

lemma symmetric_taylor {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E} {H : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (x d : E) :
    |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3 := by
  have h₁ := objective_taylor hf hg hLip x d
  have h₂ := objective_taylor hf hg hLip x (-d)
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg, norm_neg,
    ← sub_eq_add_neg] at h₂
  have hlow₁ := (abs_le.mp h₁).1
  have hhigh₁ := (abs_le.mp h₁).2
  have hlow₂ := (abs_le.mp h₂).1
  have hhigh₂ := (abs_le.mp h₂).2
  apply abs_le.mpr
  constructor <;> linarith

end LongTails.Proofs.CubicRegularization
