import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SoftRadialProjection

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def scale (R : ℝ) (x : E) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2)

noncomputable def project (R : ℝ) (x : E) : E := (scale R x)⁻¹ • x

omit [InnerProductSpace ℝ E] in
lemma scale_sq (R : ℝ) (x : E) : scale R x ^ 2 = 1 + ‖x‖ ^ 2 / R ^ 2 :=
  Real.sq_sqrt (by positivity)

omit [InnerProductSpace ℝ E] in
lemma scale_one_le (R : ℝ) (x : E) : 1 ≤ scale R x := by
  unfold scale
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  have : 0 ≤ ‖x‖ ^ 2 / R ^ 2 := by positivity
  linarith

omit [InnerProductSpace ℝ E] in
lemma scale_pos (R : ℝ) (x : E) : 0 < scale R x := lt_of_lt_of_le zero_lt_one (scale_one_le R x)

lemma norm_project (R : ℝ) (x : E) : ‖project R x‖ = ‖x‖ / scale R x := by
  simp [project, norm_smul, abs_of_pos (scale_pos R x), div_eq_mul_inv, mul_comm]

lemma norm_project_le {R : ℝ} (hR : 0 < R) (x : E) : ‖project R x‖ ≤ R := by
  have hs := scale_sq R x
  have hsp := scale_pos R x
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have he : ‖x‖ ^ 2 = R ^ 2 * (scale R x ^ 2 - 1) := by
    rw [hs]
    field_simp
    ring
  have hnn : 0 ≤ R * scale R x := by positivity
  have hr : ‖x‖ ≤ R * scale R x := by nlinarith [norm_nonneg x]
  rw [norm_project, div_le_iff₀ hsp]
  exact hr

noncomputable def derivative (R : ℝ) (x : E) : E →L[ℝ] E :=
  (scale R x)⁻¹ • ContinuousLinearMap.id ℝ E -
    (1 / (R ^ 2 * scale R x ^ 3)) • (innerSL ℝ x).smulRight x

lemma derivative_apply (R : ℝ) (x v : E) :
    derivative R x v = (scale R x)⁻¹ • v -
      (⟪x, v⟫ / (R ^ 2 * scale R x ^ 3)) • x := by
  simp [derivative, smul_smul, div_eq_mul_inv, mul_comm]

lemma weight_hasFDerivAt {R : ℝ} (hR : 0 < R) (x : E) :
    HasFDerivAt (fun y => (scale R y)⁻¹)
      (-(1 / (R ^ 2 * scale R x ^ 3)) • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hf : HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2 / R ^ 2)
      ((2 / R ^ 2) • innerSL ℝ x) x := by
    convert (hn.const_mul (R ^ 2)⁻¹).const_add 1 using 1
    · ext y
      simp [div_eq_mul_inv, mul_comm]
    · ext v
      simp [div_eq_mul_inv]
      ring
  have hs := hf.sqrt (show 1 + ‖x‖ ^ 2 / R ^ 2 ≠ 0 by positivity)
  have hi := (hasDerivAt_inv (show Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2) ≠ 0 from
    (scale_pos R x).ne')).comp_hasFDerivAt x hs
  apply hi.congr_fderiv
  simp only [smul_smul]
  congr 1
  dsimp [scale]
  field_simp

lemma project_hasFDerivAt {R : ℝ} (hR : 0 < R) (x : E) :
    HasFDerivAt (project R) (derivative R x) x := by
  have hp := (weight_hasFDerivAt hR x).smul (hasFDerivAt_id x)
  convert hp using 1
  · rfl
  · ext v
    simp [derivative, smul_smul]
    module

lemma norm_le_scale {R : ℝ} (hR : 0 < R) (x : E) : ‖x‖ ≤ R * scale R x := by
  have h := norm_project_le hR x
  rwa [norm_project, div_le_iff₀ (scale_pos R x)] at h

lemma derivative_norm_le {R : ℝ} (hR : 0 < R) (x v : E) :
    ‖derivative R x v‖ ≤ 2 * ‖v‖ := by
  have hs := scale_one_le R x
  have hsp := scale_pos R x
  have hd : 0 < R ^ 2 * scale R x ^ 3 := by positivity
  have hr2 : ‖x‖ ^ 2 ≤ R ^ 2 * scale R x ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg x) (norm_le_scale hR x) 2
    simpa only [mul_pow] using h
  have hr3 : ‖x‖ ^ 2 ≤ R ^ 2 * scale R x ^ 3 := hr2.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs (by norm_num : 2 ≤ 3)) (sq_nonneg R))
  have ha : (scale R x)⁻¹ ≤ 1 := (inv_le_one₀ hsp).mpr hs
  have hcross : ‖(⟪x, v⟫ / (R ^ 2 * scale R x ^ 3)) • x‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd]
    calc _ ≤ (‖x‖ * ‖v‖ / (R ^ 2 * scale R x ^ 3)) * ‖x‖ := by
          gcongr
          exact abs_real_inner_le_norm x v
      _ = (‖x‖ ^ 2 / (R ^ 2 * scale R x ^ 3)) * ‖v‖ := by ring
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ((div_le_one hd).mpr hr3) (norm_nonneg v)
      _ = _ := one_mul _
  rw [derivative_apply]
  calc _ ≤ ‖(scale R x)⁻¹ • v‖ + ‖(⟪x, v⟫ / (R ^ 2 * scale R x ^ 3)) • x‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsp)]
      simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg v)) hcross
    _ = _ := by ring

lemma derivative_opNorm_le {R : ℝ} (hR : 0 < R) (x : E) : ‖derivative R x‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (derivative_norm_le hR x)

lemma project_lipschitz {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖project R x - project R y‖ ≤ 2 * ‖x - y‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => (project_hasFDerivAt hR z).hasFDerivWithinAt)
    (fun z _ => derivative_opNorm_le hR z) (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ y) (Set.mem_univ x)

lemma weight_derivative_norm_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖-(1 / (R ^ 2 * scale R x ^ 3)) • innerSL ℝ x‖ ≤ 1 / R := by
  have hs := scale_one_le R x
  have hd : 0 < R ^ 2 * scale R x ^ 3 := by have := scale_pos R x; positivity
  have h13 : scale R x ≤ scale R x ^ 3 := by
    simpa using pow_le_pow_right₀ hs (by norm_num : 1 ≤ 3)
  have hr := (norm_le_scale hR x).trans (mul_le_mul_of_nonneg_left h13 hR.le)
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_div, abs_one, abs_of_pos hd,
    innerSL_apply_norm]
  have he : 1 / (R ^ 2 * scale R x ^ 3) * ‖x‖ = ‖x‖ / (R ^ 2 * scale R x ^ 3) := by ring
  rw [he, div_le_div_iff₀ hd hR]
  nlinarith

lemma weight_lipschitz {R : ℝ} (hR : 0 < R) (x y : E) :
    |(scale R x)⁻¹ - (scale R y)⁻¹| ≤ (1 / R) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => (weight_hasFDerivAt hR z).hasFDerivWithinAt)
    (fun z _ => weight_derivative_norm_le hR z) (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

noncomputable def rankAction (R : ℝ) (u w : E) : E := (⟪u, w⟫ / R ^ 2) • u

lemma rankAction_norm_le {R : ℝ} (hR : 0 < R) {u : E} (hu : ‖u‖ ≤ R) (w : E) :
    ‖rankAction R u w‖ ≤ ‖w‖ := by
  have hd : 0 < R ^ 2 := sq_pos_of_pos hR
  rw [rankAction, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd]
  calc _ ≤ (R * ‖w‖ / R ^ 2) * R := by
        gcongr
        exact (abs_real_inner_le_norm u w).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg w))
    _ = _ := by field_simp

lemma rankAction_difference {R : ℝ} (hR : 0 < R) {u v : E} (hu : ‖u‖ ≤ R)
    (hv : ‖v‖ ≤ R) (w : E) :
    ‖rankAction R u w - rankAction R v w‖ ≤ (2 / R) * ‖u - v‖ * ‖w‖ := by
  have he : rankAction R u w - rankAction R v w =
      (⟪u - v, w⟫ / R ^ 2) • u + (⟪v, w⟫ / R ^ 2) • (u - v) := by
    simp only [rankAction, inner_sub_left, sub_div, sub_smul, smul_sub]
    module
  have hd : 0 < R ^ 2 := sq_pos_of_pos hR
  rw [he]
  calc _ ≤ ‖(⟪u - v, w⟫ / R ^ 2) • u‖ + ‖(⟪v, w⟫ / R ^ 2) • (u - v)‖ := norm_add_le _ _
    _ = |⟪u - v, w⟫| / R ^ 2 * ‖u‖ + |⟪v, w⟫| / R ^ 2 * ‖u - v‖ := by
      simp [norm_smul]
    _ ≤ (‖u - v‖ * ‖w‖ / R ^ 2) * R + (R * ‖w‖ / R ^ 2) * ‖u - v‖ := by
      gcongr
      · exact abs_real_inner_le_norm _ _
      · exact (abs_real_inner_le_norm v w).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
    _ = _ := by field_simp; ring

lemma derivative_factor (R : ℝ) (x w : E) :
    derivative R x w = (scale R x)⁻¹ • (w - rankAction R (project R x) w) := by
  rw [derivative_apply]
  simp only [rankAction, project, inner_smul_left, RCLike.conj_to_real, smul_sub, smul_smul]
  congr 1
  congr 1
  field_simp

lemma derivative_difference {R : ℝ} (hR : 0 < R) (x y w : E) :
    ‖derivative R x w - derivative R y w‖ ≤ (6 / R) * ‖x - y‖ * ‖w‖ := by
  let a := (scale R x)⁻¹
  let b := (scale R y)⁻¹
  let u := project R x
  let v := project R y
  have hu : ‖u‖ ≤ R := norm_project_le hR x
  have hv : ‖v‖ ≤ R := norm_project_le hR y
  have hb : |b| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (scale_pos R y))]
    exact (inv_le_one₀ (scale_pos R y)).mpr (scale_one_le R y)
  have he : derivative R x w - derivative R y w =
      (a - b) • (w - rankAction R u w) + b • (rankAction R v w - rankAction R u w) := by
    rw [derivative_factor, derivative_factor]
    dsimp [a, b, u, v]
    module
  have hfirst : ‖(a - b) • (w - rankAction R u w)‖ ≤ (2 / R) * ‖x - y‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ ((1 / R) * ‖x - y‖) * (2 * ‖w‖) := by
          apply mul_le_mul (weight_lipschitz hR x y)
            ((norm_sub_le _ _).trans (by linarith [rankAction_norm_le hR hu w]))
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsecond : ‖b • (rankAction R v w - rankAction R u w)‖ ≤
      (4 / R) * ‖x - y‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ 1 * ((2 / R) * ‖v - u‖ * ‖w‖) :=
          mul_le_mul hb (rankAction_difference hR hv hu w) (norm_nonneg _) (by norm_num)
      _ ≤ 1 * ((2 / R) * (2 * ‖x - y‖) * ‖w‖) := by
          gcongr
          simpa only [norm_sub_rev y x] using project_lipschitz hR y x
      _ = _ := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

lemma derivative_self_adjoint (R : ℝ) (x v w : E) :
    ⟪derivative R x v, w⟫ = ⟪v, derivative R x w⟫ := by
  rw [derivative_apply, derivative_apply]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm v x]
  ring

lemma composition_gradient [CompleteSpace E] {R : ℝ} (hR : 0 < R) {F : E → ℝ} {g : E} (x : E)
    (hF : HasGradientAt F g (project R x)) :
    HasGradientAt (fun y => F (project R y)) (derivative R x g) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := hF.hasFDerivAt.comp x (project_hasFDerivAt hR x)
  apply h.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
  exact (derivative_self_adjoint R x g v).symm

lemma composition_field_lipschitz {R L G : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (g : E → E) (hbound : ∀ x, ‖g x‖ ≤ G) (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    ‖derivative R x (g (project R x)) - derivative R y (g (project R y))‖ ≤
      (4 * L + 6 * G / R) * ‖x - y‖ := by
  have he : derivative R x (g (project R x)) - derivative R y (g (project R y)) =
      derivative R x (g (project R x) - g (project R y)) +
        (derivative R x (g (project R y)) - derivative R y (g (project R y))) := by
    rw [map_sub]
    abel
  have h1 : ‖derivative R x (g (project R x) - g (project R y))‖ ≤ 4 * L * ‖x - y‖ := by
    calc _ ≤ 2 * ‖g (project R x) - g (project R y)‖ := derivative_norm_le hR _ _
      _ ≤ 2 * (L * (2 * ‖x - y‖)) := mul_le_mul_of_nonneg_left
        ((hlip _ _).trans (mul_le_mul_of_nonneg_left (project_lipschitz hR x y) hL)) (by norm_num)
      _ = _ := by ring
  have h2 : ‖derivative R x (g (project R y)) - derivative R y (g (project R y))‖ ≤
      (6 * G / R) * ‖x - y‖ := by
    calc _ ≤ (6 / R) * ‖x - y‖ * ‖g (project R y)‖ := derivative_difference hR _ _ _
      _ ≤ (6 / R) * ‖x - y‖ * G := by gcongr; exact hbound _
      _ = _ := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end LongTails.Proofs.SoftRadialProjection
