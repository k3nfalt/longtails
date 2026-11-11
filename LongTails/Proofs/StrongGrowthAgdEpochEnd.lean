import LongTails.Proofs.StrongGrowthAgdModel
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.StrongGrowthAgdEpochEnd

open scoped RealInnerProductSpace
open LongTails.Proofs.StrongGrowthAgdModel LongTails.Proofs.AdaptiveSilverSplit
open OracleTemplate.NonlinearTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

structure Hyp (f : E → ℝ) (L ρ : ℝ) : Prop where
  hL : 0 < L
  hρ : 0 ≤ ρ
  hf : ContDiff ℝ 2 f
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  hess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖

variable {f : E → ℝ} {L ρ : ℝ}

omit [FiniteDimensional ℝ E] in
lemma Hyp.hasGrad (h : Hyp f L ρ) (x : E) : HasGradientAt f (gradient f x) x :=
  ((h.hf.differentiable (by norm_num)) x).hasGradientAt

lemma Hyp.gradDiff (h : Hyp f L ρ) : Differentiable ℝ (gradient f) :=
  (gradient_contDiff_one h.hf).differentiable (by norm_num)

lemma Hyp.symm (h : Hyp f L ρ) (x0 u v : E) :
    ⟪fderiv ℝ (gradient f) x0 u, v⟫ = ⟪u, fderiv ℝ (gradient f) x0 v⟫ :=
  hessian_symmetric h.hf x0 u v

omit [FiniteDimensional ℝ E] in
lemma Hyp.hessNorm (h : Hyp f L ρ) (x0 : E) : ‖fderiv ℝ (gradient f) x0‖ ≤ L := by
  have hl : LipschitzWith ⟨L, h.hL.le⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact h.lip x y
  exact norm_fderiv_le_of_lipschitz ℝ hl (x₀ := x0)

omit [FiniteDimensional ℝ E] in
lemma Hyp.hessQuad (h : Hyp f L ρ) (x0 v : E) :
    |⟪fderiv ℝ (gradient f) x0 v, v⟫| ≤ L * ‖v‖ ^ 2 := by
  calc |⟪fderiv ℝ (gradient f) x0 v, v⟫| ≤ ‖fderiv ℝ (gradient f) x0 v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (L * ‖v‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact ((fderiv ℝ (gradient f) x0).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (h.hessNorm x0) (norm_nonneg _))
    _ = L * ‖v‖ ^ 2 := by ring

lemma Hyp.gradModel_err (h : Hyp f L ρ) (x0 x : E) :
    ‖gradient f x - gradModel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) x‖ ≤ ρ * ‖x - x0‖ ^ 2 := by
  have := gradient_linearization_bound h.hρ h.gradDiff h.hess x0 x
  unfold gradModel
  rw [show gradient f x - (gradient f x0 + fderiv ℝ (gradient f) x0 (x - x0)) =
    gradient f x - gradient f x0 - fderiv ℝ (gradient f) x0 (x - x0) by abel]
  exact this

lemma gmodel_hasFDerivAt (h : Hyp f L ρ) (x0 : E) (f0 : ℝ) (y : E) :
    HasFDerivAt (gmodel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) f0)
      (innerSL ℝ (gradModel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) y)) y := by
  set H := fderiv ℝ (gradient f) x0
  set g0 := gradient f x0
  have hsub : HasFDerivAt (fun y : E => y - x0) (ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).sub_const x0
  have hlin : HasFDerivAt (fun y : E => ⟪g0, y - x0⟫) ((innerSL ℝ g0).comp (ContinuousLinearMap.id ℝ E)) y :=
    (innerSL ℝ g0).hasFDerivAt.comp y hsub
  have hHy : HasFDerivAt (fun y : E => H (y - x0)) (H.comp (ContinuousLinearMap.id ℝ E)) y :=
    H.hasFDerivAt.comp y hsub
  have hquad : HasFDerivAt (fun t : E => ⟪H (t - x0), t - x0⟫)
      ((fderivInnerCLM ℝ (H (y - x0), y - x0)).comp
        ((H.comp (ContinuousLinearMap.id ℝ E)).prod (ContinuousLinearMap.id ℝ E))) y :=
    hHy.inner ℝ hsub
  have hall := ((hasFDerivAt_const f0 y).add hlin).add (hquad.const_mul (1 / 2 : ℝ))
  have hfun : gmodel H x0 g0 f0 =
      ((fun _ : E => f0) + fun y : E => ⟪g0, y - x0⟫) + fun y : E => 1 / 2 * ⟪H (y - x0), y - x0⟫ := by
    funext y; simp only [gmodel, Pi.add_apply]; ring
  rw [hfun]
  convert hall using 1
  ext v
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply,
    smul_apply, smul_eq_mul, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    zero_add]
  have hs : ⟪H v, y - x0⟫ = ⟪H (y - x0), v⟫ := by
    rw [h.symm x0 v (y - x0), real_inner_comm]
  have e1 : ⟪gradModel H x0 g0 y, v⟫ = ⟪g0, v⟫ + ⟪H (y - x0), v⟫ := by
    unfold gradModel; exact inner_add_left _ _ _
  linarith [hs, e1]

lemma Hyp.model_err (h : Hyp f L ρ) (x0 x : E) :
    |f x - gmodel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) (f x0) x| ≤ ρ * ‖x - x0‖ ^ 3 := by
  set H := fderiv ℝ (gradient f) x0
  set g0 := gradient f x0
  let R := fun y => f y - gmodel H x0 g0 (f x0) y
  have hR (y : E) : HasFDerivAt R
      (InnerProductSpace.toDual ℝ E (gradient f y) - innerSL ℝ (gradModel H x0 g0 y)) y :=
    (h.hasGrad y).sub (gmodel_hasFDerivAt h x0 (f x0) y)
  have hnorm (y : E) : ‖InnerProductSpace.toDual ℝ E (gradient f y) - innerSL ℝ (gradModel H x0 g0 y)‖ =
      ‖gradient f y - gradModel H x0 g0 y‖ := by
    have : InnerProductSpace.toDual ℝ E (gradient f y) - innerSL ℝ (gradModel H x0 g0 y) =
        innerSL ℝ (gradient f y - gradModel H x0 g0 y) := by
      ext v
      simp
    rw [this, innerSL_apply_norm]
  have hb (y : E) (hy : y ∈ Metric.closedBall x0 ‖x - x0‖) :
      ‖InnerProductSpace.toDual ℝ E (gradient f y) - innerSL ℝ (gradModel H x0 g0 y)‖ ≤
        ρ * ‖x - x0‖ ^ 2 := by
    rw [hnorm]
    refine (h.gradModel_err x0 y).trans ?_
    apply mul_le_mul_of_nonneg_left _ h.hρ
    have hy' : ‖y - x0‖ ≤ ‖x - x0‖ := by simpa [dist_eq_norm] using hy
    exact pow_le_pow_left₀ (norm_nonneg _) hy' 2
  have hh := (convex_closedBall x0 ‖x - x0‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y _ => (hR y).hasFDerivWithinAt) hb
    (show x0 ∈ Metric.closedBall x0 ‖x - x0‖ by simp)
    (show x ∈ Metric.closedBall x0 ‖x - x0‖ by simp [dist_eq_norm])
  have hR0 : R x0 = 0 := by simp [R, gmodel]
  simp only [R, hR0, sub_zero] at hh
  rw [Real.norm_eq_abs] at hh
  calc |f x - gmodel H x0 g0 (f x0) x| ≤ ρ * ‖x - x0‖ ^ 2 * ‖x - x0‖ := hh
    _ = ρ * ‖x - x0‖ ^ 3 := by ring

lemma gmodel_shift (h : Hyp f L ρ) (x0 : E) (f0 : ℝ) (y v : E) :
    gmodel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) f0 (y - v) =
      gmodel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) f0 y -
        ⟪gradModel (fderiv ℝ (gradient f) x0) x0 (gradient f x0) y, v⟫ +
        ⟪fderiv ℝ (gradient f) x0 v, v⟫ / 2 := by
  set H := fderiv ℝ (gradient f) x0 with hHdef
  have hsym : ∀ u w : E, ⟪H u, w⟫ = ⟪u, H w⟫ := fun u w => h.symm x0 u w
  unfold gmodel gradModel
  have e1 : y - v - x0 = (y - x0) - v := by abel
  rw [e1, map_sub]
  have h1 : ⟪H (y - x0) - H v, y - x0 - v⟫ =
      ⟪H (y - x0), y - x0⟫ - 2 * ⟪H (y - x0), v⟫ + ⟪H v, v⟫ := by
    have e2 : ⟪H v, y - x0⟫ = ⟪H (y - x0), v⟫ := by rw [hsym v (y - x0), real_inner_comm]
    rw [inner_sub_left, inner_sub_right (H (y - x0)) (y - x0) v, inner_sub_right (H v) (y - x0) v, e2]
    ring
  have h2 : ⟪gradient f x0, y - x0 - v⟫ = ⟪gradient f x0, y - x0⟫ - ⟪gradient f x0, v⟫ :=
    inner_sub_right _ _ _
  have h3 : ⟪gradient f x0 + H (y - x0), v⟫ = ⟪gradient f x0, v⟫ + ⟪H (y - x0), v⟫ :=
    inner_add_left _ _ _
  rw [h1, h2, h3]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma gradModel_shift (x0 g0 : E) (H : E →L[ℝ] E) (y v : E) :
    gradModel H x0 g0 (y - v) = gradModel H x0 g0 y - H v := by
  unfold gradModel
  rw [show y - v - x0 = (y - x0) - v by abel, map_sub]
  abel

theorem epoch_end_f_bound (h : Hyp f L ρ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (x0 : E) {η θ B : ℝ}
    (hη : η = 1 / (8 * L)) (_hθ : 0 < θ) (_hB : 0 ≤ B)
    (hH : ∀ j v, ⟪b j, fderiv ℝ (gradient f) x0 v⟫ = eig j * ⟪b j, v⟫)
    (y ghat d' : E) (hy : ‖y - x0‖ ≤ 2 * B) :
    let H := fderiv ℝ (gradient f) x0
    let g0 := gradient f x0
    let xτ := y - η • ghat
    let δ := gradient f y - gradModel H x0 g0 y
    f xτ ≤ Phi b eig H x0 g0 (f x0) η θ xτ d' + 9 / 25 * η * ‖gradModel H x0 g0 y‖ ^ 2 +
      147 / 1000 * η * ‖ghat‖ ^ 2 + 8 * ρ * B ^ 3 + 16 * η * ‖δ‖ ^ 2 := by
  intro H g0 xτ δ
  have hL := h.hL
  have hHdef : H = fderiv ℝ (gradient f) x0 := rfl
  have hηpos : 0 < η := by rw [hη]; positivity
  have hLη : L * η = 1 / 8 := by rw [hη]; field_simp
  have h1 : f xτ ≤ f y + ⟪gradient f y, xτ - y⟫ + L / 2 * ‖xτ - y‖ ^ 2 :=
    OracleTemplate.Gradient.smooth_upper_bound h.hasGrad h.lip y xτ
  have hxy : xτ - y = -(η • ghat) := by simp only [xτ]; abel
  rw [hxy, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hηpos, mul_pow] at h1
  have h2 : f y ≤ gmodel H x0 g0 (f x0) y + 8 * ρ * B ^ 3 := by
    have := (abs_le.mp (h.model_err x0 y)).2
    have hy3 : ‖y - x0‖ ^ 3 ≤ (2 * B) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hy 3
    nlinarith [h.hρ]
  have h3 : gmodel H x0 g0 (f x0) y = gmodel H x0 g0 (f x0) xτ + η * ⟪gradModel H x0 g0 y, ghat⟫ -
      ⟪H (η • ghat), η • ghat⟫ / 2 := by
    have := gmodel_shift h x0 (f x0) y (η • ghat)
    simp only [xτ]
    rw [this, inner_smul_right]
    ring
  have h3' : -⟪H (η • ghat), η • ghat⟫ / 2 ≤ η / 16 * ‖ghat‖ ^ 2 := by
    have := (abs_le.mp (h.hessQuad x0 (η • ghat))).1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hηpos, mul_pow, ← hHdef] at this
    have key : L * (η ^ 2 * ‖ghat‖ ^ 2) = 1 / 8 * η * ‖ghat‖ ^ 2 := by
      rw [show L * (η ^ 2 * ‖ghat‖ ^ 2) = (L * η) * η * ‖ghat‖ ^ 2 by ring, hLη]
    linarith
  have h4 : gmodel H x0 g0 (f x0) xτ ≤ Phi b eig H x0 g0 (f x0) η θ xτ d' +
      9 / 50 * η * ‖gradModel H x0 g0 xτ‖ ^ 2 := gmodel_le_Phi x0 g0 (f x0) η θ hηpos hH xτ d'
  have h5 : ‖gradModel H x0 g0 xτ‖ ^ 2 ≤ 2 * ‖gradModel H x0 g0 y‖ ^ 2 + ‖ghat‖ ^ 2 / 32 := by
    have hs : gradModel H x0 g0 xτ = gradModel H x0 g0 y - H (η • ghat) := gradModel_shift x0 g0 H y _
    have hn : ‖H (η • ghat)‖ ≤ ‖ghat‖ / 8 := by
      calc ‖H (η • ghat)‖ ≤ ‖H‖ * ‖η • ghat‖ := H.le_opNorm _
        _ ≤ L * (η * ‖ghat‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hηpos]
            exact mul_le_mul_of_nonneg_right (h.hessNorm x0) (by positivity)
        _ = ‖ghat‖ / 8 := by rw [← mul_assoc, hLη]; ring
    rw [hs]
    have := norm_sub_le (gradModel H x0 g0 y) (H (η • ghat))
    have h6 : ‖gradModel H x0 g0 y - H (η • ghat)‖ ^ 2 ≤
        (‖gradModel H x0 g0 y‖ + ‖ghat‖ / 8) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (this.trans (by linarith)) 2
    nlinarith [sq_nonneg (‖gradModel H x0 g0 y‖ - ‖ghat‖ / 8), norm_nonneg ghat,
      norm_nonneg (gradModel H x0 g0 y)]
  have h7 : -(η * ⟪δ, ghat⟫) ≤ η / 64 * ‖ghat‖ ^ 2 + 16 * η * ‖δ‖ ^ 2 := by
    have := abs_real_inner_le_norm δ ghat
    have hy := LongTails.Proofs.StrongGrowthAgdLmi.young_coef (A := 1 / 64) (B := 16) (x := ‖ghat‖)
      (y := ‖δ‖) (by norm_num) (by norm_num)
    have : -⟪δ, ghat⟫ ≤ ‖δ‖ * ‖ghat‖ := by linarith [(abs_le.mp this).1]
    nlinarith [hηpos]
  have hδ : ⟪gradient f y, ghat⟫ = ⟪gradModel H x0 g0 y, ghat⟫ + ⟪δ, ghat⟫ := by
    simp only [δ]; rw [inner_sub_left]; ring
  have hL2 : L / 2 * (η ^ 2 * ‖ghat‖ ^ 2) = η / 16 * ‖ghat‖ ^ 2 := by
    have : L / 2 * (η ^ 2 * ‖ghat‖ ^ 2) = (L * η) * η / 2 * ‖ghat‖ ^ 2 := by ring
    rw [this, hLη]; ring
  rw [hδ] at h1
  rw [hL2] at h1
  nlinarith [h1, h2, h3, h3', h4, h5, h7, mul_nonneg hηpos.le (sq_nonneg ‖ghat‖),
    mul_nonneg hηpos.le (sq_nonneg ‖gradModel H x0 g0 y‖)]

end LongTails.Proofs.StrongGrowthAgdEpochEnd
