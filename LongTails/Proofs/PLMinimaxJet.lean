import LongTails.Proofs.PLMinimaxRegularity

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma envelopeHessianApprox_apply (L : ℝ) (K : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    (t : ℝ) (h : E) :
    envelopeHessianApprox L K t h =
      (2 * L) • (h - (tikhonovResponse K t (WithLp.toLp 2 ((2 * L) • h, 0))).fst) := by
  have he : WithLp.toLp 2 ((2 * L) • h, (0 : F)) = (2 * L) • WithLp.toLp 2 (h, 0) := by
    rw [← WithLp.toLp_smul]
    simp
  rw [he, map_smul, WithLp.smul_fst]
  simp only [envelopeHessianApprox, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, WithLp.fstL_apply, primalInjection,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.inl_apply, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

lemma envelopeHessianApprox_symmetric [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : ℝ) (K : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) {t : ℝ} (ht : 0 < t)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) (u v : E) :
    ⟪envelopeHessianApprox L K t u, v⟫ = ⟪u, envelopeHessianApprox L K t v⟫ := by
  have hh := tikhonovResponse_symmetric K hs ht (WithLp.toLp 2 (u, 0)) (WithLp.toLp 2 (v, 0))
  have hh' : ⟪(tikhonovResponse K t (WithLp.toLp 2 (u, 0))).fst, v⟫ =
      ⟪u, (tikhonovResponse K t (WithLp.toLp 2 (v, 0))).fst⟫ := by
    simpa [WithLp.prod_inner_apply] using hh
  simp only [envelopeHessianApprox, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, WithLp.fstL_apply, primalInjection,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.inl_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right]
  rw [hh']

lemma envelopeHessianApprox_lift_bias [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖)
    (hdual : ∀ b : F, ⟪H (WithLp.toLp 2 (0, b)), WithLp.toLp 2 (0, b)⟫ ≤ 0)
    (h : E) (v : WithLp 2 (E × F))
    (hv : regularizedHessian H L v = WithLp.toLp 2 ((2 * L) • h, 0)) :
    ‖envelopeHessianApprox L (regularizedHessian H L) t h - (2 * L) • (h - v.fst)‖ ^ 4 ≤
      4 * L ^ 2 * t * ‖v‖ ^ 4 := by
  have hb := regularizedResponse_primal_bias H hL ht hs hbound hdual v
  rw [hv] at hb
  have he : envelopeHessianApprox L (regularizedHessian H L) t h - (2 * L) • (h - v.fst) =
      -(2 * L) • (tikhonovResponse (regularizedHessian H L) t
        (WithLp.toLp 2 ((2 * L) • h, 0)) - v).fst := by
    rw [envelopeHessianApprox_apply]
    simp only [WithLp.sub_fst, neg_smul, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (show 0 < 2 * L by positivity)]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * L ^ 2 by positivity)
  nlinarith

lemma setup_envelopeHessianApprox_bias {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (y : p.F)
    (hy : ∀ v, f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, v)) ≤
      f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)))
    {t : ℝ} (ht : 0 < t) (h : p.E) :
    ‖envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f)
      (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) p.L) t h -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z h‖ ^ 4 ≤
      4 * p.L ^ 2 * t * (4 + 32 * p.L / p.μ) ^ 2 * ‖h‖ ^ 4 := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  let w : Space p := WithLp.toLp 2 (primal φ p.L z, y)
  have H := setup_hyp hv hf
  obtain ⟨Q, hQ, _, _, hlift⟩ := setup_primal_derivative_at_saddle hv hf z y hy
  obtain ⟨v, hKv, hp, hn⟩ := hlift h
  have hs := SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1 w
  have hb := envelopeHessianApprox_lift_bias (fderiv ℝ (gradient f) w) H.hL ht hs
    (setup_hessian_bound hv hf w) (setup_hessian_dual_nonpos hv hf (primal φ p.L z) y hy) h v hKv
  rw [hp] at hb
  rw [setup_envelope_hessian_formula hv hf, hQ.fderiv]
  simp only [smul_apply, sub_apply, ContinuousLinearMap.id_apply]
  have hpow := pow_le_pow_left₀ (norm_nonneg v) hn 4
  have hc : 0 ≤ 4 + 32 * p.L / p.μ := by have := H.hL; have := H.hμ; positivity
  have he : (Real.sqrt (4 + 32 * p.L / p.μ) * ‖h‖) ^ 4 =
      (4 + 32 * p.L / p.μ) ^ 2 * ‖h‖ ^ 4 := by
    rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hc]
  rw [he] at hpow
  have hscaled := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 * p.L ^ 2 * t by positivity)
  exact hb.trans (by nlinarith [hscaled])

lemma norm_le_of_fourth_power (A : E →L[ℝ] F) {η : ℝ} (hη : 0 ≤ η)
    (hA : ∀ h, ‖A h‖ ^ 4 ≤ η ^ 4 * ‖h‖ ^ 4) : ‖A‖ ≤ η := by
  apply ContinuousLinearMap.opNorm_le_bound A hη
  intro h
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hη (norm_nonneg h)) (by decide : 4 ≠ 0)).mp
  simpa only [mul_pow] using hA h

lemma setup_envelopeHessianApprox_norm {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (y : p.F)
    (hy : ∀ v, f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, v)) ≤
      f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)))
    {t η : ℝ} (ht : 0 < t) (hη : 0 ≤ η)
    (hsmall : 4 * p.L ^ 2 * t * (4 + 32 * p.L / p.μ) ^ 2 ≤ η ^ 4) :
    ‖envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f)
      (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) p.L) t -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z‖ ≤ η := by
  apply norm_le_of_fourth_power _ hη
  intro h
  exact (setup_envelopeHessianApprox_bias hv hf z y hy ht h).trans
    (mul_le_mul_of_nonneg_right hsmall (by positivity))

lemma envelopeHessianApprox_difference [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : ℝ) (A B : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) {t : ℝ} (ht : 0 < t)
    (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hB : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) :
    ‖envelopeHessianApprox L A t - envelopeHessianApprox L B t‖ ≤
      4 * L ^ 2 * (t⁻¹ + ‖A‖ * t⁻¹ * (‖A‖ + ‖B‖) * t⁻¹) * ‖B - A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  let v : WithLp 2 (E × F) := WithLp.toLp 2 (h, 0)
  have he : (envelopeHessianApprox L A t - envelopeHessianApprox L B t) h =
      -(4 * L ^ 2) • (tikhonovResponse A t v - tikhonovResponse B t v).fst := by
    simp only [envelopeHessianApprox, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, WithLp.fstL_apply, primalInjection,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      ContinuousLinearMap.inl_apply, WithLp.sub_fst, neg_smul, smul_sub, v]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (show 0 ≤ 4 * L ^ 2 by positivity)]
  have hn := WithLp.norm_fst_le E (tikhonovResponse A t v - tikhonovResponse B t v)
  have hd := tikhonovResponse_difference_bound A B ht hA hB v
  have hv : ‖v‖ = ‖h‖ := by simp [v, WithLp.norm_toLp_fst]
  rw [hv] at hd
  have hh := mul_le_mul_of_nonneg_left (hn.trans hd) (show 0 ≤ 4 * L ^ 2 by positivity)
  convert hh using 1
  ring

lemma setup_envelopeHessianApprox_difference {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (w w' : Space p)
    {t : ℝ} (ht : 0 < t) :
    ‖envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L) t -
      envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w') p.L) t‖ ≤
      4 * p.L ^ 2 * (t⁻¹ + 18 * p.L ^ 2 * t⁻¹ ^ 2) * p.ρ * ‖w - w'‖ := by
  have H := setup_hyp hv hf
  let A := regularizedHessian (fderiv ℝ (gradient f) w) p.L
  let B := regularizedHessian (fderiv ℝ (gradient f) w') p.L
  have ha : ‖A‖ ≤ 3 * p.L := regularizedHessian_norm _ H.hL.le (setup_hessian_bound hv hf w)
  have hb : ‖B‖ ≤ 3 * p.L := regularizedHessian_norm _ H.hL.le (setup_hessian_bound hv hf w')
  have hs : ∀ q : Space p, ∀ u v, ⟪regularizedHessian (fderiv ℝ (gradient f) q) p.L u, v⟫ =
      ⟪u, regularizedHessian (fderiv ℝ (gradient f) q) p.L v⟫ := fun q =>
    regularizedHessian_symmetric _
      (SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1 q) p.L
  have hd := envelopeHessianApprox_difference p.L A B ht (hs w) (hs w')
  have hab : ‖B - A‖ ≤ p.ρ * ‖w - w'‖ := by
    change ‖regularizedHessian _ p.L - regularizedHessian _ p.L‖ ≤ _
    rw [regularizedHessian_difference, norm_sub_rev]
    exact hf.2.2.2.1 w' w
  have hc : t⁻¹ + ‖A‖ * t⁻¹ * (‖A‖ + ‖B‖) * t⁻¹ ≤
      t⁻¹ + 18 * p.L ^ 2 * t⁻¹ ^ 2 := by
    calc
      _ ≤ t⁻¹ + (3 * p.L) * t⁻¹ * (3 * p.L + 3 * p.L) * t⁻¹ := by
        have := H.hL
        gcongr
      _ = _ := by ring
  apply hd.trans
  calc
    _ ≤ 4 * p.L ^ 2 * (t⁻¹ + 18 * p.L ^ 2 * t⁻¹ ^ 2) * (p.ρ * ‖w - w'‖) := by
      gcongr
    _ = _ := by ring

end OracleTemplate.PLMinimax
