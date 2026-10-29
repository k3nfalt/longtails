import LongTails.Proofs.PLMinimaxOracleGeometry
import LongTails.Proofs.PLMinimaxImplicit

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

lemma setup_primal_derivative_at_saddle {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (y : p.F)
    (hy : ∀ v, f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, v)) ≤
      f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) :
    ∃ Q : p.E →L[ℝ] p.E,
      HasFDerivAt (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) Q z ∧
      (∀ h, ‖primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L (z + h) -
        primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - Q h‖ ≤
        p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ)) * ‖h‖ ^ 2) ∧
      (∀ h v, regularizedHessian (fderiv ℝ (gradient f)
        (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) p.L v =
          WithLp.toLp 2 ((2 * p.L) • h, 0) → v.fst = Q h) ∧
      ∀ h, ∃ v, regularizedHessian (fderiv ℝ (gradient f)
        (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) p.L v =
          WithLp.toLp 2 ((2 * p.L) • h, 0) ∧ v.fst = Q h ∧
            ‖v‖ ≤ Real.sqrt (4 + 32 * p.L / p.μ) * ‖h‖ := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  let w : Space p := WithLp.toLp 2 (primal φ p.L z, y)
  let P : p.E →L[ℝ] Space p := (2 * p.L) •
    ((WithLp.prodContinuousLinearEquiv 2 ℝ p.E p.F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ p.E p.F))
  let K := regularizedHessian (fderiv ℝ (gradient f) w) p.L
  have hroot : regularizedGradient (gradient f) p.L z w = 0 := regularizedGradient_root H z y hy
  have hpos : 0 < p.L * p.μ := mul_pos H.hL H.hμ
  have hC : 0 ≤ 4 + 32 * p.L / p.μ := by have := H.hL; have := H.hμ; positivity
  have hker : ∀ v, K v = 0 → (WithLp.fstL 2 ℝ p.E p.F) v = 0 := by
    intro v hzero
    apply regularizedHessian_kernel _ H.hL _ (setup_hessian_bound hv hf w) _ v hzero
    · exact SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1 w
    · exact setup_hessian_dual_nonpos hv hf (primal φ p.L z) y hy
  have ht : ∀ s, ‖regularizedGradient (gradient f) p.L z (w + s) - K s‖ ≤ (p.ρ / 2) * ‖s‖ ^ 2 := by
    intro s
    have hh := regularizedGradient_taylor (fun a => (hf.2.1 a).hasFDerivAt)
      hf.2.2.2.1 p.L z w hroot s
    convert hh using 1
    ring
  have hsol : ∀ h, ∃ q, regularizedGradient (gradient f) p.L z q = P h ∧
      ‖q - w‖ ≤ Real.sqrt (4 + 32 * p.L / p.μ) * ‖h‖ := by
    intro h
    obtain ⟨q, hq, hd⟩ := regularized_roots_move H z y hy h
    refine ⟨q, ?_, hd⟩
    simpa [P, ← WithLp.toLp_smul] using hq
  have herr : ∀ h q, ‖(WithLp.fstL 2 ℝ p.E p.F) q - primal φ p.L (z + h)‖ ≤
      (1 / Real.sqrt (p.L * p.μ)) * ‖regularizedGradient (gradient f) p.L z q - P h‖ := by
    intro h q
    have hr := regularized_primal_error H (z + h) q.fst q.snd
    have hq : WithLp.toLp 2 (q.fst, q.snd) = q := (WithLp.equiv 2 (p.E × p.F)).left_inv q
    rw [hq] at hr
    have he : regularizedGradient (gradient f) p.L z q - P h =
        regularizedGradient (gradient f) p.L (z + h) q := by
      rw [regularizedGradient_center_shift (gradient f) p.L z h q]
      have hp : P h = WithLp.toLp 2 ((2 * p.L) • h, 0) := by simp [P, ← WithLp.toLp_smul]
      rw [hp, add_sub_cancel_right]
    rw [he]
    simpa [div_eq_mul_inv, mul_comm] using hr
  obtain ⟨Q, hQ, hb, hlinear⟩ := implicit_primal_derivative
    (π := WithLp.fstL 2 ℝ p.E p.F) (U := primal φ p.L)
    (B := 1 / Real.sqrt (p.L * p.μ)) (C := Real.sqrt (4 + 32 * p.L / p.μ))
    (ρ := p.ρ / 2) (z := z) (w := w)
    (by positivity) (Real.sqrt_nonneg _) (by linarith [hv.2.2.1]) rfl hker ht hsol herr
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · intro h
    have hh := hb h
    rw [Real.sq_sqrt hC] at hh
    convert hh using 1
    ring
  · intro h v hv
    apply hlinear h v
    simpa [P, ← WithLp.toLp_smul] using hv
  · intro h
    obtain ⟨v, hv', hn⟩ := bounded_linearized_lift
      (Real.sqrt_nonneg (4 + 32 * p.L / p.μ)) (show 0 ≤ p.ρ / 2 by linarith [hv.2.2.1]) ht hsol h
    refine ⟨v, ?_, hlinear h v hv', hn⟩
    simpa [P, ← WithLp.toLp_smul] using hv'

lemma setup_primal_derivative {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    ∃ Q : p.E →L[ℝ] p.E,
      HasFDerivAt (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) Q z ∧
      ∀ h, ‖primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L (z + h) -
        primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - Q h‖ ≤
        p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ)) * ‖h‖ ^ 2 := by
  have H := setup_hyp hv hf
  obtain ⟨y, hy⟩ := H.attain (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z)
  obtain ⟨Q, hQ, hb, _⟩ := setup_primal_derivative_at_saddle hv hf z y hy
  exact ⟨Q, hQ, hb⟩

lemma setup_inversePrimal_derivative {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (x : p.E) :
    ∃ R : p.E →L[ℝ] p.E,
      HasFDerivAt (inversePrimal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) R x ∧
      ∀ h, ‖inversePrimal (fun x y => f (WithLp.toLp 2 (x, y))) p.L (x + h) -
        inversePrimal (fun x y => f (WithLp.toLp 2 (x, y))) p.L x - R h‖ ≤
        (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
          (1 + 2 * p.L / p.μ) ^ 3 * ‖h‖ ^ 2 := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  obtain ⟨Q, _, hb⟩ := setup_primal_derivative hv hf (inversePrimal φ p.L x)
  have hA : 0 ≤ 1 + 2 * p.L / p.μ := by have := H.hL; have := H.hμ; positivity
  have hC : 0 ≤ p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ)) := by
    have := H.hL; have := H.hμ; have := hv.2.2.1; positivity
  obtain ⟨R, hR, hb, _⟩ := inverse_derivative_of_bounded_response
    (U := primal φ p.L) (V := inversePrimal φ p.L) (Q := Q)
    hA hC H.primal_inversePrimal
    (fun h => by simpa using H.inversePrimal_lipschitz (x + h) x) hb
  exact ⟨R, hR, hb⟩

lemma setup_value_twice_differentiable {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) :
    Differentiable ℝ (value f) ∧ Differentiable ℝ (gradient (value f)) := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  constructor
  · intro x
    obtain ⟨y, hy⟩ := H.attain x
    exact (H.value_hasGradient hy).differentiableAt
  · intro x
    obtain ⟨R, hR, _⟩ := setup_inversePrimal_derivative hv hf x
    have hd := (hR.sub (hasFDerivAt_id x)).const_smul (2 * p.L)
    have hn : 2 * p.L ≠ 0 := by have := H.hL; positivity
    have he : (fun x => (2 * p.L) • (inversePrimal φ p.L x - x)) = gradient (value f) := by
      funext x
      have hh : inversePrimal φ p.L x - x = (2 * p.L)⁻¹ • gradient (value f) x := by
        change (x + (2 * p.L)⁻¹ • gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue φ) x) - x =
          (2 * p.L)⁻¹ • gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue φ) x
        abel
      rw [hh, smul_smul, mul_inv_cancel₀ hn, one_smul]
    change HasFDerivAt (fun x => (2 * p.L) • (inversePrimal φ p.L x - x)) _ x at hd
    rw [he] at hd
    exact hd.differentiableAt

lemma setup_envelope_gradient {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z =
      (2 * p.L) • (z - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) := by
  have H := setup_hyp hv hf
  exact (weakEnvelope_hasGradient H.hL H.value_continuous H.value_weak z).gradient

lemma setup_envelope_quadratic_gradient {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    ∃ A : p.E →L[ℝ] p.E,
      HasFDerivAt (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) A z ∧
      ∀ h, ‖gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) (z + h) -
        gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z - A h‖ ≤
        (2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) * ‖h‖ ^ 2 := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  obtain ⟨Q, hQ, hb⟩ := setup_primal_derivative hv hf z
  let A : p.E →L[ℝ] p.E := (2 * p.L) • (ContinuousLinearMap.id ℝ p.E - Q)
  have he : gradient (envelope φ p.L) = fun z => (2 * p.L) • (z - primal φ p.L z) :=
    funext (setup_envelope_gradient hv hf)
  have hd := ((hasFDerivAt_id z).sub hQ).const_smul (2 * p.L)
  change HasFDerivAt (fun z => (2 * p.L) • (z - primal φ p.L z)) A z at hd
  rw [← he] at hd
  refine ⟨A, hd, fun h => ?_⟩
  have hh : gradient (envelope φ p.L) (z + h) - gradient (envelope φ p.L) z - A h =
      -(2 * p.L) • (primal φ p.L (z + h) - primal φ p.L z - Q h) := by
    rw [he]
    simp only [A, smul_apply, sub_apply, ContinuousLinearMap.id_apply, neg_smul,
      smul_sub, smul_add]
    abel
  change ‖gradient (envelope φ p.L) (z + h) - gradient (envelope φ p.L) z - A h‖ ≤ _
  rw [hh, norm_smul, norm_neg, Real.norm_of_nonneg (by linarith [hv.1, hv.2.1])]
  have hh' := mul_le_mul_of_nonneg_left (hb h) (show 0 ≤ 2 * p.L by linarith [hv.1, hv.2.1])
  simpa only [mul_assoc] using hh'

lemma setup_envelope_hessian_lipschitz {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z z' : p.E) :
    ‖fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z'‖ ≤
      6 * ((2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ)))) * ‖z - z'‖ := by
  have hC : 0 ≤ (2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) := by
    have H := setup_hyp hv hf
    have := H.hL; have := H.hμ; have := hv.2.2.1
    positivity
  apply derivative_lipschitz_of_quadratic_remainder
    (G := gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) hC _ z' z
  intro x h
  obtain ⟨A, hA, hb⟩ := setup_envelope_quadratic_gradient hv hf x
  rw [hA.fderiv]
  exact hb h

lemma setup_value_quadratic_gradient {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (x : p.E) :
    ∃ A : p.E →L[ℝ] p.E, HasFDerivAt (gradient (value f)) A x ∧
      ∀ h, ‖gradient (value f) (x + h) - gradient (value f) x - A h‖ ≤
        (2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
          (1 + 2 * p.L / p.μ) ^ 3 * ‖h‖ ^ 2 := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  obtain ⟨R, hR, hb⟩ := setup_inversePrimal_derivative hv hf x
  let A : p.E →L[ℝ] p.E := (2 * p.L) • (R - ContinuousLinearMap.id ℝ p.E)
  have hn : 2 * p.L ≠ 0 := by have H := setup_hyp hv hf; have := H.hL; positivity
  have he : gradient (value f) = fun x => (2 * p.L) • (inversePrimal φ p.L x - x) := by
    funext x
    have hh : inversePrimal φ p.L x - x = (2 * p.L)⁻¹ • gradient (value f) x := by
      change (x + (2 * p.L)⁻¹ • gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue φ) x) - x =
        (2 * p.L)⁻¹ • gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue φ) x
      abel
    rw [hh, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hd := (hR.sub (hasFDerivAt_id x)).const_smul (2 * p.L)
  change HasFDerivAt (fun x => (2 * p.L) • (inversePrimal φ p.L x - x)) A x at hd
  rw [← he] at hd
  refine ⟨A, hd, fun h => ?_⟩
  have hh : gradient (value f) (x + h) - gradient (value f) x - A h =
      (2 * p.L) • (inversePrimal φ p.L (x + h) - inversePrimal φ p.L x - R h) := by
    rw [he]
    simp only [A, smul_apply, sub_apply, ContinuousLinearMap.id_apply, smul_sub, smul_add]
    abel
  rw [hh, norm_smul, Real.norm_of_nonneg (by linarith [hv.1, hv.2.1])]
  have hh' := mul_le_mul_of_nonneg_left (hb h) (show 0 ≤ 2 * p.L by linarith [hv.1, hv.2.1])
  simpa only [mul_assoc] using hh'

lemma setup_value_hessian_lipschitz {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (x x' : p.E) :
    ‖fderiv ℝ (gradient (value f)) x - fderiv ℝ (gradient (value f)) x'‖ ≤
      6 * ((2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
        (1 + 2 * p.L / p.μ) ^ 3) * ‖x - x'‖ := by
  have hC : 0 ≤ (2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
      (1 + 2 * p.L / p.μ) ^ 3 := by
    have H := setup_hyp hv hf
    have := H.hL; have := H.hμ; have := hv.2.2.1
    positivity
  apply derivative_lipschitz_of_quadratic_remainder (G := gradient (value f)) hC _ x' x
  intro z h
  obtain ⟨A, hA, hb⟩ := setup_value_quadratic_gradient hv hf z
  rw [hA.fderiv]
  exact hb h

lemma setup_primal_derivative_nonneg {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z h : p.E) :
    0 ≤ ⟪fderiv ℝ (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z h, h⟫ := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  obtain ⟨y, hy⟩ := H.attain (primal φ p.L z)
  obtain ⟨Q, hQ, _, _, hlift⟩ := setup_primal_derivative_at_saddle hv hf z y hy
  obtain ⟨v, hKv, hp, _⟩ := hlift h
  have hs := SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1
    (WithLp.toLp 2 (primal φ p.L z, y))
  have he := regularizedHessian_inner_energy _ hs (setup_hessian_bound hv hf _)
    (setup_hessian_dual_nonpos hv hf (primal φ p.L z) y hy) v
  rw [hKv] at he
  simp only [WithLp.prod_inner_apply, real_inner_smul_left,
    inner_zero_left, add_zero] at he
  change p.L * ‖v.fst‖ ^ 2 ≤ 2 * p.L * ⟪h, v.fst⟫ at he
  rw [hp] at he
  have hn : 0 ≤ 2 * p.L * ⟪h, Q h⟫ :=
    (mul_nonneg H.hL.le (sq_nonneg ‖Q h‖)).trans he
  have hpos : 0 < 2 * p.L := by linarith [H.hL]
  have hh : 0 ≤ ⟪h, Q h⟫ := (mul_le_mul_iff_right₀ hpos).mp (by simpa using hn)
  rw [hQ.fderiv, real_inner_comm]
  exact hh

lemma setup_envelope_hessian_formula {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z =
      (2 * p.L) • (ContinuousLinearMap.id ℝ p.E -
        fderiv ℝ (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z) := by
  obtain ⟨Q, hQ, _⟩ := setup_primal_derivative hv hf z
  have hd := ((hasFDerivAt_id z).sub hQ).const_smul (2 * p.L)
  have he : gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) =
      fun z => (2 * p.L) • (z - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) :=
    funext (setup_envelope_gradient hv hf)
  rw [hQ.fderiv]
  apply HasFDerivAt.fderiv
  rw [he]
  exact hd

lemma setup_primal_derivative_symmetric {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z u v : p.E) :
    ⟪fderiv ℝ (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z u, v⟫ =
      ⟪u, fderiv ℝ (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z v⟫ := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  obtain ⟨y, hy⟩ := H.attain (primal φ p.L z)
  obtain ⟨Q, hQ, _, _, hlift⟩ := setup_primal_derivative_at_saddle hv hf z y hy
  obtain ⟨a, ha, hap, _⟩ := hlift u
  obtain ⟨b, hb, hbp, _⟩ := hlift v
  have hs := regularizedHessian_symmetric _
    (SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1
      (WithLp.toLp 2 (primal φ p.L z, y))) p.L a b
  rw [ha, hb] at hs
  simp only [WithLp.prod_inner_apply, real_inner_smul_left, inner_smul_right,
    inner_zero_left, inner_zero_right, add_zero] at hs
  change 2 * p.L * ⟪u, b.fst⟫ = 2 * p.L * ⟪a.fst, v⟫ at hs
  rw [hap, hbp] at hs
  rw [hQ.fderiv]
  have hp : 2 * p.L ≠ 0 := by have := H.hL; positivity
  exact (mul_left_cancel₀ hp hs).symm

lemma setup_value_hessian_formula {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (x : p.E) :
    fderiv ℝ (gradient (value f)) x = (2 * p.L) •
      (fderiv ℝ (inversePrimal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) x -
        ContinuousLinearMap.id ℝ p.E) := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  obtain ⟨R, hR, _⟩ := setup_inversePrimal_derivative hv hf x
  have H := setup_hyp hv hf
  have hn : 2 * p.L ≠ 0 := by have := H.hL; positivity
  have he : gradient (value f) = fun x => (2 * p.L) • (inversePrimal φ p.L x - x) := by
    funext x
    change gradient (value f) x = (2 * p.L) •
      (x + (2 * p.L)⁻¹ • gradient (value f) x - x)
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hR.fderiv]
  apply HasFDerivAt.fderiv
  rw [he]
  exact (hR.sub (hasFDerivAt_id x)).const_smul (2 * p.L)

lemma setup_primal_inverse_derivative {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z v : p.E) :
    fderiv ℝ (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z
      (fderiv ℝ (inversePrimal (fun x y => f (WithLp.toLp 2 (x, y))) p.L)
        (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) v) = v := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  have H := setup_hyp hv hf
  obtain ⟨Q, hQ, _⟩ := setup_primal_derivative hv hf z
  obtain ⟨R, hR, _⟩ := setup_inversePrimal_derivative hv hf (primal φ p.L z)
  have hQ' : HasFDerivAt (primal φ p.L) Q (inversePrimal φ p.L (primal φ p.L z)) := by
    rw [H.inversePrimal_primal]
    exact hQ
  have hc := hQ'.comp (primal φ p.L z) hR
  have he : primal φ p.L ∘ inversePrimal φ p.L = id := funext H.primal_inversePrimal
  rw [he] at hc
  have hh := hc.unique (hasFDerivAt_id (primal φ p.L z))
  rw [hQ.fderiv, hR.fderiv]
  exact congrArg (fun A : p.E →L[ℝ] p.E => A v) hh

lemma setup_curvature_transfer {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E)
    {η : ℝ} (hη : 0 ≤ η)
    (hc : ∀ v, -η * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z v, v⟫)
    (v : p.E) : -η * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (value f)) (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) v, v⟫ := by
  let φ : p.E → p.F → ℝ := fun x y => f (WithLp.toLp 2 (x, y))
  let Q := fderiv ℝ (primal φ p.L) z
  let R := fderiv ℝ (inversePrimal φ p.L) (primal φ p.L z)
  have H := setup_hyp hv hf
  have hupper : ∀ u, -η * ‖u‖ ^ 2 ≤ (2 * p.L) * (‖u‖ ^ 2 - ⟪Q u, u⟫) := by
    intro u
    have hh := hc u
    rw [setup_envelope_hessian_formula hv hf] at hh
    simpa only [smul_apply, sub_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
      inner_sub_left, real_inner_self_eq_norm_sq] using hh
  have hh := inverse_curvature_transfer Q R H.hL hη
    (setup_primal_derivative_symmetric hv hf z) (setup_primal_derivative_nonneg hv hf z)
    (setup_primal_inverse_derivative hv hf z) hupper v
  rw [setup_value_hessian_formula hv hf]
  simpa only [smul_apply, sub_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
    inner_sub_left, real_inner_self_eq_norm_sq] using hh

lemma setup_gradient_transfer {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    gradient (value f) (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) =
      gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z := by
  have H := setup_hyp hv hf
  have hh := H.primal_stationary z
  rw [setup_envelope_gradient hv hf]
  change gradient (value f) (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) +
    (2 * p.L) • (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - z) = 0 at hh
  rw [smul_sub] at hh ⊢
  simpa only [neg_sub] using eq_neg_of_add_eq_zero_left hh

lemma setup_approximate_gradient_transfer {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z x : p.E) :
    ‖gradient (value f) x‖ ≤
      ‖gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z‖ +
        (4 * p.L ^ 2 / p.μ) * ‖x - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z‖ := by
  have H := setup_hyp hv hf
  have hh := H.value_gradient_lipschitz x (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z)
  change ‖gradient (value f) x - gradient (value f)
    (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z)‖ ≤ _ at hh
  rw [setup_gradient_transfer hv hf] at hh
  have hn := norm_add_le (gradient (value f) x -
    gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z)
    (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z)
  rw [sub_add_cancel] at hn
  linarith

lemma setup_approximate_curvature_transfer {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z x : p.E)
    {η : ℝ} (hη : 0 ≤ η)
    (hc : ∀ v, -η * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z v, v⟫)
    (v : p.E) :
    -(η + 6 * ((2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
      (1 + 2 * p.L / p.μ) ^ 3) * ‖x - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z‖) * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (value f)) x v, v⟫ := by
  let u := primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z
  have hh := setup_curvature_transfer hv hf z hη hc v
  have hd := setup_value_hessian_lipschitz hv hf u x
  rw [norm_sub_rev u x] at hd
  have hn := (fderiv ℝ (gradient (value f)) u - fderiv ℝ (gradient (value f)) x).le_opNorm v
  have hi := real_inner_le_norm
    ((fderiv ℝ (gradient (value f)) u - fderiv ℝ (gradient (value f)) x) v) v
  have hb := mul_le_mul_of_nonneg_right hd (norm_nonneg v)
  have hb' := mul_le_mul_of_nonneg_right (hn.trans hb) (norm_nonneg v)
  simp only [sub_apply, inner_sub_left] at hi hb'
  change -η * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient (value f)) u v, v⟫ at hh
  change -(η + _ * ‖x - u‖) * ‖v‖ ^ 2 ≤ _
  nlinarith

end OracleTemplate.PLMinimax
