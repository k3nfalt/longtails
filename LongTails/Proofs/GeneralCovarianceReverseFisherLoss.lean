import LongTails.Setups.GeneralCovarianceReverseFisher
import LongTails.Proofs.GeneralCovarianceReverseFisherBilinear

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherLoss

open LongTails.Setups.GeneralCovarianceReverseFisher
open LongTails.Proofs.GeneralCovarianceReverseFisherDensity
open LongTails.Proofs.GeneralCovarianceReverseFisherScore
open LongTails.Proofs.GeneralCovarianceReverseFisherDerivative
open LongTails.Proofs.GeneralCovarianceReverseFisherParts
open LongTails.Proofs.GeneralCovarianceReverseFisherTail
open LongTails.Proofs.GeneralCovarianceReverseFisherBilinear

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

noncomputable def normalizer (A : V ≃L[ℝ] V) : ℝ :=
  |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| * (2 * Real.pi) ^ (-(Module.finrank ℝ V / 2 : ℝ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma normalizer_pos (A : V ≃L[ℝ] V) : 0 < normalizer A := by
  unfold normalizer
  have := det_ne_zero A
  have h2 : 0 < 2 * Real.pi := by positivity
  positivity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma gaussDensity_eq (A : V ≃L[ℝ] V) {k : ℕ} (c : Fin k → V) (i : Fin k) (x : V) :
    gaussDensity A (c i) x = normalizer A * weight A c x i := by
  unfold gaussDensity stdDensity normalizer weight
  ring

lemma normalizer_mul_integral_weight (A : V ≃L[ℝ] V) {k : ℕ} (c : Fin k → V) (i : Fin k) :
    normalizer A * ∫ x, weight A c x i = 1 := by
  have h := integral_affine A (c i) (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  rw [← integral_const_mul]
  simp_rw [← gaussDensity_eq]
  exact h.symm

lemma integral_affine_weight (A : V ≃L[ℝ] V) {k : ℕ} (c : Fin k → V) (i : Fin k) (F : V → ℝ) :
    ∫ z, F (c i + A z) ∂ProbabilityTheory.stdGaussian V =
      normalizer A * ∫ x, weight A c x i * F x := by
  rw [integral_affine, ← integral_const_mul]
  congr 1
  ext x
  rw [gaussDensity_eq, smul_eq_mul]
  ring

lemma tail_x (A : V ≃L[ℝ] V) {k : ℕ} [NeZero k] (c : Fin k → V) (i : Fin k) :
    normalizer A * ∫ x, weight A c x i * ‖A.symm (c i - posteriorMean A c x)‖ ^ 2 ≤
      8 * Real.log k := by
  rw [← integral_affine_weight A c i (fun x => ‖A.symm (c i - posteriorMean A c x)‖ ^ 2)]
  set c' : Fin k → V := fun j => A.symm (c j - c i) with hc'
  have hc0 : c' i = 0 := by simp [hc']
  have hw : ∀ z j, weight A c (c i + A z) j = softWeight c' z j := by
    intro z j
    simp only [weight, softWeight, hc']
    congr 3
    rw [show c i + A z - c j = A z - (c j - c i) by abel, map_sub,
      ContinuousLinearEquiv.symm_apply_apply]
  have hr : ∀ z j, resp A c (c i + A z) j = softResp c' z j := by
    intro z j
    simp only [resp, total, softResp, hw]
  have hm : ∀ z, ‖A.symm (c i - posteriorMean A c (c i + A z))‖ ^ 2 =
      ‖∑ j, softResp c' z j • c' j‖ ^ 2 := by
    intro z
    have e : c i - posteriorMean A c (c i + A z) =
        -∑ j, resp A c (c i + A z) j • (c j - c i) := by
      unfold posteriorMean
      simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_resp, one_smul]
      abel
    rw [e, map_neg, norm_neg, map_sum]
    simp_rw [map_smul, hr]
    rfl
  simp_rw [hm]
  exact tail_bound c' i hc0

section Setup

variable {p : Params}

instance (p : Params) : NeZero (p.components : ℕ) := ⟨p.components.ne_zero⟩

lemma score_sq (M : Model p) (θ : Means p) (y : Space p) :
    ‖gradient (logMixture M.covarianceRoot (fun i => θ i)) y -
      gradient (logMixture M.covarianceRoot (fun _ : Fin 1 => M.target)) y‖ ^ 2 =
      ‖precision M.covarianceRoot (center M.covarianceRoot M.target θ y)‖ ^ 2 := by
  have h := score_difference M.covarianceRoot (fun i => θ i) M.target y
  unfold logMixture
  rw [h]
  rfl

lemma loss_eq (M : Model p) (θ : Means p) :
    loss M θ = normalizer M.covarianceRoot / p.components *
      ∫ x, integrand M.covarianceRoot M.target θ x := by
  unfold loss
  simp_rw [score_sq]
  set A := M.covarianceRoot
  set t := M.target
  have hs := spread_nonneg t θ
  have hF : ∀ ℓ, Integrable (fun x => weight A (fun i => θ i) x ℓ *
      ‖precision A (center A t θ x)‖ ^ 2) := fun ℓ =>
    integrable_weight_mul A _ ℓ
      (((precision A).continuous.comp (continuous_center A t θ)).norm.pow 2)
      (C := (‖precision A‖ * spread t θ) ^ 2)
      (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (norm_center_le A t θ x) (norm_nonneg _))) 2)
  have h1 : ∀ ℓ, ∫ z, ‖precision A (center A t θ (θ ℓ + A z))‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (Space p) =
      normalizer A * ∫ x, weight A (fun i => θ i) x ℓ * ‖precision A (center A t θ x)‖ ^ 2 :=
    fun ℓ => integral_affine_weight A (fun i => θ i) ℓ
      (fun x => ‖precision A (center A t θ x)‖ ^ 2)
  simp_rw [h1]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun ℓ _ => hF ℓ)]
  simp_rw [← Finset.sum_mul, integrand_eq]
  unfold total
  ring

lemma hasFDerivAt_loss (M : Model p) (θ : Means p) :
    HasFDerivAt (loss M) ((normalizer M.covarianceRoot / p.components) •
      ∫ x, integrandDeriv M.covarianceRoot M.target θ x) θ := by
  have hf : loss M = fun η => normalizer M.covarianceRoot / p.components *
      ∫ x, integrand M.covarianceRoot M.target η x := funext (loss_eq M)
  rw [hf]
  exact (hasFDerivAt_integral_integrand M.covarianceRoot M.target θ).const_mul _

lemma inner_gradient_loss (M : Model p) (θ h : Means p) :
    ⟪gradient (loss M) θ, h⟫ = normalizer M.covarianceRoot / p.components *
      ∫ x, pairing M.covarianceRoot M.target θ x h := by
  rw [(hasFDerivAt_loss M θ).hasGradientAt.gradient, InnerProductSpace.toDual_symm_apply,
    smul_apply, smul_eq_mul, integral_integrandDeriv_apply]

end Setup

end LongTails.Proofs.GeneralCovarianceReverseFisherLoss
