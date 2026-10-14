import LongTails.Proofs.FiniteVarianceBatch
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticConvexQuadratic

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] [SecondCountableTopology E]
    [CompleteSpace F] [SecondCountableTopology F] [IsProbabilityMeasure P] in
lemma transformed_noise_second_moment {X : Ω → E} (hX : Measurable X)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (B : E →L[ℝ] F)
    {C v : ℝ} (hC : 0 ≤ C) (hB : ∀ x, ‖B x‖ ≤ C * ‖x‖)
    (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖B (X ω)‖ ^ 2) P ∧
      (∫ ω, ‖B (X ω)‖ ^ 2 ∂P) ≤ C ^ 2 * v := by
  have hpoint (ω : Ω) : ‖B (X ω)‖ ^ 2 ≤ C ^ 2 * ‖X ω‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hB (X ω))
    simpa only [mul_pow] using h
  have hi : Integrable (fun ω => ‖B (X ω)‖ ^ 2) P :=
    (hX2.const_mul (C ^ 2)).mono'
      (((B.continuous.measurable.comp hX).norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖B (X ω)‖)] using hpoint ω))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, C ^ 2 * ‖X ω‖ ^ 2 ∂P := integral_mono hi (hX2.const_mul _) hpoint
    _ = C ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂P := integral_const_mul _ _
    _ ≤ C ^ 2 * v := mul_le_mul_of_nonneg_left hv (sq_nonneg C)

omit [SecondCountableTopology E] [SecondCountableTopology F] in
lemma centered_affine_second_moment {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hzero : (∫ ω, X ω ∂P) = 0) (B : E →L[ℝ] F) (y : F) :
    Integrable (fun ω => ‖y + B (X ω)‖ ^ 2) P ∧
      (∫ ω, ‖y + B (X ω)‖ ^ 2 ∂P) =
        ‖y‖ ^ 2 + ∫ ω, ‖B (X ω)‖ ^ 2 ∂P := by
  have hBi := B.integrable_comp hXi
  have hB2 := (transformed_noise_second_moment hX hX2 B (norm_nonneg B)
    (fun x => B.le_opNorm x) (le_refl _)).1
  have hinner : Integrable (fun ω => ⟪y, B (X ω)⟫) P := hBi.const_inner y
  have heq : (fun ω => ‖y + B (X ω)‖ ^ 2) =
      fun ω => (‖y‖ ^ 2 + 2 * ⟪y, B (X ω)⟫) + ‖B (X ω)‖ ^ 2 := by
    funext ω
    rw [norm_add_sq_real]
  have hsum : Integrable (fun ω => ‖y‖ ^ 2 + 2 * ⟪y, B (X ω)⟫) P :=
    (integrable_const _).add (hinner.const_mul 2)
  rw [heq]
  refine ⟨hsum.add hB2, ?_⟩
  rw [integral_add hsum hB2,
    integral_add (integrable_const (‖y‖ ^ 2)) (hinner.const_mul 2), integral_const_mul,
    integral_inner hBi, B.integral_comp_comm hXi, hzero]
  simp

omit [CompleteSpace E] [SecondCountableTopology E]
    [CompleteSpace F] [SecondCountableTopology F] [IsProbabilityMeasure P] in
lemma transformed_noise_squared_bound {X : Ω → E} (hX : Measurable X)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (B : E →L[ℝ] F)
    {C v : ℝ} (hC : 0 ≤ C) (hB : ∀ x, ‖B x‖ ^ 2 ≤ C * ‖x‖ ^ 2)
    (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖B (X ω)‖ ^ 2) P ∧
      (∫ ω, ‖B (X ω)‖ ^ 2 ∂P) ≤ C * v := by
  have hb (x : E) : ‖B x‖ ≤ Real.sqrt C * ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hC] using hB x
  simpa only [Real.sq_sqrt hC] using
    transformed_noise_second_moment hX hX2 B (Real.sqrt_nonneg C) hb hv

lemma nonnegative_product_control {Ξ Ψ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ψ]
    {μ : Measure Ξ} {ν : Measure Ψ} [SFinite μ] [SFinite ν]
    {f : Ξ × Ψ → ℝ} {g : Ξ → ℝ}
    (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hi : ∀ x, Integrable (fun y => f (x, y)) ν)
    (hg : Integrable g μ) (hb : ∀ x, (∫ y, f (x, y) ∂ν) ≤ g x) :
    Integrable f (μ.prod ν) ∧ (∫ z, f z ∂μ.prod ν) ≤ ∫ x, g x ∂μ := by
  have hn (x : Ξ) : (∫ y, ‖f (x, y)‖ ∂ν) = ∫ y, f (x, y) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hf0 (x, y)))
  have ho : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
    apply hg.mono' hf.aestronglyMeasurable.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), hn]
    exact hb x
  have hfi := (integrable_prod_iff hf.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall hi, ho⟩
  refine ⟨hfi, ?_⟩
  rw [integral_prod _ hfi]
  exact integral_mono hfi.integral_prod_left hg hb

end OracleTemplate.StochasticConvexQuadratic
