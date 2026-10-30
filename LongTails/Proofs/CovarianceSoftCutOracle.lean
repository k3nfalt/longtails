import LongTails.Setups.CovarianceBoundedConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.CovarianceSoftCutPotential

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CovarianceSoftCutOracle

open LongTails.Setups.CovarianceBoundedConvex

lemma norm_second_moment_of_directional {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) (V : ℝ) (hd : 0 < d)
    (hint : ∀ u, Integrable (fun ω => ⟪X ω, u⟫ ^ 2) μ)
    (hbound : ∀ u, (∫ ω, ⟪X ω, u⟫ ^ 2 ∂μ) ≤ V * ‖u‖ ^ 2 / d) :
    Integrable (fun ω => ‖X ω‖ ^ 2) μ ∧ (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ V := by
  have hi (i : Fin d) : Integrable (fun ω => (X ω i) ^ 2) μ := by
    simpa [EuclideanSpace.inner_single_right] using hint (EuclideanSpace.single i 1)
  have hb (i : Fin d) : (∫ ω, (X ω i) ^ 2 ∂μ) ≤ V / d := by
    simpa [EuclideanSpace.inner_single_right] using hbound (EuclideanSpace.single i 1)
  have heq : (fun ω => ‖X ω‖ ^ 2) = fun ω => ∑ i : Fin d, (X ω i) ^ 2 := by
    ext ω
    exact EuclideanSpace.real_norm_sq_eq (X ω)
  rw [heq]
  constructor
  · exact integrable_finsetSum _ (fun i _ => hi i)
  · rw [integral_finsetSum _ (fun i _ => hi i)]
    calc
      (∑ i : Fin d, ∫ ω, (X ω i) ^ 2 ∂μ) ≤ ∑ _i : Fin d, V / d :=
        Finset.sum_le_sum (fun i _ => hb i)
      _ = V := by
        have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
        simp [hd', mul_div_cancel₀]

lemma isCovarianceSubgradient_of_directional (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hmeas : Measurable (Function.uncurry g))
    (hint : ∀ x, Integrable (g x) p) (hunbiased : ∀ x, ∫ ω, g x ω ∂p = v x)
    (hsquare : ∀ x u, Integrable (fun ω => ⟪g x ω - v x, u⟫ ^ 2) p)
    (hsupport : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (hcov : ∀ x u, (∫ ω, ⟪g x ω - v x, u⟫ ^ 2 ∂p) ≤ q.σ ^ 2 * ‖u‖ ^ 2 / q.d) :
    IsCovarianceSubgradient q p f v g := by
  refine
    { measurable := hmeas
      integrable := hint
      unbiased := hunbiased
      variance_integrable := ?_
      support := hsupport
      covariance := hcov }
  · intro x
    exact (norm_second_moment_of_directional p (fun ω => g x ω - v x)
      (q.σ ^ 2) hd (hsquare x) (hcov x)).1

lemma measurable_mean_of_oracle (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g) :
    Measurable (v) := by
  have h : Measurable (fun x => ∫ ω, g x ω ∂p) :=
    hg.measurable.stronglyMeasurable.integral_prod_right.measurable
  simpa only [hg.unbiased] using h

lemma directional_square_integrable (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) : Integrable (fun ω => ⟪g x ω - v x, u⟫ ^ 2) p := by
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun ω => ⟪g x ω - v x, u⟫ ^ 2) := by fun_prop
  apply ((hg.variance_integrable x).mul_const (‖u‖ ^ 2)).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  apply Filter.Eventually.of_forall
  intro ω
  have h := (sq_le_sq₀ (abs_nonneg ⟪g x ω - v x, u⟫)
    (mul_nonneg (norm_nonneg _) (norm_nonneg u))).mpr
    (abs_real_inner_le_norm (g x ω - v x) u)
  simpa only [sq_abs, mul_pow] using h

lemma batch_directional_variance (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (b : ℕ) (hb : 0 < b) :
    Integrable (fun ξ : Fin b → q.Ω =>
      ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i) - v x, u⟫ ^ 2) (Measure.pi fun _ => p) ∧
    (∫ ξ : Fin b → q.Ω, ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i) - v x, u⟫ ^ 2
      ∂Measure.pi (fun _ => p)) ≤ q.σ ^ 2 * ‖u‖ ^ 2 / (q.d * b) := by
  let X := fun ω => ⟪g x ω - v x, u⟫
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hXm : Measurable X := by dsimp [X]; fun_prop
  have hXi : Integrable X p := by
    simpa only [X, innerSL_apply_apply, Pi.sub_apply, real_inner_comm] using
      (innerSL ℝ u).integrable_comp ((hg.integrable x).sub (integrable_const (v x)))
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) p := by
    simpa only [X, Real.norm_eq_abs, sq_abs] using directional_square_integrable q p f v g hg x u
  have hzero : (∫ ω, X ω ∂p) = 0 := by
    have h := (innerSL ℝ u).integral_comp_comm
      ((hg.integrable x).sub (integrable_const (v x)))
    simp only [innerSL_apply_apply, Pi.sub_apply, integral_sub (hg.integrable x) (integrable_const (v x)),
      hg.unbiased, integral_const, probReal_univ, one_smul, sub_self, inner_zero_right] at h
    simpa only [X, real_inner_comm] using h
  have hm := OracleTemplate.RobustGradient.finite_mean_second_moment hXm hXi hX2 hzero b hb
  have heq (ξ : Fin b → q.Ω) :
      ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i) - v x, u⟫ ^ 2 =
        ‖(1 / (b : ℝ)) • ∑ i, X (ξ i)‖ ^ 2 := by
    rw [OracleTemplate.RobustGradient.finite_mean_centered (v x) b hb ξ]
    simp only [real_inner_smul_left, sum_inner, X, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  simp_rw [heq]
  refine ⟨hm.1, ?_⟩
  rw [hm.2]
  have h := div_le_div_of_nonneg_right (hg.covariance x u) (by positivity : 0 ≤ (b : ℝ))
  simpa only [X, Real.norm_eq_abs, sq_abs, div_div] using h

lemma batch_shifted_hinge_integrable (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (b : ℕ) (hb : 0 < b) (α : ℝ) (hα : 0 < α)
    (hsignal : ⟪v x, u⟫ ≤ -(3 * α / 4)) :
    Integrable (fun ξ : Fin b → q.Ω =>
      max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), u⟫ + α / 2)) (Measure.pi fun _ => p) := by
  let noise := fun ξ : Fin b → q.Ω =>
    ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i) - v x, u⟫
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hn : Measurable noise := by dsimp [noise]; fun_prop
  have hv := batch_directional_variance q p f v g hg x u b hb
  have h := CovarianceSoftCutPotential.integrable_shiftedHinge
    (Measure.pi fun _ : Fin b => p) noise ⟪v x, u⟫ α hα hsignal hn hv.1
  have heq (ξ : Fin b → q.Ω) :
      ⟪v x, u⟫ + noise ξ + α / 2 =
        ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), u⟫ + α / 2 := by
    dsimp [noise]
    rw [inner_sub_left]
    ring
  simpa only [heq] using h

lemma batch_shifted_hinge_bound (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (b : ℕ) (hb : 0 < b) (α : ℝ) (hα : 0 < α)
    (hsignal : ⟪v x, u⟫ ≤ -(3 * α / 4)) :
    (∫ ξ : Fin b → q.Ω, max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), u⟫ + α / 2)
      ∂Measure.pi (fun _ => p)) ≤ q.σ ^ 2 * ‖u‖ ^ 2 / (q.d * b * α) := by
  let noise := fun ξ : Fin b → q.Ω =>
    ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i) - v x, u⟫
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hn : Measurable noise := by dsimp [noise]; fun_prop
  have hv := batch_directional_variance q p f v g hg x u b hb
  have h := CovarianceSoftCutPotential.integral_shiftedHinge_le_variance
    (Measure.pi fun _ : Fin b => p) noise ⟪v x, u⟫ α
    (q.σ ^ 2 * ‖u‖ ^ 2 / (q.d * b)) hα hsignal hn hv.1 hv.2
  have heq (ξ : Fin b → q.Ω) :
      ⟪v x, u⟫ + noise ξ + α / 2 =
        ⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), u⟫ + α / 2 := by
    dsimp [noise]
    rw [inner_sub_left]
    ring
  simpa only [heq, div_div] using h

lemma batch_scaled_hinge_bound (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (hu : ‖u‖ ≤ 4 * q.R) (b : ℕ) (hb : 0 < b)
    (α : ℝ) (hα : 0 < α) (hsignal : ⟪v x, u⟫ ≤ -(3 * α / 4))
    (hbatch : 1024 * q.σ ^ 2 * q.R ^ 2 ≤ (q.d : ℝ) * b * α ^ 2) :
    (2 / α) * (∫ ξ : Fin b → q.Ω,
      max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), u⟫ + α / 2)
      ∂Measure.pi (fun _ => p)) ≤ 1 / 32 := by
  have hv := batch_shifted_hinge_bound q p f v g hg x u b hb α hα hsignal
  have hd' : 0 < (q.d : ℝ) := by exact_mod_cast hd
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hu2 : ‖u‖ ^ 2 ≤ 16 * q.R ^ 2 := by nlinarith [norm_nonneg u]
  apply (mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 / α)).trans
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (by positivity : 0 < α * ((q.d : ℝ) * b * α))).2
  have hnoise := mul_le_mul_of_nonneg_left hu2 (sq_nonneg q.σ)
  nlinarith

lemma target_integrated_hinge_bound (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x : Space q) (μ : Measure (Space q)) [IsFiniteMeasure μ]
    (b : ℕ) (hb : 0 < b) (α : ℝ) (hα : 0 < α)
    (hu : ∀ᵐ y ∂μ, ‖y-x‖ ≤ 4 * q.R)
    (hsignal : ∀ᵐ y ∂μ, ⟪v x, y-x⟫ ≤ -(3 * α / 4))
    (hbatch : 1024 * q.σ ^ 2 * q.R ^ 2 ≤ (q.d : ℝ) * b * α ^ 2) :
    Integrable (fun ξ : Fin b → q.Ω => ∫ y,
      (2 / α) * max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), y-x⟫ + α / 2) ∂μ)
      (Measure.pi fun _ => p) ∧
    (∫ ξ : Fin b → q.Ω, ∫ y,
      (2 / α) * max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (ξ i), y-x⟫ + α / 2) ∂μ
      ∂Measure.pi (fun _ => p)) ≤ μ.real Set.univ / 32 := by
  let F : Space q × (Fin b → q.Ω) → ℝ := fun z =>
    (2 / α) * max 0 (⟪(1 / (b : ℝ)) • ∑ i, g x (z.2 i), z.1-x⟫ + α / 2)
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hnon (z) : 0 ≤ F z := mul_nonneg (by positivity) (le_max_left _ _)
  have hsection : ∀ᵐ y ∂μ, Integrable (fun ξ => F (y, ξ)) (Measure.pi fun _ => p) := by
    filter_upwards [hsignal] with y hy
    exact (batch_shifted_hinge_integrable q p f v g hg x (y-x) b hb α hα hy).const_mul (2 / α)
  have hmean : ∀ᵐ y ∂μ, (∫ ξ, F (y, ξ) ∂Measure.pi (fun _ => p)) ≤ 1 / 32 := by
    filter_upwards [hu, hsignal] with y hy hs
    dsimp only [F]
    rw [integral_const_mul]
    exact batch_scaled_hinge_bound q hd hR p f v g hg x (y-x) hy b hb α hα hs hbatch
  have hprod : Integrable F (μ.prod (Measure.pi fun _ : Fin b => p)) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).2
    refine ⟨hsection, ?_⟩
    apply (integrable_const (1 / 32 : ℝ)).mono_nonneg
      hF.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => integral_nonneg (fun ξ => norm_nonneg _)))
    filter_upwards [hmean] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnon _)] using hy
  refine ⟨hprod.integral_prod_right, ?_⟩
  have he := integral_integral_swap (f := fun y ξ => F (y, ξ)) hprod
  change (∫ ξ, ∫ y, F (y, ξ) ∂μ ∂Measure.pi (fun _ => p)) ≤ _
  rw [← he]
  have hm := integral_mono_ae hprod.integral_prod_left (integrable_const (1 / 32 : ℝ)) hmean
  simpa only [integral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using hm

end LongTails.Proofs.CovarianceSoftCutOracle
