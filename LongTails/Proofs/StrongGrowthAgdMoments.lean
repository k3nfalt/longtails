import LongTails.Proofs.StrongGrowthAgdProcess
import LongTails.Proofs.FiniteVarianceBatch

namespace LongTails.Proofs.StrongGrowthAgdMoments

open MeasureTheory ProbabilityTheory LongTails.Algorithms.StrongGrowthRestartedAgd
  LongTails.Proofs.StrongGrowthAgdProcess OracleTemplate.RobustGradient OracleTemplate.LightTail
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {g : E → Ω → E} {gf : E → E} {κ : ℝ}

structure OracleHyp (g : E → Ω → E) (gf : E → E) (p : Measure Ω) (κ : ℝ) : Prop where
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gf x
  int2 : ∀ x, Integrable (fun ω => ‖g x ω - gf x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gf x‖ ^ 2 ∂p ≤ (κ - 1) * ‖gf x‖ ^ 2

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma OracleHyp.meas_right (h : OracleHyp g gf p κ) (q : E) : Measurable (g q) :=
  h.meas.comp (measurable_const.prodMk measurable_id)

variable (cfg : Config)

lemma bmean_measurable_joint {α : Type*} [MeasurableSpace α] (hg : Measurable (Function.uncurry g))
    {q : α → E} (hq : Measurable q) :
    Measurable (fun z : α × (Fin cfg.b → Ω) => bmean cfg g (q z.1) z.2) := by
  unfold bmean
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact hg.comp ((hq.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma bmean_measurable (hg : Measurable (Function.uncurry g)) (q : E) :
    Measurable (bmean cfg g q) := by
  unfold bmean
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact hg.comp (measurable_const.prodMk (measurable_pi_apply i))

variable (hb : 0 < cfg.b)
include hb

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma bmean_integrable (h : OracleHyp g gf p κ) (q : E) :
    Integrable (bmean cfg g q) (Measure.pi fun _ : Fin cfg.b => p) := by
  unfold bmean
  exact (finite_mean_integral (P := p) (h.int q) cfg.b hb).1

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma integral_bmean (h : OracleHyp g gf p κ) (q : E) :
    ∫ ω, bmean cfg g q ω ∂(Measure.pi fun _ : Fin cfg.b => p) = gf q := by
  unfold bmean
  exact ((finite_mean_integral (P := p) (h.int q) cfg.b hb).2).trans (h.mean q)

lemma bmean_err_integrable (h : OracleHyp g gf p κ) (q : E) :
    Integrable (fun ω => ‖bmean cfg g q ω - gf q‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := by
  unfold bmean
  exact (finite_mean_variance (P := p) (h.meas_right q) (h.int q) (gf q) (h.int2 q) (h.mean q)
    cfg.b hb).1

lemma integral_bmean_err (h : OracleHyp g gf p κ) (q : E) :
    ∫ ω, ‖bmean cfg g q ω - gf q‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (κ - 1) / cfg.b * ‖gf q‖ ^ 2 := by
  have := (finite_mean_variance (P := p) (h.meas_right q) (h.int q) (gf q) (h.int2 q) (h.mean q)
    cfg.b hb).2
  unfold bmean
  rw [this, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (h.var q) (Nat.cast_nonneg _)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma bmean_err_integrable' (h : OracleHyp g gf p κ) (q : E) :
    Integrable (fun ω => bmean cfg g q ω - gf q) (Measure.pi fun _ : Fin cfg.b => p) :=
  (bmean_integrable cfg hb h q).sub (integrable_const _)

omit [BorelSpace E] in
lemma integral_bmean_err_vec (h : OracleHyp g gf p κ) (q : E) :
    ∫ ω, (bmean cfg g q ω - gf q) ∂(Measure.pi fun _ : Fin cfg.b => p) = 0 := by
  rw [integral_sub (bmean_integrable cfg hb h q) (integrable_const _), integral_bmean cfg hb h q,
    integral_const]
  simp

omit [BorelSpace E] in
lemma integral_inner_bmean_err (h : OracleHyp g gf p κ) (q v : E) :
    ∫ ω, ⟪v, bmean cfg g q ω - gf q⟫ ∂(Measure.pi fun _ : Fin cfg.b => p) = 0 := by
  rw [integral_inner (bmean_err_integrable' cfg hb h q) v, integral_bmean_err_vec cfg hb h q,
    inner_zero_right]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] hb in
lemma bmean_sq_eq (q : E) (ω : Fin cfg.b → Ω) :
    ‖bmean cfg g q ω‖ ^ 2 =
      ‖bmean cfg g q ω - gf q‖ ^ 2 + 2 * ⟪gf q, bmean cfg g q ω - gf q⟫ + ‖gf q‖ ^ 2 := by
  have := norm_add_sq_real (bmean cfg g q ω - gf q) (gf q)
  rw [sub_add_cancel] at this
  rw [this, real_inner_comm]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma bmean_inner_integrable (h : OracleHyp g gf p κ) (q : E) :
    Integrable (fun ω => 2 * ⟪gf q, bmean cfg g q ω - gf q⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
  ((bmean_err_integrable' cfg hb h q).const_inner (𝕜 := ℝ) (gf q)).const_mul 2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] hb in
lemma bmean_sq_fun_eq (q : E) : (fun ω : Fin cfg.b → Ω => ‖bmean cfg g q ω‖ ^ 2) =
    fun ω => ‖bmean cfg g q ω - gf q‖ ^ 2 + 2 * ⟪gf q, bmean cfg g q ω - gf q⟫ + ‖gf q‖ ^ 2 :=
  funext (bmean_sq_eq cfg (gf := gf) q)

lemma bmean_sq_integrable (h : OracleHyp g gf p κ) (q : E) :
    Integrable (fun ω => ‖bmean cfg g q ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := by
  rw [bmean_sq_fun_eq cfg (gf := gf) q]
  have hAB : Integrable (fun ω => ‖bmean cfg g q ω - gf q‖ ^ 2 + 2 * ⟪gf q, bmean cfg g q ω - gf q⟫)
      (Measure.pi fun _ : Fin cfg.b => p) :=
    (bmean_err_integrable cfg hb h q).add (bmean_inner_integrable cfg hb h q)
  exact hAB.add (integrable_const _)

lemma integral_bmean_sq (h : OracleHyp g gf p κ) (q : E) :
    ∫ ω, ‖bmean cfg g q ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) =
      (∫ ω, ‖bmean cfg g q ω - gf q‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p)) + ‖gf q‖ ^ 2 := by
  rw [bmean_sq_fun_eq cfg (gf := gf) q]
  have hA := bmean_err_integrable cfg hb h q
  have hB := bmean_inner_integrable cfg hb h q
  have hAB : Integrable (fun ω => ‖bmean cfg g q ω - gf q‖ ^ 2 + 2 * ⟪gf q, bmean cfg g q ω - gf q⟫)
      (Measure.pi fun _ : Fin cfg.b => p) := hA.add hB
  rw [integral_add hAB (integrable_const _), integral_add hA hB]
  have hzero : ∫ ω, 2 * ⟪gf q, bmean cfg g q ω - gf q⟫ ∂(Measure.pi fun _ : Fin cfg.b => p) = 0 := by
    rw [integral_const_mul, integral_inner_bmean_err cfg hb h q (gf q), mul_zero]
  rw [hzero, add_zero, integral_const]
  simp

lemma integral_bmean_sq_le (h : OracleHyp g gf p κ) (q : E) :
    ∫ ω, ‖bmean cfg g q ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (1 + (κ - 1) / cfg.b) * ‖gf q‖ ^ 2 := by
  rw [integral_bmean_sq cfg hb h q]
  have := integral_bmean_err cfg hb h q
  linarith

end LongTails.Proofs.StrongGrowthAgdMoments
