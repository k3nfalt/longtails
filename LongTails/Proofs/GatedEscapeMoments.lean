import LongTails.Proofs.GatedEscapeProcess
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.NormSubGaussianBatch
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace LongTails.Proofs.GatedEscapeMoments

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess OracleTemplate.RobustGradient
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {g : E → Ω → E} {gf : E → E} {σ : ℝ}

structure Noise (g : E → Ω → E) (gf : E → E) (p : Measure Ω) (σ : ℝ) : Prop where
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gf x
  int2 : ∀ x, Integrable (fun ω => ‖g x ω - gf x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gf x‖ ^ 2 ∂p ≤ σ ^ 2

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma Noise.meas_right (h : Noise g gf p σ) (q : E) : Measurable (g q) :=
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
lemma bmean_integrable (h : Noise g gf p σ) (q : E) :
    Integrable (bmean cfg g q) (Measure.pi fun _ : Fin cfg.b => p) := by
  unfold bmean
  exact (OracleTemplate.LightTail.finite_mean_integral (P := p) (h.int q) cfg.b hb).1

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma integral_bmean (h : Noise g gf p σ) (q : E) :
    ∫ ω, bmean cfg g q ω ∂(Measure.pi fun _ : Fin cfg.b => p) = gf q := by
  unfold bmean
  exact ((OracleTemplate.LightTail.finite_mean_integral (P := p) (h.int q) cfg.b hb).2).trans (h.mean q)

lemma err_sq_integrable (h : Noise g gf p σ) (q : E) :
    Integrable (fun ω => ‖bmean cfg g q ω - gf q‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := by
  unfold bmean
  exact (finite_mean_variance (P := p) (h.meas_right q) (h.int q) (gf q) (h.int2 q) (h.mean q)
    cfg.b hb).1

lemma integral_err_sq (h : Noise g gf p σ) (q : E) :
    ∫ ω, ‖bmean cfg g q ω - gf q‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ σ ^ 2 / cfg.b := by
  have := (finite_mean_variance (P := p) (h.meas_right q) (h.int q) (gf q) (h.int2 q) (h.mean q)
    cfg.b hb).2
  unfold bmean
  rw [this]
  exact div_le_div_of_nonneg_right (h.var q) (Nat.cast_nonneg _)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma err_integrable (h : Noise g gf p σ) (q : E) :
    Integrable (fun ω => bmean cfg g q ω - gf q) (Measure.pi fun _ : Fin cfg.b => p) :=
  (bmean_integrable cfg hb h q).sub (integrable_const _)

omit [BorelSpace E] in
lemma integral_inner_err (h : Noise g gf p σ) (q v : E) :
    ∫ ω, ⟪v, bmean cfg g q ω - gf q⟫ ∂(Measure.pi fun _ : Fin cfg.b => p) = 0 := by
  rw [integral_inner (err_integrable cfg hb h q) v, integral_sub (bmean_integrable cfg hb h q)
    (integrable_const _), integral_bmean cfg hb h q, integral_const]
  simp

lemma integral_norm_err (h : Noise g gf p σ) (hσ : 0 ≤ σ) (q : E) :
    ∫ ω, ‖bmean cfg g q ω - gf q‖ ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ σ / Real.sqrt cfg.b := by
  have hint2 := err_sq_integrable cfg hb h q
  have hint1 : Integrable (fun ω => ‖bmean cfg g q ω - gf q‖) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h q).norm
  have hj : (∫ ω, ‖bmean cfg g q ω - gf q‖ ∂(Measure.pi fun _ : Fin cfg.b => p)) ^ 2 ≤
      ∫ ω, ‖bmean cfg g q ω - gf q‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) := by
    have := ConvexOn.map_integral_le (convexOn_pow 2) (continuous_pow 2).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun ω => (norm_nonneg _ : (0:ℝ) ≤ _)) hint1 hint2
    simpa using this
  have hle := hj.trans (integral_err_sq cfg hb h q)
  have hb' : (0 : ℝ) < cfg.b := by exact_mod_cast hb
  have hnn : 0 ≤ ∫ ω, ‖bmean cfg g q ω - gf q‖ ∂(Measure.pi fun _ : Fin cfg.b => p) :=
    integral_nonneg fun _ => norm_nonneg _
  have hrhs : σ ^ 2 / cfg.b = (σ / Real.sqrt cfg.b) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hb'.le]
  rw [hrhs] at hle
  exact (sq_le_sq₀ hnn (div_nonneg hσ (Real.sqrt_nonneg _))).mp hle

lemma chebyshev (h : Noise g gf p σ) (q : E) (c : ℝ) (hc : 0 < c) :
    ∫ ω, (if c < ‖bmean cfg g q ω - gf q‖ then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ σ ^ 2 / cfg.b / c ^ 2 := by
  have hint := err_sq_integrable cfg hb h q
  have hmeas : Measurable (fun ω => if c < ‖bmean cfg g q ω - gf q‖ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const
      ((bmean_measurable cfg h.meas q).sub measurable_const).norm) measurable_const measurable_const
  have hpt : ∀ ω, (if c < ‖bmean cfg g q ω - gf q‖ then (1 : ℝ) else 0) ≤
      ‖bmean cfg g q ω - gf q‖ ^ 2 / c ^ 2 := by
    intro ω
    split_ifs with hh
    · rw [le_div_iff₀ (by positivity)]
      nlinarith [norm_nonneg (bmean cfg g q ω - gf q)]
    · positivity
  have h1 : Integrable (fun ω => if c < ‖bmean cfg g q ω - gf q‖ then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) := by
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    split_ifs <;> simp
  have h2 := integral_mono h1 (hint.div_const _) hpt
  rw [integral_div] at h2
  refine h2.trans ?_
  exact div_le_div_of_nonneg_right (integral_err_sq cfg hb h q) (by positivity)

lemma integral_sq_shift (h : Noise g gf p σ) (q : E) (A v : E) (η : ℝ) :
    ∫ ω, ⟪v, A - η • (bmean cfg g q ω - gf q)⟫ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) =
      ⟪v, A⟫ ^ 2 + η ^ 2 * ∫ ω, ⟪v, bmean cfg g q ω - gf q⟫ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) := by
  have hi1 : Integrable (fun ω => ⟪v, bmean cfg g q ω - gf q⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h q).const_inner v
  have hi2 : Integrable (fun ω => ⟪v, bmean cfg g q ω - gf q⟫ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := by
    refine ((err_sq_integrable cfg hb h q).const_mul (‖v‖ ^ 2)).mono' (hi1.aestronglyMeasurable.pow 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
    have hcs := abs_real_inner_le_norm v (bmean cfg g q ω - gf q)
    exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  have hexp : (fun ω => ⟪v, A - η • (bmean cfg g q ω - gf q)⟫ ^ 2) =
      fun ω => ⟪v, A⟫ ^ 2 - 2 * η * ⟪v, A⟫ * ⟪v, bmean cfg g q ω - gf q⟫ +
        η ^ 2 * ⟪v, bmean cfg g q ω - gf q⟫ ^ 2 := by
    funext ω; rw [inner_sub_right, inner_smul_right]; ring
  have H1 : Integrable (fun ω => ⟪v, A⟫ ^ 2 - 2 * η * ⟪v, A⟫ * ⟪v, bmean cfg g q ω - gf q⟫)
      (Measure.pi fun _ : Fin cfg.b => p) := (integrable_const _).sub (hi1.const_mul _)
  have H2 : Integrable (fun ω => η ^ 2 * ⟪v, bmean cfg g q ω - gf q⟫ ^ 2)
      (Measure.pi fun _ : Fin cfg.b => p) := hi2.const_mul _
  have H3 : Integrable (fun ω => 2 * η * ⟪v, A⟫ * ⟪v, bmean cfg g q ω - gf q⟫)
      (Measure.pi fun _ : Fin cfg.b => p) := hi1.const_mul _
  rw [hexp, integral_add H1 H2, integral_sub (integrable_const _) H3, integral_const_mul,
    integral_const_mul, integral_inner_err cfg hb h q v]
  simp

end LongTails.Proofs.GatedEscapeMoments
