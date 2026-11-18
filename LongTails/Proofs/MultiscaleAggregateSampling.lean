import LongTails.Proofs.MultiscaleAggregateHistory
import LongTails.Proofs.MultiscaleAggregateBudget
import LongTails.Proofs.SvrgConvex

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateSampling

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateHistory MultiscaleAggregateTrajectory MultiscaleAggregateBudget

noncomputable abbrev streamParams (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params where
  d := p.d
  n := p.n
  Ω := p.Ω
  h := p.h
  l := p.l
  b := p.b
  L := p.L
  Δ := p.Δ
  σ := 0
  ε := p.ε
  x0 := p.x0

noncomputable abbrev streamConfig (p : Params) :
    LongTails.Algorithms.DistributedBatchedSgd.Config (streamParams p) :=
  ⟨1, batch p, 1, 0⟩

variable {p : Params}

lemma objective_gradient (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (x : Point p) : HasGradientAt (objective p f) ((p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x) x :=
  OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hg x

lemma worker_moments (P : Measure (Samples p)) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (x : Point p) (k : ℕ) (i : Fin p.n) :
    let X := fun s => batchMean p g s k i x
    Integrable X P ∧ (∫ s, X s ∂P) = gradient (f i) x ∧
      Integrable (fun s => ‖X s - gradient (f i) x‖ ^ 2) P ∧
      ∫ s, ‖X s - gradient (f i) x‖ ^ 2 ∂P ≤ p.σ i ^ 2 / batch p i := by
  let X := fun ξ : Fin (batch p i) → p.Ω => (1 / (batch p i : ℝ)) • ∑ j, g i x (ξ j)
  obtain ⟨hXi, hX⟩ := OracleTemplate.LightTail.finite_mean_integral ((hsg i).integrable x)
    (batch p i) (batch_pos i)
  obtain ⟨hX₂i, hX₂⟩ := OracleTemplate.RobustGradient.finite_mean_variance
    ((hsg i).measurable.comp measurable_prodMk_left) ((hsg i).integrable x) (gradient (f i) x)
    ((hsg i).variance_integrable x) ((hsg i).unbiased x) (batch p i) (batch_pos i)
  have hl := DistributedSampling.worker_batch_law (streamParams p) (streamConfig p) P μ hIID k i
  let proj := fun (s : Samples p) (j : Fin (batch p i)) => s i (k * batch p i + j)
  have hident (s : Samples p) : X (proj s) = batchMean p g s k i x := by
    simp only [X, proj, batchMean, one_div]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j => g i x (s i (k * batch p i + j))) _
  change Integrable X _ at hXi
  change Integrable (fun ξ => ‖X ξ - gradient (f i) x‖ ^ 2) _ at hX₂i
  change HasLaw proj _ P at hl
  have hi := hl.integrable_comp hXi
  have hi₂ := hl.integrable_comp hX₂i
  have he := hl.integral_comp hXi.aestronglyMeasurable
  have he₂ := hl.integral_comp hX₂i.aestronglyMeasurable
  simp only [Function.comp_def, hident] at hi hi₂ he he₂
  exact ⟨hi, he.trans (hX.trans ((hsg i).unbiased x)), hi₂,
    he₂.trans_le (hX₂.trans_le (div_le_div_of_nonneg_right ((hsg i).variance x) (Nat.cast_nonneg _)))⟩

noncomputable def unrounded (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (k : ℕ) (x : Point p) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, batchMean p g s k i x

lemma aggregate_variance (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) (x : Point p) (k : ℕ) :
    let e := fun s => ‖unrounded p g s k x - gradient (objective p f) x‖ ^ 2
    Integrable e P ∧ (∫ s, e s ∂P) ≤ precision p ^ 2 := by
  let X := fun i (s : Samples p) => batchMean p g s k i x - gradient (f i) x
  have hwm := worker_moments P μ hIID g f hsg x k
  have hInd : iIndepFun X P := by
    let M := fun i (ξ : ℕ → p.Ω) =>
      (batch p i : ℝ)⁻¹ • ∑ j ∈ Finset.range (batch p i), g i x (ξ (k * batch p i + j))
    apply hw.comp (fun i ξ => M i ξ - gradient (f i) x)
    intro i
    apply Measurable.sub_const
    apply Measurable.fun_const_smul
    exact Finset.measurable_sum _ fun j _ =>
      ((hsg i).measurable.comp measurable_prodMk_left).comp (measurable_pi_apply _)
  obtain ⟨hI, hE⟩ := DistributedBatchedSgd.independent_biased_sum (p := streamParams p) P X
    (fun i => p.σ i ^ 2 / batch p i) (fun _ => 0) hInd
    (fun i => (hwm i).1.sub (integrable_const _)) (fun i => (hwm i).2.2.1)
    (fun i => (hwm i).2.2.2) (fun i => by
      change ‖∫ s, batchMean p g s k i x - (fun _ : Samples p => gradient (f i) x) s ∂P‖ ≤ 0
      rw [integral_sub (hwm i).1 (integrable_const _), (hwm i).2.1]
      simp)
  have he (s : Samples p) : ‖unrounded p g s k x - gradient (objective p f) x‖ ^ 2 =
      ((p.n : ℝ)⁻¹)^2 * ‖∑ i, X i s‖ ^ 2 := by
    rw [unrounded, (objective_gradient f hg x).gradient, ← smul_sub,
      ← Finset.sum_sub_distrib, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hE
  simp only [he]
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ ((p.n : ℝ)⁻¹) ^ 2 * ((p.n : ℝ) ^ 2 * precision p ^ 2) :=
      mul_le_mul_of_nonneg_left (hE.trans (batch_variance hh hε)) (sq_nonneg _)
    _ = _ := by field_simp

end LongTails.Proofs.MultiscaleAggregateSampling
