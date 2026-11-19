import LongTails.Proofs.WeightedInterpolationEstimator
import LongTails.Proofs.WeightedInterpolationSampling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationStep

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationBatch WeightedInterpolationPrecision
open WeakInterpolationGeometry WeightedInterpolationEstimator

variable {p : Params}

structure Data (p : Params) (f : Functions p) (g : LocalOracle p) (z : Point p)
    (P : Measure (Samples p)) (ν : Fin p.n → ProbabilityMeasure p.Ω) : Prop where
  valid : spec.valid p
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  differentiable : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  lipschitz : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖
  solution : z ∈ solutions p f
  initial : ‖p.x0 - z‖ ≤ p.R
  growth : ∀ x, p.μ/2 * Metric.infDist x (solutions p f)^2 ≤ objective p f x - objective p f z
  workers : iIndepFun (fun i (s : Samples p) => s i) P
  samples : ∀ i, IID (fun j (s : Samples p) => s i j) (ν i : Measure _) P
  stochastic : ∀ i, IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ

variable {f : Functions p} {g : LocalOracle p} {z : Point p}
    {P : Measure (Samples p)} [IsProbabilityMeasure P] {ν : Fin p.n → ProbabilityMeasure p.Ω}

lemma fixed_noise (D : Data p f g z P ν) (T : DistributedTemplate.Time) (k : ℕ) (x v : Point p) :
    let u := stepSize p k • direction p f x
    let δ := errorRadius p T x
    let e := tolerance p
    ∫ s, ‖v - (estimate p T k g x s - u)‖^2 ∂P ≤
      ‖v‖^2 + 2*‖v‖*(e + 3*δ) + 4 * stepSize p k ^ 2 * p.σ^2 * information p / (batchTime p : ℝ) +
      12*δ^2 + 2*(e+δ)^2 := by
  let δ := errorRadius p T x
  let e := tolerance p
  let X := message p T k g x
  let m := localMean p k f x
  let q := fraction p
  let a i := stepSize p k * weights p i / q i
  let V i := (a i * p.σ)^2 / batch p i
  let r := Algorithms.DistributedBatchedSgd.radius (rawParams p) x
  let u := stepSize p k • direction p f x
  let Y := fun s => ∑ i, q i • (X i s - m i)
  let U := fun s => estimate p T k g x s - u
  have he := tolerance_pos D.valid
  have hn := noise_nonneg D.valid
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hlocal (i : Fin p.n) := local_radius D.valid k i f (D.lipschitz i) D.solution D.initial x
  have hm (i : Fin p.n) := bias_margin D.valid x (m i) (hlocal i)
  have hmessage i := message_moments D.valid T k g f x P ν D.samples D.stochastic i (hm i).1
  have hM (i : Fin p.n) : V i ≤ noiseRadius p ^ 2 := by
    have ha := alpha_bounds D.valid k i
    have hσ := D.valid.2.2.2.2.2.1
    have hb : (1 : ℝ) ≤ batch p i := by exact_mod_cast batch_pos p i
    apply (div_le_iff₀ (by exact_mod_cast batch_pos p i)).mpr
    have hsq := mul_self_le_mul_self (mul_nonneg ha.1 hσ) ha.2.2
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (noiseRadius p))]
  have hXI (i : Fin p.n) : Integrable (X i) P := (hmessage i).1
  have hbias (i : Fin p.n) : ‖(∫ s, X i s ∂P) - m i‖ ≤ e+δ := by
    have h := (div_le_div_of_nonneg_right (hM i) (sub_pos.mpr (hm i).1).le).trans (hm i).2
    exact (hmessage i).2.2.2.trans (add_le_add h le_rfl)
  have hworker := WeakInterpolationAggregation.weighted_moments (p := rawParams p)
    P q (fun i => (fraction_pos p i).le) (fraction_sum p) X m (fun i => 2*V i+2*δ^2) (e+δ)
    (message_independent T k g (fun i => (D.stochastic i).measurable) x P D.workers) hXI
    (fun i => (hmessage i).2.1) (fun i => (hmessage i).2.2.1) hbias
  have hUmeas : Measurable U :=
    ((DistributedBatchedSgd.measurable_estimate (rawConfig p T) (scaled p g k)
      (measurable_scaled g (fun i => (D.stochastic i).measurable) k) 0).comp
      (measurable_const.prodMk measurable_id)).sub_const _
  have hfinite : (Set.range U).Finite := by
    have h := DistributedBatchedSgd.finite_range_estimate (rawConfig p T) (scaled p g k)
      (fun _ => x) Set.finite_range_const 0
    exact (h.image (fun y => y - u)).subset (by rintro _ ⟨s,rfl⟩; exact ⟨_,⟨s,rfl⟩,rfl⟩)
  have hU := DistributedBatchedSgd.integrable_finite_range P U hUmeas hfinite
  have hU2 := DistributedBatchedSgd.integrable_finite_range P (fun s => ‖U s‖^2) (hUmeas.norm.pow_const _)
    ((hfinite.image (fun y => ‖y‖^2)).subset (by rintro _ ⟨s,rfl⟩; exact ⟨_,⟨s,rfl⟩,rfl⟩))
  have hd := WeakInterpolationAggregation.noisy_displacement (p := rawParams p)
    P v Y U hworker.1 hU hworker.2.1 hU2 (δ := 2*δ)
    hworker.2.2.2 hworker.2.2.1 (estimator_residual D.valid T k g f x)
  have hv := weighted_variance D.valid k δ
  change (∑ i, q i ^ 2 * (2*V i+2*δ^2)) ≤ _ at hv
  change (∫ s, ‖v-U s‖^2 ∂P) ≤ _
  change (∫ s, ‖v-U s‖^2 ∂P) ≤ ‖v‖^2 + 2*‖v‖*(e+δ+2*δ) +
    2*((∑ i, q i^2*(2*V i+2*δ^2)) + (e+δ)^2) + 2*(2*δ)^2 at hd
  change _ ≤ ‖v‖^2 + 2*‖v‖*(e + 3*δ) + 4*stepSize p k^2*p.σ^2*information p/(batchTime p : ℝ) +
    12*δ^2 + 2*(e+δ)^2
  linear_combination hd + 2 * hv

end LongTails.Proofs.WeightedInterpolationStep
