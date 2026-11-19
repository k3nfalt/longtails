import LongTails.Proofs.WeightedInterpolationBatch
import LongTails.Proofs.WeightedInterpolationPrecision
import LongTails.Proofs.WeakInterpolationAggregation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationEstimator

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationBatch WeightedInterpolationPrecision
open WeakInterpolationGeometry

variable {p : Params}

noncomputable def estimate (p : Params) (T : DistributedTemplate.Time) (k : ℕ) (g : LocalOracle p)
    (x : Point p) (s : Samples p) : Point p :=
  Algorithms.DistributedBatchedSgd.estimate (rawParams p) (rawConfig p T) (scaled p g k) x 0 s

lemma message_independent (T : DistributedTemplate.Time) (k : ℕ) (g : LocalOracle p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (x : Point p)
    (P : Measure (Samples p)) (hw : iIndepFun (fun i (s : Samples p) => s i) P) :
    iIndepFun (message p T k g x) P := by
  let f (i : Fin p.n) (s : ℕ → p.Ω) := quantizer p T x
    ((batch p i : ℝ)⁻¹ • ∑ j ∈ Finset.range (batch p i), scaled p g k i x (s j))
  have hm i : Measurable (f i) := (measurable_quantizer T x).comp
    ((Finset.measurable_sum _ fun j _ => ((measurable_scaled g hg k i).comp
      measurable_prodMk_left).comp (measurable_pi_apply j)).fun_const_smul _)
  have he : message p T k g x = fun i s => f i (s i) := by
    funext i s
    simp only [f, message, Algorithms.DistributedBatchedSgd.batchMean, zero_mul, zero_add]
    rfl
  rw [he]
  exact hw.comp f hm

lemma mean_direction (p : Params) (k : ℕ) (f : Functions p) (x : Point p) :
    ∑ i, fraction p i • localMean p k f x i = stepSize p k • direction p f x := by
  unfold direction localMean
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul]
  congr 1
  field_simp [(fraction_pos p i).ne']

lemma estimator_residual (hp : spec.valid p) (T : DistributedTemplate.Time) (k : ℕ)
    (g : LocalOracle p) (f : Functions p) (x : Point p) (s : Samples p) :
    let δ := errorRadius p T x
    let u := stepSize p k • direction p f x
    let Y := ∑ i, fraction p i • (message p T k g x i s - localMean p k f x i)
    ‖estimate p T k g x s - u - Y‖ ≤ 2*δ := by
  dsimp only
  simp only [smul_sub, Finset.sum_sub_distrib, mean_direction p, sub_sub_sub_cancel_right]
  let z := fun i => Algorithms.DistributedBatchedSgd.batchMean
    (rawParams p) (rawConfig p T) (scaled p g k) x 0 s i
  apply WeakInterpolationAggregation.broadcast_displacement (p := rawParams p) (fraction p)
    (fun i => (fraction_pos p i).le) (fraction_sum p)
    (R := Algorithms.DistributedBatchedSgd.radius (rawParams p) x)
    (by rw [radius_eq hp]; have := guard_nonneg hp; positivity)
    (Real.sqrt_nonneg _) (quantizer p T x) (quantizer_error hp T x) z

lemma weighted_variance (hp : spec.valid p) (k : ℕ) (δ : ℝ) :
    ∑ i, fraction p i ^ 2 *
      (2 * ((stepSize p k * weights p i / fraction p i * p.σ)^2 / batch p i) + 2*δ^2) ≤
      2 * stepSize p k ^ 2 * p.σ ^ 2 * information p / (batchTime p : ℝ) + 2*δ^2 := by
  have he i : fraction p i ^ 2 * (2 * ((stepSize p k * weights p i / fraction p i * p.σ)^2 / batch p i) + 2*δ^2) =
      (2 * stepSize p k ^ 2 * p.σ ^ 2) * (weights p i ^2 / batch p i) + fraction p i ^2 * (2*δ^2) := by
    field_simp [(fraction_pos p i).ne']
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have ht : 0 < (batchTime p : ℝ) := by
    exact_mod_cast (hp.1 0).trans_le (local_time p 0)
  have hv := (le_div_iff₀ ht).mpr (variance_cost hp)
  have hs : ∑ i, fraction p i ^ 2 ≤ 1 := DistributedBatchedSgd.batch_weights_square _ (total_pos p)
  have h1 := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * stepSize p k ^ 2 * p.σ^2)
  have h2 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 2*δ^2)
  simpa only [one_mul, mul_div_assoc] using add_le_add h1 h2

end LongTails.Proofs.WeightedInterpolationEstimator
