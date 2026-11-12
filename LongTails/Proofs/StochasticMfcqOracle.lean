import LongTails.Proofs.StochasticMfcqEstimator
import LongTails.Proofs.AdaptiveReplicaMoments
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.TerminalClippingEnergy

open MeasureTheory

namespace LongTails.Proofs.StochasticMfcqOracle

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection

noncomputable def mean (p : Params) (I : Problem p) (x : p.E) : JointSpace p :=
  jointEquiv p (gradient I.f x, I.c x, I.J x)

noncomputable def observation (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (x : p.E) (ω : p.Ω) : JointSpace p := jointEquiv p (g x ω, v x ω, D x ω)

variable (p : Params) (I : Problem p)
  (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
  (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
  (H : OracleConditions p I g v D P)

include H in
lemma observation_measurable : Measurable (Function.uncurry (observation p g v D)) :=
  (jointEquiv p).continuous.measurable.comp
    (H.gradientMeasurable.prodMk (H.valueMeasurable.prodMk H.jacobianMeasurable))

include H in
lemma observation_integrable (x : p.E) (hx : feasible p I x) :
    Integrable (observation p g v D x) (P : Measure p.Ω) :=
  (jointEquiv p).toContinuousLinearMap.integrable_comp
    ((H.integrable x hx).1.prodMk ((H.integrable x hx).2.1.prodMk (H.integrable x hx).2.2))

include H in
lemma observation_mean (x : p.E) (hx : feasible p I x) :
    (∫ ω, observation p g v D x ω ∂(P : Measure p.Ω)) = mean p I x := by
  have hi := H.integrable x hx
  rw [show (fun ω => observation p g v D x ω) =
    fun ω => (jointEquiv p).toContinuousLinearMap (g x ω, v x ω, D x ω) from rfl]
  rw [(jointEquiv p).toContinuousLinearMap.integral_comp_comm (hi.1.prodMk (hi.2.1.prodMk hi.2.2)),
    integral_pair hi.1 (hi.2.1.prodMk hi.2.2), integral_pair hi.2.1 hi.2.2,
    H.gradientMean x hx, H.valueMean x hx, H.jacobianMean x hx]
  rfl

lemma observation_error_sq (x : p.E) (ω : p.Ω) :
    ‖observation p g v D x ω - mean p I x‖ ^ 2 =
      ‖g x ω - gradient I.f x‖ ^ 2 + ‖v x ω - I.c x‖ ^ 2 + ‖D x ω - I.J x‖ ^ 2 := by
  unfold observation mean
  rw [← map_sub, StochasticMfcqEstimator.joint_norm_sq]
  rfl

include H in
lemma observation_variance (x : p.E) (hx : feasible p I x) :
    Integrable (fun ω => ‖observation p g v D x ω - mean p I x‖ ^ 2) (P : Measure p.Ω) ∧
    (∫ ω, ‖observation p g v D x ω - mean p I x‖ ^ 2 ∂(P : Measure p.Ω)) ≤ p.σ ^ 2 := by
  simp_rw [observation_error_sq]
  exact ⟨H.varianceIntegrable x hx, H.variance x hx⟩

lemma observation_difference_sq (x y : p.E) (ω : p.Ω) :
    ‖observation p g v D x ω - observation p g v D y ω‖ ^ 2 =
      ‖g x ω - g y ω‖ ^ 2 + ‖v x ω - v y ω‖ ^ 2 + ‖D x ω - D y ω‖ ^ 2 := by
  unfold observation
  rw [← map_sub, StochasticMfcqEstimator.joint_norm_sq]
  rfl

include H in
lemma observation_difference_moment (x y : p.E)
    (hx : feasible p I x) (hy : feasible p I y) :
    Integrable (fun ω => ‖observation p g v D x ω - observation p g v D y ω‖ ^ 2)
      (P : Measure p.Ω) ∧
    (∫ ω, ‖observation p g v D x ω - observation p g v D y ω‖ ^ 2
      ∂(P : Measure p.Ω)) ≤ p.L ^ 2 * ‖x - y‖ ^ 2 := by
  simp_rw [observation_difference_sq]
  exact ⟨H.differenceIntegrable x y hx hy, H.meanSquaredSmooth x y hx hy⟩

include H in
lemma centered_difference_moment (x y : p.E)
    (hx : feasible p I x) (hy : feasible p I y) :
    Integrable (fun ω => ‖(observation p g v D x ω - observation p g v D y ω) -
      (mean p I x - mean p I y)‖ ^ 2) (P : Measure p.Ω) ∧
    (∫ ω, ‖(observation p g v D x ω - observation p g v D y ω) -
      (mean p I x - mean p I y)‖ ^ 2 ∂(P : Measure p.Ω)) ≤ p.L ^ 2 * ‖x - y‖ ^ 2 := by
  have hi := (observation_integrable p I g v D P H x hx).sub
    (observation_integrable p I g v D P H y hy)
  have hmean : (∫ ω, observation p g v D x ω - observation p g v D y ω
      ∂(P : Measure p.Ω)) = mean p I x - mean p I y := by
    rw [integral_sub (observation_integrable p I g v D P H x hx)
      (observation_integrable p I g v D P H y hy),
      observation_mean p I g v D P H x hx, observation_mean p I g v D P H y hy]
  have hraw := observation_difference_moment p I g v D P H x y hx hy
  have hc := OracleTemplate.TerminalClipping.centered_second_moment hi hraw.1
  simp only [Pi.sub_apply] at hc
  rw [hmean] at hc
  exact ⟨hc.1, hc.2.trans hraw.2⟩

include H in
lemma reset_batch_variance (x : p.E) (hx : feasible p I x) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → p.Ω =>
      ‖(1 / (n : ℝ)) • ∑ i, observation p g v D x (ξ i) - mean p I x‖ ^ 2)
      (Measure.pi fun _ : Fin n => (P : Measure p.Ω)) ∧
    (∫ ξ : Fin n → p.Ω,
      ‖(1 / (n : ℝ)) • ∑ i, observation p g v D x (ξ i) - mean p I x‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => (P : Measure p.Ω))) ≤ p.σ ^ 2 / n := by
  have hm : Measurable (observation p g v D x) :=
    (observation_measurable p I g v D P H).comp measurable_prodMk_left
  have hv := observation_variance p I g v D P H x hx
  have hb := OracleTemplate.RobustGradient.finite_mean_variance hm
    (observation_integrable p I g v D P H x hx) (mean p I x) hv.1
    (observation_mean p I g v D P H x hx) n hn
  refine ⟨hb.1, ?_⟩
  rw [hb.2]
  exact div_le_div_of_nonneg_right hv.2 (Nat.cast_nonneg n)

include H in
lemma increment_batch_variance (x y : p.E) (hx : feasible p I x)
    (hy : feasible p I y) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → p.Ω =>
      ‖(1 / (n : ℝ)) • ∑ i, (observation p g v D x (ξ i) - observation p g v D y (ξ i)) -
        (mean p I x - mean p I y)‖ ^ 2)
      (Measure.pi fun _ : Fin n => (P : Measure p.Ω)) ∧
    (∫ ξ : Fin n → p.Ω,
      ‖(1 / (n : ℝ)) • ∑ i, (observation p g v D x (ξ i) - observation p g v D y (ξ i)) -
        (mean p I x - mean p I y)‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => (P : Measure p.Ω))) ≤ p.L ^ 2 * ‖x - y‖ ^ 2 / n := by
  have hm := observation_measurable p I g v D P H
  have hxI := observation_integrable p I g v D P H x hx
  have hyI := observation_integrable p I g v D P H y hy
  have hv := centered_difference_moment p I g v D P H x y hx hy
  have hmean : (∫ ω, observation p g v D x ω - observation p g v D y ω
      ∂(P : Measure p.Ω)) = mean p I x - mean p I y := by
    rw [integral_sub hxI hyI, observation_mean p I g v D P H x hx,
      observation_mean p I g v D P H y hy]
  have hb := OracleTemplate.RobustGradient.finite_mean_variance
    ((hm.comp measurable_prodMk_left).sub (hm.comp measurable_prodMk_left))
    (hxI.sub hyI) (mean p I x - mean p I y) hv.1 hmean n hn
  simp only [Function.comp_def, Function.uncurry_apply_pair, Pi.sub_apply] at hb
  refine ⟨hb.1, ?_⟩
  rw [hb.2]
  exact div_le_div_of_nonneg_right hv.2 (Nat.cast_nonneg n)

end LongTails.Proofs.StochasticMfcqOracle
