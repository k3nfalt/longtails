import LongTails.Proofs.SurjectiveConfidenceTuning
import LongTails.Proofs.SurjectiveConfidenceExecution

open MeasureTheory

set_option backward.isDefEq.respectTransparency false

namespace LongTails.Proofs.SurjectiveConfidenceCertificate

lemma adaptive_pilot_failure {Ω X V : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n k m : ℕ)
    (x : (ℕ → Ω) → X) (hx : Measurable x)
    (hdep : ∀ ξ η, (∀ j < n, ξ j = η j) → x ξ = x η)
    (g : X → Ω → V) (hg : Measurable (Function.uncurry g))
    (mean : X → V) (hmean : Measurable mean) {σ a : ℝ} (ha : 0 < a)
    (hm : 0 < m) (hsize : 144 * σ ^ 2 ≤ (m : ℝ) * a ^ 2)
    (hi : ∀ z, Integrable (g z) μ) (hμ : ∀ z, ∫ ω, g z ω ∂μ = mean z)
    (hvi : ∀ z, Integrable (fun ω => ‖g z ω - mean z‖ ^ 2) μ)
    (hv : ∀ z, (∫ ω, ‖g z ω - mean z‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | a < ‖LongTails.Algorithms.SymmetricThirdOrder.gradientPilot a
        (fun (i : Fin k) (j : Fin m) => g (x ξ) (ξ (n + m * i.val + j.val))) - mean (x ξ)‖}
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  obtain ⟨G, hG, hfactor⟩ := SymmetricThirdOrderSampling.measurable_prefix_factor μ n x hx hdep
  let S : Set ((Fin n → Ω) × (Fin k → Fin m → Ω)) := {z |
    a < ‖LongTails.Algorithms.SymmetricThirdOrder.gradientPilot a
      (fun i j => g (G z.1) (z.2 i j)) - mean (G z.1)‖}
  have hdata : Measurable (fun z : (Fin n → Ω) × (Fin k → Fin m → Ω) =>
      (a, fun (i : Fin k) (j : Fin m) => g (G z.1) (z.2 i j))) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hg.comp ((hG.comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)))
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    (((SymmetricThirdOrderEstimation.measurable_gradientPilot k m).comp hdata).sub
      (hmean.comp (hG.comp measurable_fst))).norm
  have hlaw := SymmetricThirdOrderSampling.prefix_group_law
    (OracleTemplate.StochasticGeneralized.infinitePi_iid μ) n k m
  have he := hlaw.measure_preimage hS.nullMeasurableSet
  simp only [Set.preimage_ofPred_eq, S, ← hfactor] at he
  rw [he, Measure.prod_apply hS]
  have hb : ∀ u, (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μ)
      {v | (u, v) ∈ S} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro u
    exact SymmetricThirdOrderEstimation.gradientPilot_failure
      (hg.comp (measurable_const.prodMk measurable_id)) (hi (G u)) (mean (G u))
      (hμ (G u)) ha (hvi (G u)) (hv (G u)) k m hm hsize
  exact (lintegral_mono hb).trans_eq (by simp)

open LongTails.Algorithms.SurjectiveConfidence
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearTuning
open LongTails.Proofs.SurjectiveConfidenceExecution

noncomputable def estimator (p : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.Params)
    (Z : p.problem.E → p.problem.Ω → JointSpace p.problem)
    (t : ℕ) (ξ : ℕ → p.problem.Ω) : JointSpace p.problem :=
  LongTails.Algorithms.SymmetricThirdOrder.gradientPilot (certificateError p.problem / 4)
    (fun (i : Fin (groups p)) (j : Fin (batch p)) =>
      Z (trajectory p.problem Z ξ t).1 (ξ (trainingCalls p + batch p * i.val + j.val)))

lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

lemma candidate_certificate (p : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.Params)
    (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (t : Fin (iterations p.problem + 1)) (ξ : ℕ → p.problem.Ω) :
    jointEquiv p.problem (candidate p Z t ξ).2 =
      estimator p (SurjectiveProxLinearExecution.liftedOracle p.problem Z) t.val ξ := by
  have hscale : 2 * (certificateError p.problem / 4) = certificateError p.problem / 2 := by ring
  simp only [candidate, robustEstimate, estimator,
    LongTails.Algorithms.SymmetricThirdOrder.gradientPilot, hscale]
  change OracleTemplate.RobustGradient.pilotCenter _ _ = _
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [getD_ofFn, getD_ofFn]
  rfl

lemma measurable_estimator (p : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.Params)
    (hp : spec.valid p.problem) (Z : p.problem.E → p.problem.Ω → JointSpace p.problem)
    (hZ : Measurable (Function.uncurry Z)) (t : ℕ) : Measurable (estimator p Z t) := by
  have hx := (measurable_trajectory p.problem hp Z hZ t).fst
  have hdata : Measurable (fun ξ : ℕ → p.problem.Ω =>
      (certificateError p.problem / 4, fun (i : Fin (groups p)) (j : Fin (batch p)) =>
        Z (trajectory p.problem Z ξ t).1 (ξ (trainingCalls p + batch p * i.val + j.val)))) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hZ.comp (hx.prodMk (measurable_pi_apply (trainingCalls p + batch p * i.val + j.val)))
  exact (SymmetricThirdOrderEstimation.measurable_gradientPilot (groups p) (batch p)).comp hdata

lemma measurable_candidate (p : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.Params)
    (hp : spec.valid p.problem) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (hZ : Measurable (Function.uncurry Z)) :
    Measurable (fun z : Fin (iterations p.problem + 1) × (ℕ → p.problem.Ω) =>
      candidate p Z z.1 z.2) := by
  have hJ : Measurable (Function.uncurry (SurjectiveProxLinearExecution.liftedOracle p.problem Z)) :=
    (jointEquiv p.problem).continuous.measurable.comp hZ
  apply measurable_from_prod_countable_right
  intro t
  have heq (ξ : ℕ → p.problem.Ω) : candidate p Z t ξ =
      ((trajectory p.problem (SurjectiveProxLinearExecution.liftedOracle p.problem Z) ξ t.val).1,
        (jointEquiv p.problem).symm
          (estimator p (SurjectiveProxLinearExecution.liftedOracle p.problem Z) t.val ξ)) := by
    apply Prod.ext
    · rfl
    · apply (jointEquiv p.problem).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, candidate_certificate]
  simp_rw [heq]
  exact (measurable_trajectory p.problem hp _ hJ t.val).fst.prodMk
    ((jointEquiv p.problem).symm.continuous.measurable.comp (measurable_estimator p hp _ hJ t.val))

lemma estimator_failure (p : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.Params)
    (hp : LongTails.Setups.ConfidentStochasticSurjectiveInequalities.spec.valid p)
    (I : Problem p.problem) (H : Regularity p.problem I)
    (g : p.problem.E → p.problem.Ω → p.problem.E)
    (v : p.problem.E → p.problem.Ω → Constraint p.problem)
    (D : p.problem.E → p.problem.Ω → Jacobian p.problem) (μ : ProbabilityMeasure p.problem.Ω)
    (O : OracleConditions p.problem I g v D μ)
    (t : Fin (iterations p.problem + 1)) :
    (Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω))
      {ξ | certificateError p.problem / 4 <
        ‖estimator p (jointOracle p.problem g v D) t.val ξ -
          jointMean p.problem I (trajectory p.problem (jointOracle p.problem g v D) ξ t.val).1‖}
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ groups p) := by
  have hZ := jointOracle_measurable p.problem I g v D μ O
  have hpos := (variance_scales_positive p.problem hp.1).2.2.1
  apply adaptive_pilot_failure (μ : Measure p.problem.Ω) (trainingCalls p) (groups p) (batch p)
    (fun ξ => (trajectory p.problem (jointOracle p.problem g v D) ξ t.val).1)
    (measurable_trajectory p.problem hp.1 _ hZ t.val).fst
  · intro ξ η h
    apply congrArg Prod.fst
    apply trajectory_congr
    intro j hj
    apply h j
    have ht := t.isLt
    unfold trainingCalls
    omega
  · exact hZ
  · exact (jointMean_continuous p.problem I H (le_trans zero_le_one hp.1.2.1)).measurable
  · positivity
  · unfold batch
    omega
  · exact SurjectiveConfidenceTuning.batch_sufficient p hp
  · exact jointOracle_integrable p.problem I g v D μ O
  · exact jointOracle_mean p.problem I g v D μ O
  · exact fun x => (jointOracle_variance p.problem I g v D μ O x).1
  · exact fun x => (jointOracle_variance p.problem I g v D μ O x).2

end LongTails.Proofs.SurjectiveConfidenceCertificate
