import LongTails.Proofs.SurjectiveConfidenceProbability
import LongTails.Proofs.SurjectiveConfidenceOutput

open MeasureTheory

set_option backward.isDefEq.respectTransparency false

namespace LongTails.Proofs.SurjectiveConfidenceConvergence

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities (Primitive Constraint Jacobian Problem Regularity OracleConditions accurate)
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveConfidence
open LongTails.Algorithms.SurjectiveProxLinear (radius certificateError iterations)
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveConfidenceExecution
open LongTails.Proofs.SurjectiveConfidenceCertificate
open LongTails.Proofs.SurjectiveConfidenceOutput
open LongTails.Proofs.SurjectiveConfidenceProbability

lemma selected_certificate_failure (p : Params) (hp : spec.valid p) (I : Problem p.problem)
    (H : Regularity p.problem I) (g : p.problem.E → p.problem.Ω → p.problem.E)
    (v : p.problem.E → p.problem.Ω → Constraint p.problem)
    (D : p.problem.E → p.problem.Ω → Jacobian p.problem) (μ : ProbabilityMeasure p.problem.Ω)
    (O : OracleConditions p.problem I g v D μ) :
    ((PMF.uniformOfFintype (Fin (iterations p.problem + 1))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω)))
      {z | certificateError p.problem / 4 <
        ‖jointEquiv p.problem (candidate p (fun x ω => (g x ω, v x ω, D x ω)) z.1 z.2).2 -
          jointMean p.problem I (candidate p (fun x ω => (g x ω, v x ω, D x ω)) z.1 z.2).1‖}
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ groups p) := by
  have hraw := O.gradientMeasurable.prodMk (O.valueMeasurable.prodMk O.jacobianMeasurable)
  have hF := measurable_candidate p hp.1 (fun x ω => (g x ω, v x ω, D x ω)) hraw
  have hM := (jointMean_continuous p.problem I H (le_trans zero_le_one hp.1.2.1)).measurable
  have hS := measurableSet_lt (measurable_const (a := certificateError p.problem / 4))
    (((jointEquiv p.problem).continuous.measurable.comp hF.snd).sub (hM.comp hF.fst)).norm
  simp only [Function.comp_def, Pi.sub_apply] at hS
  rw [Measure.prod_apply hS]
  have hb : ∀ t : Fin (iterations p.problem + 1),
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω))
        {ξ | certificateError p.problem / 4 <
          ‖jointEquiv p.problem (candidate p (fun x ω => (g x ω, v x ω, D x ω)) t ξ).2 -
            jointMean p.problem I (candidate p (fun x ω => (g x ω, v x ω, D x ω)) t ξ).1‖}
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ groups p) := by
    intro t
    simp_rw [candidate_certificate]
    exact estimator_failure p hp I H g v D μ O t
  exact (lintegral_mono hb).trans_eq (by simp)

lemma selected_success (p : Params) (hp : spec.valid p) (I : Problem p.problem)
    (H : Regularity p.problem I) (g : p.problem.E → p.problem.Ω → p.problem.E)
    (v : p.problem.E → p.problem.Ω → Constraint p.problem)
    (D : p.problem.E → p.problem.Ω → Jacobian p.problem) (μ : ProbabilityMeasure p.problem.Ω)
    (O : OracleConditions p.problem I g v D μ) :
    ENNReal.ofReal (1 - p.δ) ≤
      ((seedLaw p : Measure (Fin (replicas p) → Fin (iterations p.problem + 1))).prod (Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω)))
      {z | accurate p.problem I (selectFunction p (fun i : Fin (replicas p) =>
        candidate p (fun x ω => (g x ω, v x ω, D x ω)) (z.1 i)
          (fun j => z.2 (trialCalls p * i.val + j))))} := by
  let Z := fun x ω => (g x ω, v x ω, D x ω)
  let F := fun z : Fin (iterations p.problem + 1) × (ℕ → p.problem.Ω) => candidate p Z z.1 z.2
  have hraw : Measurable (Function.uncurry Z) :=
    O.gradientMeasurable.prodMk (O.valueMeasurable.prodMk O.jacobianMeasurable)
  have hF := measurable_candidate p hp.1 Z hraw
  let A : Set (p.problem.E × Primitive p.problem) :=
    {u | radius p.problem / 8 < ‖exactModelStep p.problem I u.1‖}
  let B : Set (p.problem.E × Primitive p.problem) :=
    {u | certificateError p.problem / 4 < ‖jointEquiv p.problem u.2 - jointMean p.problem I u.1‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (((continuous_exactModelStep p.problem I hp.1 H).measurable.comp measurable_fst).norm)
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (((jointEquiv p.problem).continuous.measurable.comp measurable_snd).sub
      ((jointMean_continuous p.problem I H (le_trans zero_le_one hp.1.2.1)).measurable.comp measurable_fst)).norm
  have hbad := block_replica_failure
    (PMF.uniformOfFintype (Fin (iterations p.problem + 1))).toMeasure (μ : Measure p.problem.Ω)
    F hF (trialCalls p) (replicas p) (fun t ξ η h => candidate_congr p Z t ξ η h)
    A B hA hB (candidate_step_failure p.problem I hp.1 H g v D μ O)
    (selected_certificate_failure p hp I H g v D μ O)
  let C := fun z : (Fin (replicas p) → Fin (iterations p.problem + 1)) × (ℕ → p.problem.Ω) =>
    fun i : Fin (replicas p) => F (z.1 i, fun j => z.2 (trialCalls p * i.val + j))
  have hC : Measurable C := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (Fin (replicas p) → Fin (iterations p.problem + 1)) × (ℕ → p.problem.Ω) =>
        (z.1 i, fun j => z.2 (trialCalls p * i.val + j))) by fun_prop)
  let bad := {z | (∀ i : Fin (replicas p), C z i ∈ A) ∨ (∃ i : Fin (replicas p), C z i ∈ B)}
  have hAllM : MeasurableSet {z | ∀ i : Fin (replicas p), C z i ∈ A} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i : Fin (replicas p) => ((measurable_pi_apply i).comp hC) hA)
  have hAnyM : MeasurableSet {z | ∃ i : Fin (replicas p), C z i ∈ B} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun i : Fin (replicas p) => ((measurable_pi_apply i).comp hC) hB)
  have hbadM : MeasurableSet bad := hAllM.union hAnyM
  let P := (seedLaw p : Measure (Fin (replicas p) → Fin (iterations p.problem + 1))).prod (Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω))
  have hbound : P bad ≤ ENNReal.ofReal p.δ := by
    apply hbad.trans
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast (replicas p), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (SurjectiveConfidenceTuning.confidence_failure_bound p hp)
  have hreal : P.real bad ≤ p.δ := by
    exact (ENNReal.toReal_mono (by simp) hbound).trans_eq (ENNReal.toReal_ofReal hp.2.1.le)
  have hsuccess : ENNReal.ofReal (1 - p.δ) ≤ P badᶜ := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    rw [measureReal_compl hbadM, probReal_univ]
    linarith
  apply hsuccess.trans
  apply measure_mono
  intro z hz
  have hh : ¬ ((∀ i : Fin (replicas p), C z i ∈ A) ∨ (∃ i : Fin (replicas p), C z i ∈ B)) := hz
  apply selection_accurate p hp I H (C z)
  · have h := (not_or.mp hh).1
    simp only [A, Set.mem_ofPred_eq, not_forall, not_lt] at h
    exact h
  · have h := (not_or.mp hh).2
    simpa only [B, Set.mem_ofPred_eq, not_exists, not_lt] using h

lemma execution_success (p : Params) (hp : spec.valid p) (I : Problem p.problem)
    (oracle : Oracle (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem))
    (hadm : spec.admissible p I oracle) (K : ℕ)
    (hK : trialCalls p * replicas p ≤ K) :
    spec.successful p I
      (fun seed : (algorithm p).Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle (algorithm p) (fun _ => K) seed.1 seed.2)
      ⟨((algorithm p).law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  obtain ⟨g, v, D, μ, P, hIID, rfl, H, O⟩ := hadm
  have hP : (P : Measure (ℕ → p.problem.Ω)) =
      Measure.infinitePi fun _ : ℕ => (μ : Measure p.problem.Ω) := by
    exact (Measure.map_id' (μ := (P : Measure (ℕ → p.problem.Ω)))).symm.trans hIID.stream_law.map_eq
  let Z := fun x ω => (g x ω, v x ω, D x ω)
  have hraw : Measurable (Function.uncurry Z) :=
    O.gradientMeasurable.prodMk (O.valueMeasurable.prodMk O.jacobianMeasurable)
  have hF := measurable_candidate p hp.1 Z hraw
  let C := fun z : (Fin (replicas p) → Fin (iterations p.problem + 1)) × (ℕ → p.problem.Ω) =>
    fun i : Fin (replicas p) => candidate p Z (z.1 i) (fun j => z.2 (trialCalls p * i.val + j))
  have hC : Measurable C := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (Fin (replicas p) → Fin (iterations p.problem + 1)) × (ℕ → p.problem.Ω) =>
        (z.1 i, fun j => z.2 (trialCalls p * i.val + j))) by fun_prop)
  have hout :
      (fun seed : (algorithm p).Seed × (ℕ → p.problem.Ω) =>
        execute ({ Seed := fun _ => p.problem.Ω
                   law := P
                   answer := fun _ (_, z) ω => ((g z.1 ω, v z.1 ω, D z.1 ω),
            (g z.2 ω, v z.2 ω, D z.2 ω)) } :
          Oracle (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem))
          (algorithm p) (fun _ => K) seed.1 seed.2) =
      (fun z => selectFunction p (C z)) := by
    funext seed
    rw [execution_output p Z P K seed.1 seed.2 hK, select_ofFn]
  change Measurable _ ∧ _
  rw [hout]
  refine ⟨(measurable_selectFunction p hp).comp hC, ?_⟩
  change ENNReal.ofReal (1 - p.δ) ≤ ((seedLaw p : Measure (Fin (replicas p) → Fin (iterations p.problem + 1))).prod (P : Measure (ℕ → p.problem.Ω))) _
  rw [hP]
  exact selected_success p hp I H g v D μ O

end LongTails.Proofs.SurjectiveConfidenceConvergence
