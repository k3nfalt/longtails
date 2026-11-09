import LongTails.Proofs.SurjectiveConfidenceCertificate
import LongTails.Proofs.AdaptiveEntropicStateMeasurable
import LongTails.Proofs.AdaptiveEntropicExecution

open MeasureTheory

namespace LongTails.Proofs.SurjectiveConfidenceOutput

open OracleTemplate
open LongTails.Algorithms.SurjectiveConfidence
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Setups.StochasticSurjectiveInequalities (Primitive Constraint Problem Regularity accurate)
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearExactModel

lemma select_ofFn (p : Params)
    (entries : Fin (replicas p) → p.problem.E × Primitive p.problem) :
    select p (List.ofFn entries) = selectFunction p entries := by
  unfold select
  congr 1
  funext i
  exact SurjectiveConfidenceCertificate.getD_ofFn entries i (p.problem.x0, 0)

lemma measurable_selectFunction (p : Params) (hp : spec.valid p) :
    Measurable (selectFunction p) := by
  have hi : Measurable (selectedIndex p) :=
    (AdaptiveHeavyTailSimplex.measurable_minimumIndex _).comp
      (Measurable.of_eval (fun i =>
        ((continuous_modelStep p.problem hp.1).measurable.comp (measurable_pi_apply i).snd).norm))
  have he : Measurable (fun entries : Fin (replicas p) → p.problem.E × Primitive p.problem =>
      entries (selectedIndex p entries)) :=
    (measurable_from_prod_countable_left
      (f := fun w : (Fin (replicas p) → p.problem.E × Primitive p.problem) × Fin (replicas p) =>
        w.1 w.2) (fun i => measurable_pi_apply i)).comp
      (measurable_id.prodMk hi)
  exact he.fst.prodMk ((measurable_dualPoint p.problem hp.1).comp he.snd)

lemma selection_accurate (p : Params) (hp : spec.valid p) (I : Problem p.problem)
    (H : Regularity p.problem I)
    (entries : Fin (replicas p) → p.problem.E × Primitive p.problem)
    (hg : ∃ i, ‖exactModelStep p.problem I (entries i).1‖ ≤ radius p.problem / 8)
    (he : ∀ i, ‖jointEquiv p.problem (entries i).2 - jointMean p.problem I (entries i).1‖ ≤
      certificateError p.problem / 4) :
    accurate p.problem I (selectFunction p entries) := by
  obtain ⟨j, hj⟩ := hg
  apply SurjectiveConfidenceSelection.selected_accurate p.problem I hp.1 H
    (fun i => (entries i).1) (fun i => (entries i).2) (selectedIndex p entries) j
  · intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (he i) 2
    simpa only [jointMean, jointEquiv_sub_norm_sq] using h
  · exact hj
  · exact AdaptiveHeavyTailSimplex.minimumIndex_le (by unfold replicas; omega)
      (fun i : Fin (replicas p) => ‖modelStep p.problem (entries i).2‖) j

end LongTails.Proofs.SurjectiveConfidenceOutput
