import LongTails.Algorithms.DashaDistributedSelection
import LongTails.Proofs.DashaDistributedNormalization
import LongTails.Proofs.DashaScalingIdle
import LongTails.Proofs.DashaDistributedTracked

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedSelection

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedNormalization
open LongTails.Algorithms.DashaDistributedSelection

variable {p : Params}

lemma selected_le (p : Params) (candidate : Candidate p) :
    candidateCost p (selected p) ≤ candidateCost p candidate := by
  classical
  exact (Classical.choose_spec (Finset.univ.exists_min_image (candidateCost p) Finset.univ_nonempty)).2
    candidate (Finset.mem_univ candidate)

lemma selected_inf (p : Params) :
    candidateCost p (selected p) = Finset.univ.inf' Finset.univ_nonempty (candidateCost p) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro candidate _
    exact selected_le p candidate
  · exact Finset.inf'_le _ (Finset.mem_univ (selected p))

lemma idle_success (hp : spec.valid p) (f : Functions p)
    (hO : spec.admissible p f (system p f))
    (hcert : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2) :
    spec.successful p f (fun ω => execute (system p f) (idle p) 0 ω.1 ω.2) (law (system p f) (idle p)) := by
  obtain ⟨_, hL, hH, _, _, _⟩ := hp
  obtain ⟨_, hg, hlip, hs, hG, lower, hlower, hgap⟩ := hO
  have hacc := DashaScalingDescent.initial_gradient_certificate
    (DashaScalingDescent.initial_gradient_gap f hg hL hH hlip hs lower hlower hgap)
    (DashaScalingDescent.initial_gradient_norm f hg hG) hcert
  change Measurable (fun _ => p.x0) ∧ Integrable (fun _ => ‖gradient (objective p f) p.x0‖ ^ 2) _ ∧ _
  exact ⟨measurable_const, integrable_const _, by
    change (∫ _ : (idle p).Seed × (system p f).Seed, ‖gradient (objective p f) p.x0‖ ^ 2 ∂(law (system p f) (idle p) : Measure _)) ≤ p.ε ^ 2
    simpa using hacc⟩

lemma tuned_guarantee (hp : spec.valid p) (f : Functions p)
    (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (hO : spec.admissible p f O) :
    (∀ᵐ seed ∂(law O (tuned p) : Measure _), FiniteEvents O (tuned p) (timeBound p) seed) ∧
    spec.successful p f (fun seed => execute O (tuned p) (timeBound p) seed.1 seed.2) (law O (tuned p)) := by
  classical
  have he : O = system p f := hO.1
  subst O
  by_cases hc : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2
  · have ha : tuned p = idle p := by unfold tuned; rw [ite_eq_left hc]
    rw [ha]
    simp only [timeBound, ite_eq_left hc]
    exact ⟨Filter.Eventually.of_forall (DashaScalingIdle.idle_finiteEvents f), idle_success hp f hO hc⟩
  · have ha : tuned p = algorithm (normalize p) (chosenConfig (normalize p)) := by
      unfold tuned
      rw [ite_eq_right hc]
    rw [ha]
    simp only [timeBound, ite_eq_right hc]
    have hp' := DashaDistributedNormalization.normalized_valid hp
    have hO' := DashaDistributedNormalization.normalized_admissible hp f (system p f) hO
    exact DashaDistributedTracked.tracked_guarantee _ _ _ hp' f (system p f) hO'

end LongTails.Proofs.DashaDistributedSelection
