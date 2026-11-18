import LongTails.Algorithms.DashaDistributedDeadline
import LongTails.Proofs.DashaDistributedSelection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedDeadline

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedDeadline
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters
open DashaDistributedExecution

variable {p : Params}

lemma timeBudget_atDeadline (cfg : Config p) (deadline : Time) (h : timeBudget p cfg ≤ deadline) :
    timeBudget p (atDeadline p cfg deadline) = deadline := by
  calc
    timeBudget p (atDeadline p cfg deadline) = timeBudget p cfg + (deadline - timeBudget p cfg) := by
      simp only [timeBudget, atDeadline, initialBits, roundBits]
      ring
    _ = deadline := add_tsub_cancel_of_le h

lemma trajectory_atDeadline (cfg : Config p) (deadline : Time) (f : Functions p)
    (seed : ℕ → Sample p) (k : ℕ) :
    idealTrajectory p (atDeadline p cfg deadline) f seed k = idealTrajectory p cfg f seed k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => nextIterate p cfg.choice f s (seed (k + 1))) ih

lemma output_atDeadline (cfg : Config p) (deadline : Time) (f : Functions p) :
    idealOutput p (atDeadline p cfg deadline) f = idealOutput p cfg f := by
  funext seed
  exact congrArg (fun s : Iterate p => s.point) (trajectory_atDeadline cfg deadline f seed.2 seed.1.val)

lemma tracked_atDeadline_guarantee (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (deadline : Time) (hdeadline : timeBudget p (trackedConfig p c initializer modularInitialization) ≤ deadline)
    (hp : spec.valid p) (f : Functions p)
    (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (hO : spec.admissible p f O) :
    (∀ᵐ seed ∂(law O (algorithm p (atDeadline p (trackedConfig p c initializer modularInitialization) deadline)) : Measure _),
      FiniteEvents O (algorithm p (atDeadline p (trackedConfig p c initializer modularInitialization) deadline)) deadline seed) ∧
    spec.successful p f
      (fun seed => execute O (algorithm p (atDeadline p (trackedConfig p c initializer modularInitialization) deadline))
        deadline seed.1 seed.2)
      (law O (algorithm p (atDeadline p (trackedConfig p c initializer modularInitialization) deadline))) := by
  have ho := hO.1
  subst O
  obtain ⟨hpos, hL, hH, _, hG0, hε⟩ := hp
  obtain ⟨_, hg, hlip, hs, hG, lower, hlower, hgap⟩ := hO
  let cfg := atDeadline p (trackedConfig p c initializer modularInitialization) deadline
  have htime : timeBudget p cfg = deadline := timeBudget_atDeadline _ _ hdeadline
  have hJ := DashaDistributedTrackingCapacity.initial_global_bound hL hH f hg hlip hs hG lower hlower hgap
  have hx (seed : ℕ → Sample p) : TransportExact cfg f seed := by
    apply DashaDistributedTrackingCapacity.transportExact cfg hε hL hH hG0 f hg hs hG hJ
    · rfl
    · rfl
    · rfl
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · rcases seed with ⟨⟨selected, stream⟩, u⟩
    cases u
    change FiniteEvents (system p f) (algorithm p cfg) deadline ((selected, stream), ())
    rw [← htime]
    exact DashaDistributedTermination.finiteEvents cfg f stream selected (hx stream) hpos
  · have he : (fun seed : (algorithm p cfg).Seed × (system p f).Seed =>
        execute (system p f) (algorithm p cfg) deadline seed.1 seed.2) =
        fun seed => idealOutput p cfg f seed.1 := by
      funext seed
      rcases seed with ⟨⟨selected, stream⟩, u⟩
      cases u
      rw [← htime]
      exact DashaDistributedTermination.execute_eq_ideal cfg f stream selected (hx stream) hpos
    change Measurable _ ∧ Integrable _ _ ∧ _
    erw [he]
    have hout : idealOutput p cfg f = idealOutput p (config p c initializer) f :=
      (output_atDeadline _ _ f).trans (DashaDistributedTracked.tracked_output c initializer modularInitialization f)
    obtain ⟨hm, hi, hb⟩ := DashaDistributedConfigured.ideal_accuracy c initializer hε hL hH f hg hlip hs hG lower hlower hgap
    have hm' : Measurable (idealOutput p cfg f) := by rw [hout]; exact hm
    have hi' : Integrable (fun seed : (algorithm p cfg).Seed => ‖gradient (objective p f) (idealOutput p cfg f seed)‖ ^ 2)
        ((algorithm p cfg).law : Measure (algorithm p cfg).Seed) := by rw [hout]; exact hi
    refine ⟨hm'.comp measurable_fst, hi'.comp_fst ((system p f).law : Measure (system p f).Seed), ?_⟩
    change (∫ seed : (algorithm p cfg).Seed × (system p f).Seed,
      ‖gradient (objective p f) (idealOutput p cfg f seed.1)‖ ^ 2
      ∂(((algorithm p cfg).law : Measure (algorithm p cfg).Seed).prod ((system p f).law : Measure (system p f).Seed))) ≤ _
    have hprod := integral_fun_fst
      (μ := ((algorithm p cfg).law : Measure (algorithm p cfg).Seed))
      (ν := ((system p f).law : Measure (system p f).Seed))
      (fun seed : (algorithm p cfg).Seed => ‖gradient (objective p f) (idealOutput p cfg f seed)‖ ^ 2)
    apply hprod.le.trans
    rw [probReal_univ, one_smul, hout]
    change (∫ seed : (algorithm p (config p c initializer)).Seed,
      ‖gradient (objective p f) (idealOutput p (config p c initializer) f seed)‖ ^ 2
      ∂((algorithm p (config p c initializer)).law : Measure (algorithm p (config p c initializer)).Seed)) ≤ p.ε ^ 2
    exact hb

lemma tuned_atDeadline_guarantee (deadline : Time) (hp : spec.valid p)
    (hzero : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 → deadline = 0)
    (hdeadline : LongTails.Algorithms.DashaDistributedSelection.timeBound p ≤ deadline)
    (f : Functions p) (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (hO : spec.admissible p f O) :
    (∀ᵐ seed ∂(law O (tunedAtDeadline p deadline) : Measure _),
      FiniteEvents O (tunedAtDeadline p deadline) deadline seed) ∧
    spec.successful p f
      (fun seed => execute O (tunedAtDeadline p deadline) deadline seed.1 seed.2)
      (law O (tunedAtDeadline p deadline)) := by
  classical
  have he : O = system p f := hO.1
  subst O
  by_cases hc : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2
  · have ha : tunedAtDeadline p deadline = idle p := by
      unfold tunedAtDeadline
      rw [ite_eq_left hc]
    rw [ha, hzero hc]
    exact ⟨Filter.Eventually.of_forall (DashaScalingIdle.idle_finiteEvents f),
      DashaDistributedSelection.idle_success hp f hO hc⟩
  · have ha : tunedAtDeadline p deadline =
        algorithm (LongTails.Algorithms.DashaDistributedNormalization.normalize p)
          (atDeadline (LongTails.Algorithms.DashaDistributedNormalization.normalize p)
            (LongTails.Algorithms.DashaDistributedSelection.chosenConfig
              (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) deadline) := by
      unfold tunedAtDeadline
      rw [ite_eq_right hc]
    rw [ha]
    have hp' := DashaDistributedNormalization.normalized_valid hp
    have hO' := DashaDistributedNormalization.normalized_admissible hp f (system p f) hO
    have hb : timeBudget (LongTails.Algorithms.DashaDistributedNormalization.normalize p)
        (LongTails.Algorithms.DashaDistributedSelection.chosenConfig
          (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) ≤ deadline := by
      simpa only [LongTails.Algorithms.DashaDistributedSelection.timeBound, ite_eq_right hc,
        LongTails.Algorithms.DashaDistributedSelection.chosenConfig,
        LongTails.Algorithms.DashaDistributedSelection.candidateCost] using hdeadline
    exact tracked_atDeadline_guarantee _ _ _ deadline hb hp' f (system p f) hO'

end LongTails.Proofs.DashaDistributedDeadline
