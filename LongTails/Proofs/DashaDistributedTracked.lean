import LongTails.Proofs.DashaDistributedTrackingCapacity
import LongTails.Proofs.DashaDistributedConfigured

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedTracked

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters
open LongTails.Proofs.DashaDistributedExecution

variable {p : Params}

lemma tracked_transport (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG0 : 0 ≤ p.G) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (seed : ℕ → Sample p) : TransportExact (trackedConfig p c initializer modularInitialization) f seed := by
  apply DashaDistributedTrackingCapacity.transportExact (trackedConfig p c initializer modularInitialization)
    hε hL hH hG0 f hg hs hG hJ
  · rfl
  · rfl
  · rfl

lemma tracked_trajectory (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) :
    idealTrajectory p (trackedConfig p c initializer modularInitialization) f seed k =
      idealTrajectory p (config p c initializer) f seed k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun s => nextIterate p c f s (seed (k + 1))) ih

lemma tracked_output (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (f : Functions p) :
    idealOutput p (trackedConfig p c initializer modularInitialization) f = idealOutput p (config p c initializer) f := by
  funext seed
  exact congrArg (fun s : Iterate p => s.point) (tracked_trajectory c initializer modularInitialization f seed.2 seed.1.val)

lemma tracked_guarantee (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hp : spec.valid p) (f : Functions p)
    (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (hO : spec.admissible p f O) :
    (∀ᵐ seed ∂(law O (algorithm p (trackedConfig p c initializer modularInitialization)) : Measure _),
      FiniteEvents O (algorithm p (trackedConfig p c initializer modularInitialization))
        (timeBudget p (trackedConfig p c initializer modularInitialization)) seed) ∧
    spec.successful p f
      (fun seed => execute O (algorithm p (trackedConfig p c initializer modularInitialization))
        (timeBudget p (trackedConfig p c initializer modularInitialization)) seed.1 seed.2)
      (law O (algorithm p (trackedConfig p c initializer modularInitialization))) := by
  have ho := hO.1
  subst O
  obtain ⟨hpos, hL, hH, _, hG0, hε⟩ := hp
  obtain ⟨_, hg, hlip, hs, hG, lower, hlower, hgap⟩ := hO
  let cfg := trackedConfig p c initializer modularInitialization
  have hJ := DashaDistributedTrackingCapacity.initial_global_bound hL hH f hg hlip hs hG lower hlower hgap
  have hx (seed : ℕ → Sample p) : TransportExact cfg f seed :=
    tracked_transport c initializer modularInitialization hε hL hH hG0 f hg hs hG hJ seed
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · rcases seed with ⟨⟨selected, stream⟩, u⟩
    cases u
    exact DashaDistributedTermination.finiteEvents cfg f stream selected (hx stream) hpos
  · have he : (fun seed : (algorithm p cfg).Seed × (system p f).Seed =>
        execute (system p f) (algorithm p cfg) (timeBudget p cfg) seed.1 seed.2) =
        fun seed => idealOutput p cfg f seed.1 := by
      funext seed
      rcases seed with ⟨⟨selected, stream⟩, u⟩
      cases u
      exact DashaDistributedTermination.execute_eq_ideal cfg f stream selected (hx stream) hpos
    change Measurable _ ∧ Integrable _ _ ∧ _
    erw [he]
    have hout := tracked_output c initializer modularInitialization f
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

end LongTails.Proofs.DashaDistributedTracked
