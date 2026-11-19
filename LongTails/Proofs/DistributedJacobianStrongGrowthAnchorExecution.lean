import LongTails.Proofs.DistributedJacobianStrongGrowthAnchorNotification

namespace LongTails.Proofs.DistributedJacobianStrongGrowthAnchorExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianNotification
open DistributedJacobianStrongGrowthMedianExecution
open DistributedJacobianStrongGrowthAnchorState
open DistributedJacobianStrongGrowthAnchorNotification
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthEpochExecution

lemma anchorState_step (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, AnchorState p (medianCenter p codes) (c.workers v))
    (hcontent : MedianContent p codes c.workers c.oracle.communication)
    (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hno : ∀ v, (c.workers v).phase ≠ .baseline)
    (hcodes : ∀ v, (c.workers v).phase ≠ .warming →
      (c.workers v).warmCodes = fun j => (codes v j).val)
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, AnchorState p (medianCenter p codes) (next.workers v) := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate] at hs
    cases he : event (system p g S) (algorithm p idle) c c.time with
    | none =>
        rw [he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hstate := Option.some.inj hs
          subst next
          exact h
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        let updated : Fin p.n → State p := Function.update c.workers i (update p i (c.workers i) notification)
        have han := anchorState_notification p hp g S idle codes c i notification oracle h hcontent hbounds he
        have hcn := medianContent_notification p hp g S idle codes c i notification oracle hcontent hh ho hedges
          hroute hbounds hno hcodes he
        have hbu : PhaseBounds p (updated i).phase := by
          simpa [updated, Function.update, algorithm] using phaseBounds_update p i (c.workers i) notification (hbounds i)
        have hnu : (updated i).phase ≠ .baseline := by
          simpa [updated, Function.update, algorithm] using noBaseline_update p i (c.workers i) notification (hno i)
        have hqa := anchorState_query p hp codes updated oracle.communication hcn i (han i) hbu hnu
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            have hqu : query p i (updated i) = (action, worker) := by simpa [updated, Function.update] using hq
            rw [hqu] at hqa
            simp only [algorithm, hq] at hs
            cases action <;> dsimp only at hs <;> have hstate := Option.some.inj hs <;> subst next
            all_goals
              intro v
              by_cases hv : v = i
              · subst v
                simpa [Function.update, algorithm] using hqa
              · simpa [Function.update, hv, algorithm] using han v

lemma anchorState_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    ∀ v, AnchorState p
      (medianCenter p (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCodes p
        (warmCount p (localDepth p)) (warmWidth p (localDepth p)) (warmSpacing p (localDepth p))
        g (fun j => S.sample j seed.2)))
      ((run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)).workers v) := by
  induction k with
  | zero => exact fun v => anchorState_initial p _ v hε hrich
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change ∀ v, AnchorState p _ ((run (system p g S) (algorithm p idle) 1 c).workers v)
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using ih
      | some next =>
          have hh := anchorState_step p hp g S idle _ c next ih
            (medianContent_initial_run p hp g S idle deadline seed k hε hrich)
            (network_initial_run p hp g S idle deadline seed k).1
            (epochOrdering_initial_run p hp g S idle deadline seed k hε hrich)
            (network_initial_run p hp g S idle deadline seed k).2
            (fun v => routingShape_initial_run p g S idle deadline seed k v)
            (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
            (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich)
            (fun v hn => (DistributedJacobianStrongGrowthWarmReference.warmReference_initial_run
              p hp g S idle deadline seed k hε hrich v).2 hn) hs
          simpa only [run, hs] using hh

end LongTails.Proofs.DistributedJacobianStrongGrowthAnchorExecution
