import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementNotification
import LongTails.Proofs.DistributedJacobianStrongGrowthAnchorExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianQuery
open DistributedJacobianStrongGrowthMedianNotification
open DistributedJacobianStrongGrowthWarmReference
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthEpochExecution

open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementQuery
open DistributedJacobianStrongGrowthRefinementNotification
open DistributedJacobianStrongGrowthAnchorState
open DistributedJacobianStrongGrowthAnchorNotification

lemma refinementContent_step (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (samples : ℕ → p.Ω) (idle : Time)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hcodes : codes = LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCodes p
      (warmCount p (localDepth p)) (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : RefinementContent p g samples c.workers c.oracle.communication)
    (hmedian : MedianContent p codes c.workers c.oracle.communication)
    (hanchor : ∀ v, AnchorState p (medianCenter p codes) (c.workers v))
    (hwarm : ∀ v, WarmReference p g samples v (c.workers v) (c.oracle.computation v).used)
    (ha : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hm : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hsamples : ∀ v, (c.oracle.computation v).samples = samples)
    (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hno : ∀ v, (c.workers v).phase ≠ .baseline)
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    RefinementContent p g samples next.workers next.oracle.communication := by
  classical
  have hc : ∀ v, (c.workers v).phase ≠ .warming →
      (c.workers v).warmCodes = fun j => (codes v j).val := by
    intro v hn
    rw [hcodes]
    exact (hwarm v).2 hn
  have hcenter : medianCenter p codes = refinementPoint p g samples 0 := by
    rw [hcodes]
    rfl
  have hanchorWarm : ∀ v epoch, (c.workers v).phase = .refinement epoch →
      (c.workers v).anchor = LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCenter p
        (warmCount p (localDepth p)) (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples := by
    intro v epoch he
    have ha' : (c.workers v).anchor = medianCenter p codes := by
      simpa only [AnchorState, he] using hanchor v
    exact ha'.trans hcenter
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
        have hu : ∀ v, RoutingShape p v (updated v) := by
          intro v
          by_cases hv : v = i
          · subst v
            simpa [updated, Function.update] using routingShape_update p i (c.workers i) notification (hroute i)
          · simpa [updated, Function.update, hv] using hroute v
        have hbu : ∀ v, PhaseBounds p (updated v).phase := by
          intro v
          by_cases hv : v = i
          · subst v
            simpa [updated, Function.update, algorithm] using phaseBounds_update p i (c.workers i) notification (hbounds i)
          · simpa [updated, Function.update, hv] using hbounds v
        have hnu : (updated i).phase ≠ .baseline := by
          simpa [updated, Function.update, algorithm] using noBaseline_update p i (c.workers i) notification (hno i)
        have hhu := handshake_notification p hp g S idle c i notification oracle hh hedges hroute he
        have hou := epochOrdering_notification p hp g S idle c i notification oracle hh ho hbounds hedges hroute he
        have hmedianu := medianContent_notification p hp g S idle codes c i notification oracle hmedian hh ho hedges
          hroute hbounds hno hc he
        have hcontent := refinementContent_notification p hp g S samples idle codes c i notification oracle h hmedian
          hcenter hanchorWarm ha hm hsamples hh ho hedges hroute hbounds he
        have hanchoru := anchorState_notification p hp g S idle codes c i notification oracle hanchor hmedian hbounds he
        have hanchorNext : ∀ v epoch, (updated v).phase = .refinement epoch →
            (updated v).anchor = LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCenter p
              (warmCount p (localDepth p)) (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples := by
          intro v epoch he'
          have ha' : AnchorState p (medianCenter p codes) (updated v) := hanchoru v
          have heq : (updated v).anchor = medianCenter p codes := by
            simpa only [AnchorState, he'] using ha'
          exact heq.trans hcenter
        have hqall := refinementContent_query p hp S g samples codes updated oracle.communication hcontent hmedianu
          hcenter hanchorNext hhu hou hu hbu i c.time hnu
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            have hqu : query p i (updated i) = (action, worker) := by simpa [updated, Function.update] using hq
            rw [hqu] at hqall
            have hup : Function.update updated i worker = Function.update c.workers i worker := by
              funext v
              by_cases hv : v = i <;> simp [updated, Function.update, hv, algorithm]
            erw [hup] at hqall
            simp only [algorithm, hq] at hs
            cases action with
            | compute x =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                simpa [algorithm, system] using hqall
            | communicate packet =>
                rcases packet with ⟨target, bits⟩
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                simpa [algorithm, system] using hqall
            | advance code =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                simpa [algorithm, system] using hqall

lemma refinementContent_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    RefinementContent p g (fun j => S.sample j seed.2)
      (run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)).workers
      (run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)).oracle.communication := by
  induction k with
  | zero => exact refinementContent_initial p S seed.2 g _ hε hrich
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change RefinementContent p g (fun j => S.sample j seed.2) (run (system p g S) (algorithm p idle) 1 c).workers
        (run (system p g S) (algorithm p idle) 1 c).oracle.communication
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using ih
      | some next =>
          have hh := refinementContent_step p hp g S (fun j => S.sample j seed.2) idle _ rfl c next ih
            (DistributedJacobianStrongGrowthMedianExecution.medianContent_initial_run p hp g S idle deadline seed k hε hrich)
            (DistributedJacobianStrongGrowthAnchorExecution.anchorState_initial_run p hp g S idle deadline seed k hε hrich)
            (warmReference_initial_run p hp g S idle deadline seed k hε hrich)
            (accounted_initial_run p hp g S idle deadline seed k hε hrich)
            (fun v => pending_initial_run p hp g S idle deadline seed k v)
            (fun v => DistributedJacobianStrongGrowthSampleReference.samples_initial_run p g S idle deadline seed k v)
            (network_initial_run p hp g S idle deadline seed k).1
            (epochOrdering_initial_run p hp g S idle deadline seed k hε hrich)
            (network_initial_run p hp g S idle deadline seed k).2
            (fun v => routingShape_initial_run p g S idle deadline seed k v)
            (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
            (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich) hs
          simpa only [run, hs] using hh

lemma refinement_done_current (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hdone : ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers v).phase = .done) :
    ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers v).current =
      output p (localDepth p) g (fun j => S.sample j seed.2) :=
  ((refinementContent_initial_run p hp g S idle deadline seed k hε hrich).states v).2 hdone

lemma refinement_execute_of_terminal (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hterminal : step (system p g S) (algorithm p idle)
      (run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)) = none)
    (hdone : ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers p.root).phase = .done) :
    execute (system p g S) (algorithm p idle) deadline seed.1 seed.2 =
      output p (localDepth p) g (fun j => S.sample j seed.2) := by
  rw [DistributedExecution.execute_eq_terminal (system p g S) (algorithm p idle) deadline seed k hterminal]
  exact refinement_done_current p hp g S idle deadline seed k p.root hε hrich hdone

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementExecution
