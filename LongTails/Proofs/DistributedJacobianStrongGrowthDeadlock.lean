import LongTails.Proofs.DistributedJacobianStrongGrowthTerminalWaits
import LongTails.Proofs.DistributedJacobianStrongGrowthEpochExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthDeadlock

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthLiveShape
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTerminalWaits
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma finishLocal_unsent (p : Params) (s : State p) (x : Point p) (h : s.sent = false) :
    (finishLocal p s x).sent = false := by
  cases hs : s.phase <;> simp [finishLocal, hs, startMedian, h]

lemma finishBroadcast_unsent (p : Params) (s : State p) (values : Fin p.d → ℕ) (h : s.sent = false) :
    (finishBroadcast p s values).sent = false := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · rfl
      · unfold startRefinement
        split_ifs <;> rfl
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      unfold startRefinement
      split_ifs <;> rfl

lemma rootUnsent_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : Event (Point p) (CommReply p)) (h : v = p.root → s.sent = false) :
    v = p.root → (update p v s notification).sent = false := by
  intro hv
  subst v
  have hh := h rfl
  cases notification with
  | wake => exact hh
  | computed value =>
      cases hw : s.work <;> cases hb : s.busy <;> simp [update, hw, hb, hh]
  | received message => simp [update, hh]

lemma rootUnsent_query (p : Params) (v : Fin p.n) (s : State p) (h : v = p.root → s.sent = false) :
    v = p.root → (query p v s).2.sent = false := by
  intro hv
  subst v
  have hh := h rfl
  cases hqueue : s.queue with
  | cons packet rest => simpa [query, hqueue] using hh
  | nil =>
      cases hw : s.work with
      | some work =>
          cases hb : s.busy with
          | true => simpa [query, hqueue, hw, hb] using hh
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some x => simpa [query, hqueue, hw, hb, hquery] using hh
              | none =>
                  simpa [query, hqueue, hw, hb, hquery] using finishLocal_unsent p s
                    (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hh
      | none =>
          by_cases hr : s.ready ∧ ¬ s.sent ∧ children p p.root ⊆ s.collector.seen
          · simpa [query, hqueue, hw, hr, relay] using finishBroadcast_unsent p s
              (broadcastValues p s.phase (fun j => s.own j + s.collector.total j)) hh
          · simpa only [query, hqueue, hw, ite_eq_right hr] using hh

lemma rootUnsent_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, v = p.root → (c.workers v).sent = false) :
    ∀ v, v = p.root → ((run (system p g S) (algorithm p idle) k c).workers v).sent = false := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using h
      | some next =>
          have hn := workerPredicate_step p g S idle (fun v s => v = p.root → s.sent = false)
            (rootUnsent_update p)
            (fun v s next action h hq => by simpa only [hq] using rootUnsent_query p v s h) c next h hs
          simpa only [run, hs] using ih next hn

lemma rootUnsent_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) :
    ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers p.root).sent = false := by
  apply rootUnsent_run p g S idle k _ ?_ p.root rfl
  intro v _
  change (initialState p v).sent = false
  unfold initialState
  split_ifs <;> rfl

lemma active_epoch_lt_final (p : Params) (phase : Phase) (hb : PhaseBounds p phase)
    (ha : DistributedJacobianStrongGrowthPhases.Active phase) :
    epochIndex p phase < warmWidth p (localDepth p) + refinementCount p (localDepth p) := by
  cases phase <;> simp_all only [DistributedJacobianStrongGrowthPhases.Active, PhaseBounds, epochIndex]
  all_goals omega

lemma empty_terminal_root_done (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none)
    (hpark : Parked p g S idle c) (hlive : ∀ v, LiveShape p (c.workers v))
    (hmatch : ∀ v, DistributedJacobianStrongGrowthExecution.PendingMatches p (c.workers v) (c.oracle.computation v))
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p c.workers c.oracle.communication)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p c.workers c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v)) (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hroot : (c.workers p.root).sent = false)
    (hcompute : ∀ v, (c.oracle.computation v).pending = none)
    (hnetwork : ∀ source target, c.oracle.communication.messages source target = none) :
    (c.workers p.root).phase = .done := by
  classical
  have hqueries : ∀ v, (query p v (c.workers v)).1 = .advance 1 :=
    fun v => hpark v (noEvent_wake p g S idle c he v)
  have hqueues : ∀ v, (c.workers v).queue = [] := fun v => (query_park_data p v (c.workers v) (hqueries v)).1
  have hwork : ∀ v, (c.workers v).work = none := by
    intro v
    cases hw : (c.workers v).work with
    | none => rfl
    | some work =>
        have hb := (query_park_data p v (c.workers v) (hqueries v)).2.1 work hw
        have hm := (hmatch v).1
        simp [hcompute v, hb] at hm
  have hdesc : ∀ r, ∀ v : Fin p.n, p.h - p.depth v = r →
      (c.workers v).phase ≠ .done → (c.workers v).sent = false → False := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro v hr hn hsent
      have hready := liveShape_unfinished p (c.workers v) (hlive v) hn (hwork v)
      have hmissing : ¬ children p v ⊆ (c.workers v).collector.seen := by
        intro hf
        exact (query_park_data p v (c.workers v) (hqueries v)).2.2 (hwork v)
          ⟨hready, by simp [hsent], hf⟩
      obtain ⟨child, hchild, hnot⟩ := Finset.not_subset.mp hmissing
      have hc : child ≠ p.root ∧ p.parent child = v := (Finset.mem_filter.mp hchild).2
      have hchildsent : (c.workers child).sent = false := by
        have hb := hh child hc.1
        cases hs : (c.workers child).sent with
        | false => rfl
        | true =>
            simp [DistributedJacobianStrongGrowthHandshake.edgeLoad, hnetwork, hqueues, hc.2, hnot, hs] at hb
      have hchildindex := ho child hc.1
      simp only [DistributedJacobianStrongGrowthEpochOrdering.downLoad, hqueues, List.countP_nil,
        hnetwork, Option.isSome_none, Bool.toNat_false, Nat.add_zero, hc.2] at hchildindex
      have hindex := active_epoch_lt_final p (c.workers v).phase (hbounds v)
        ((hroute v).1.2.1 (Or.inl hready))
      have hchildnot : (c.workers child).phase ≠ .done := by
        intro hd
        rw [hd, epochIndex] at hchildindex
        omega
      have hdepth := hp.2.2.2.1 child hc.1
      rw [hc.2] at hdepth
      have hbound := hp.2.2.2.2.1 child
      exact ih (p.h - p.depth child) (by omega) child rfl hchildnot hchildsent
  by_contra hn
  exact hdesc (p.h - p.depth p.root) p.root rfl hn hroot

end LongTails.Proofs.DistributedJacobianStrongGrowthDeadlock
