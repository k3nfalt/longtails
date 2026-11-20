import LongTails.Proofs.DistributedJacobianStrongGrowthEpochExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthQueryAccounting

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning

def workRemaining (p : Params) (s : State p) : ℕ :=
  match s.work with
  | none => 0
  | some work => LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries work

noncomputable def targetQueries (p : Params) : Phase → ℕ
  | .baseline => baselineCount p
  | .warming => warmCount p (localDepth p)
  | .median _ => warmCount p (localDepth p)
  | .refinement epoch => warmCount p (localDepth p) + 2 * localDepth p * (epoch + 1)
  | .done => warmCount p (localDepth p) + 2 * localDepth p * refinementCount p (localDepth p)

def Accounted (p : Params) (s : State p) (used : ℕ) : Prop :=
  used + workRemaining p s = targetQueries p s.phase

lemma accounted_initial (p : Params) (v : Fin p.n) (hε : p.ε < p.R)
    (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) : Accounted p (initialState p v) 0 := by
  simp [Accounted, initialState, not_le.mpr hε, hrich, workRemaining, targetQueries,
    LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries]

lemma accounted_startRefinement (p : Params) (s : State p) (epoch used : ℕ)
    (he : epoch ≤ refinementCount p (localDepth p))
    (hu : used = warmCount p (localDepth p) + 2 * localDepth p * epoch) :
    Accounted p (startRefinement p epoch s) used := by
  unfold startRefinement
  split_ifs with hk
  · simp [Accounted, workRemaining, targetQueries,
      LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries, hu, Nat.mul_add, Nat.add_assoc]
  · have hh : epoch = refinementCount p (localDepth p) := by omega
    simp [Accounted, workRemaining, targetQueries, hu, hh]

lemma accounted_startMedian (p : Params) (s : State p) (remaining used : ℕ)
    (hu : used = warmCount p (localDepth p)) : Accounted p (startMedian p remaining s) used := by
  simp [Accounted, startMedian, workRemaining, targetQueries, hu]

lemma accounted_reply (p : Params) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (h : Accounted p s used) :
    Accounted p { s with work := some (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value), busy := false }
      (used + 1) := by
  have hd := DistributedJacobianStrongGrowthWorker.reply_decreases p work value point hq
  simp only [Accounted, workRemaining, hs] at h
  simp only [Accounted, workRemaining]
  omega

lemma accounted_finishLocal (p : Params) (s : State p) (used : ℕ) (x : Point p)
    (h : Accounted p s used) (hz : workRemaining p s = 0) (hn : s.phase ≠ .baseline) :
    Accounted p (finishLocal p s x) used := by
  have hu : used = targetQueries p s.phase := by simpa only [Accounted, hz, Nat.add_zero] using h
  cases hs : s.phase with
  | baseline => exact False.elim (hn hs)
  | warming =>
      simpa [finishLocal, hs, Accounted, startMedian, workRemaining, targetQueries] using hu
  | median remaining => simpa [finishLocal, hs, Accounted, workRemaining, targetQueries] using hu
  | refinement epoch => simpa [finishLocal, hs, Accounted, workRemaining, targetQueries] using hu
  | done => simpa [finishLocal, hs, Accounted, workRemaining, targetQueries] using hu

lemma accounted_finishBroadcast (p : Params) (s : State p) (used : ℕ) (values : Fin p.d → ℕ)
    (h : Accounted p s used) (hw : s.work = none)
    (hb : DistributedJacobianStrongGrowthPhaseProgress.PhaseBounds p s.phase) :
    Accounted p (finishBroadcast p s values) used := by
  have hu : used = targetQueries p s.phase := by simpa [Accounted, workRemaining, hw] using h
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      have he : epoch < refinementCount p (localDepth p) := by simpa [DistributedJacobianStrongGrowthPhaseProgress.PhaseBounds, hs] using hb
      simp only [finishBroadcast, hs]
      apply accounted_startRefinement p _ (epoch + 1) used (by omega)
      simpa [targetQueries, hs] using hu
  | median remaining =>
      have he : used = warmCount p (localDepth p) := by simpa [targetQueries, hs] using hu
      simp only [finishBroadcast, hs]
      split_ifs
      · exact accounted_startMedian p _ _ used he
      · apply accounted_startRefinement p _ 0 used (Nat.zero_le _)
        simpa using he

lemma accounted_relay (p : Params) (v : Fin p.n) (s : State p) (used : ℕ) (values : Fin p.d → ℕ)
    (h : Accounted p s used) (hw : s.work = none)
    (hb : DistributedJacobianStrongGrowthPhaseProgress.PhaseBounds p s.phase) :
    Accounted p (relay p v s values) used := accounted_finishBroadcast p s used values h hw hb

lemma accounted_query (p : Params) (v : Fin p.n) (s : State p) (used : ℕ)
    (h : Accounted p s used) (hn : s.phase ≠ .baseline)
    (hb : DistributedJacobianStrongGrowthPhaseProgress.PhaseBounds p s.phase) :
    Accounted p (query p v s).2 used := by
  cases hqueue : s.queue with
  | cons packet rest => simpa [query, hqueue, Accounted, workRemaining] using h
  | nil =>
      cases hw : s.work with
      | none =>
          simp only [query, hqueue, hw]
          split_ifs
          · exact accounted_relay p v s used _ h hw hb
          · simpa [Accounted, workRemaining, hw] using h
          · exact h
      | some work =>
          cases hbusy : s.busy with
          | true => simpa [query, hqueue, hw, hbusy] using h
          | false =>
              cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some x => simpa [query, hqueue, hw, hbusy, hq, Accounted, workRemaining] using h
              | none =>
                  have hz : workRemaining p s = 0 := by
                    simpa [workRemaining, hw] using (DistributedJacobianStrongGrowthWorker.query_none_iff p work).mp hq
                  simpa [query, hqueue, hw, hbusy, hq] using accounted_finishLocal p s used _ h hz hn

lemma accounted_computed (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (i : Fin p.n) (worker : State p) (oracle next : ComputationState p)
    (time : DistributedTemplate.Time) (value : Point p)
    (hm : DistributedJacobianStrongGrowthExecution.PendingMatches p worker oracle)
    (h : Accounted p worker oracle.used)
    (ha : (computation p g S).answer i oracle time = some (value, next)) :
    Accounted p (update p i worker (.computed value)) next.used := by
  obtain ⟨finish, x, hpending, _, _, hnext⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value ha
  obtain ⟨work, hwork, hq⟩ := hm.2 finish x hpending
  have hbusy : worker.busy = true := by simpa only [hpending, Option.isSome_some] using hm.1.symm
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p i worker work value hwork hbusy, hnext]
  exact accounted_reply p worker oracle.used work x value hwork hq h

lemma accounted_received (p : Params) (v : Fin p.n) (s : State p) (used : ℕ) (message : CommReply p)
    (h : Accounted p s used)
    (hb : DistributedJacobianStrongGrowthPhaseProgress.PhaseBounds p s.phase)
    (hparent : v ≠ p.root ∧ message.source = p.parent v → s.work = none) :
    Accounted p (update p v s (.received message)) used := by
  simp only [update]
  split_ifs with hp
  · exact accounted_relay p v s used _ h (hparent hp) hb
  · exact h

open DistributedTemplate
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthPhaseProgress

lemma accounted_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hm : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hnetwork : Handshake p c.workers c.oracle.communication)
    (hb : ∀ v, PhaseBounds p (c.workers v).phase)
    (hr : ∀ v, RoutingShape p v (c.workers v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    ∀ v, Accounted p (Function.update c.workers i (update p i (c.workers i) notification) v)
      (next.computation v).used := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      intro v
      by_cases hv : v = i <;> simp_all [Function.update, update]
  | computed value =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        exact accounted_computed p g S i (c.workers i) (c.oracle.computation i) oracle c.time value (hm i) (h i) ha
      · simpa [Function.update, hv] using h v
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        apply accounted_received p i (c.workers i) (c.oracle.computation i).used message (h i) (hb i)
        intro hp
        obtain ⟨finish, hstored, _, _⟩ :=
          DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
            c.time message.source i message.bits ha
        have hs := down_pending_sent p c.workers c.oracle.communication hnetwork i hp.1 finish message.bits
          (by simpa only [hp.2] using hstored)
        exact ((hr i).1.1 (Or.inr hs)).1
      · simpa [Function.update, hv] using h v

lemma computation_submit_used (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (i : Fin p.n) (oracle : ComputationState p) (time : Time) (x : Point p) :
    ((computation p g S).submit i oracle time x).used = oracle.used := by
  cases hp : oracle.pending <;> simp [computation, hp]

lemma accounted_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hm : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hnetwork : Handshake p c.workers c.oracle.communication)
    (hb : ∀ v, PhaseBounds p (c.workers v).phase)
    (hr : ∀ v, RoutingShape p v (c.workers v))
    (hno : ∀ v, (c.workers v).phase ≠ .baseline)
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, Accounted p (next.workers v) (next.oracle.computation v).used := by
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
          have hh := Option.some.inj hs
          subst next
          exact h
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        have hn := accounted_notification p g S idle c i notification oracle h hm hnetwork hb hr he
        have hi : Accounted p (update p i (c.workers i) notification) (oracle.computation i).used := by
          simpa [Function.update] using hn i
        have hqa := accounted_query p i (update p i (c.workers i) notification) (oracle.computation i).used hi
          (noBaseline_update p i (c.workers i) notification (hno i))
          (phaseBounds_update p i (c.workers i) notification (hb i))
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            rw [hq] at hqa
            simp only [algorithm, hq] at hs
            cases action with
            | compute x =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  cases hpending : (oracle.computation i).pending <;>
                    simpa [Function.update, system, algorithm, computation, hpending] using hqa
                · simpa [Function.update, hv, algorithm] using hn v
            | communicate packet =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  simpa [Function.update, algorithm] using hqa
                · simpa [Function.update, hv, algorithm] using hn v
            | advance code =>
                dsimp only at hs
                have hh := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  simpa [Function.update, algorithm] using hqa
                · simpa [Function.update, hv, algorithm] using hn v

lemma accounted_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    ∀ v, Accounted p ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers v)
      ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).oracle.computation v).used := by
  induction k with
  | zero => exact fun v => accounted_initial p v hε hrich
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change ∀ v, Accounted p ((run (system p g S) (algorithm p idle) 1 c).workers v)
        ((run (system p g S) (algorithm p idle) 1 c).oracle.computation v).used
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using ih
      | some next =>
          have hh := accounted_step p g S idle c next ih
            (fun v => DistributedJacobianStrongGrowthNetworkExecution.pending_initial_run p hp g S idle deadline seed k v)
            (DistributedJacobianStrongGrowthNetworkExecution.network_initial_run p hp g S idle deadline seed k).1
            (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
            (fun v => routingShape_initial_run p g S idle deadline seed k v)
            (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich) hs
          simpa only [run, hs] using hh

end LongTails.Proofs.DistributedJacobianStrongGrowthQueryAccounting
