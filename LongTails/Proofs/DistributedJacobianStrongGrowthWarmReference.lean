import LongTails.Proofs.DistributedJacobianStrongGrowthSampleReference

namespace LongTails.Proofs.DistributedJacobianStrongGrowthWarmReference

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.LocalNonlinearExtragradient

def WarmReference (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (state : State p) (used : ℕ) : Prop :=
  (state.phase = .warming → used ≤ warmCount p (localDepth p) ∧
    state.work = some (.warm (warmCount p (localDepth p) - used)
      (warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (fun k => samples (p.n * k + i.val)) used))) ∧
  (state.phase ≠ .warming → state.warmCodes = fun j =>
    (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCodes p (warmCount p (localDepth p))
      (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples i j).val)

lemma warmReference_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (hε : p.ε < p.R)
    (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    WarmReference p g samples i (initialState p i) 0 := by
  simp [WarmReference, initialState, not_le.mpr hε, hrich, warmRun]

lemma startRefinement_warmCodes (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).warmCodes = s.warmCodes := by
  unfold startRefinement
  split_ifs <;> rfl

lemma startRefinement_not_warming (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).phase ≠ .warming := by
  unfold startRefinement
  split_ifs <;> simp

lemma finishBroadcast_warmCodes (p : Params) (s : State p) (values : Fin p.d → ℕ) :
    (finishBroadcast p s values).warmCodes = s.warmCodes := by
  cases hs : s.phase with
  | baseline => simp [finishBroadcast, hs]
  | warming => simp [finishBroadcast, hs]
  | done => simp [finishBroadcast, hs]
  | refinement epoch =>
      simp only [finishBroadcast, hs, startRefinement_warmCodes]
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · rfl
      · exact startRefinement_warmCodes _ _ _

lemma finishBroadcast_not_warming (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (hn : s.phase ≠ .warming) : (finishBroadcast p s values).phase ≠ .warming := by
  cases hs : s.phase with
  | baseline => simp [finishBroadcast, hs]
  | warming => exact False.elim (hn hs)
  | done => simp [finishBroadcast, hs]
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact startRefinement_not_warming _ _ _
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · simp [startMedian]
      · exact startRefinement_not_warming _ _ _

lemma warmReference_finishBroadcast (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) (used : ℕ) (values : Fin p.d → ℕ)
    (h : WarmReference p g samples i s used) (hw : s.work = none) :
    WarmReference p g samples i (finishBroadcast p s values) used := by
  have hn : s.phase ≠ .warming := by
    intro hs
    have hh := (h.1 hs).2
    rw [hw] at hh
    cases hh
  constructor
  · intro hs
    exact False.elim (finishBroadcast_not_warming p s values hn hs)
  · intro _
    rw [finishBroadcast_warmCodes]
    exact h.2 hn

lemma finishLocal_not_warming (p : Params) (s : State p) (x : Point p) :
    (finishLocal p s x).phase ≠ .warming := by
  cases hs : s.phase <;> simp [finishLocal, hs, startMedian]

lemma finishLocal_warmCodes (p : Params) (s : State p) (x : Point p) (hn : s.phase ≠ .warming) :
    (finishLocal p s x).warmCodes = s.warmCodes := by
  cases hs : s.phase <;> simp_all [finishLocal]

lemma warmReference_finishLocal (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : WarmReference p g samples i s used) (hw : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none) :
    WarmReference p g samples i
      (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)) used := by
  constructor
  · intro hs
    exact False.elim (finishLocal_not_warming p s _ hs)
  · intro _
    by_cases hs : s.phase = .warming
    · have hh := h.1 hs
      have he : work = .warm (warmCount p (localDepth p) - used)
          (warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (fun k => samples (p.n * k + i.val)) used) :=
        Option.some.inj (hw.symm.trans hh.2)
      subst work
      have hz := (DistributedJacobianStrongGrowthWorker.query_none_iff p _).mp hq
      simp only [LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries] at hz
      have hu : used = warmCount p (localDepth p) := by omega
      subst used
      simp [finishLocal, hs, startMedian, LongTails.Algorithms.DistributedLocalExtragradientWorker.point,
        LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCodes,
        LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmPoint]
    · rw [finishLocal_warmCodes p s _ hs]
      exact h.2 hs

lemma computed_fields (p : Params) (i : Fin p.n) (s : State p) (value : Point p) :
    (update p i s (.computed value)).phase = s.phase ∧
    (update p i s (.computed value)).warmCodes = s.warmCodes := by
  cases hw : s.work <;> cases hb : s.busy <;> simp [update, hw, hb]

lemma warmReference_computed (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p)
    (oracle next : ComputationState p) (time : DistributedTemplate.Time) (value : Point p)
    (h : WarmReference p g samples i s oracle.used)
    (ha : DistributedJacobianStrongGrowthQueryAccounting.Accounted p s oracle.used)
    (hm : DistributedJacobianStrongGrowthExecution.PendingMatches p s oracle)
    (hsamples : oracle.samples = samples)
    (hanswer : (computation p g S).answer i oracle time = some (value, next)) :
    WarmReference p g samples i (update p i s (.computed value)) next.used := by
  obtain ⟨finish, point, hpending, _, _, hnext⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value hanswer
  have hf := computed_fields p i s value
  by_cases hs : s.phase = .warming
  · have hh := h.1 hs
    obtain ⟨work, hwork, hquery⟩ := hm.2 finish point hpending
    have he := Option.some.inj (hwork.symm.trans hh.2)
    subst work
    have hu : oracle.used < warmCount p (localDepth p) := by
      by_contra hn
      have heq : oracle.used = warmCount p (localDepth p) := by omega
      rw [heq, Nat.sub_self, LongTails.Algorithms.DistributedLocalExtragradientWorker.query] at hquery
      cases hquery
    have hw := DistributedJacobianStrongGrowthSampleReference.warm_answer_work p g S i s oracle next
      oracle.used value time hs (by simpa only [hsamples] using hh.2) hu ha hm hanswer
    constructor
    · intro _
      constructor
      · rw [hnext]
        dsimp only
        omega
      · simpa only [hnext, hsamples] using hw
    · intro hn
      exact False.elim (hn (hf.1.trans hs))
  · constructor
    · intro hw
      exact False.elim (hs (hf.1.symm.trans hw))
    · intro _
      exact hf.2.trans (h.2 hs)

lemma warmReference_query (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) (used : ℕ)
    (h : WarmReference p g samples i s used) : WarmReference p g samples i (query p i s).2 used := by
  cases hqueue : s.queue with
  | cons packet rest => simpa [query, hqueue, WarmReference] using h
  | nil =>
      cases hw : s.work with
      | none =>
          simp only [query, hqueue, hw]
          split_ifs
          · exact warmReference_finishBroadcast p g samples i s used _ h hw
          · simpa [WarmReference, hw] using h
          · exact h
      | some work =>
          cases hb : s.busy with
          | true => simpa [query, hqueue, hw, hb] using h
          | false =>
              cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some point => simpa [query, hqueue, hw, hb, hq, WarmReference] using h
              | none =>
                  simpa [query, hqueue, hw, hb, hq] using warmReference_finishLocal p g samples i s used work h hw hq

lemma warmReference_received (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) (used : ℕ) (message : CommReply p)
    (h : WarmReference p g samples i s used)
    (hparent : i ≠ p.root ∧ message.source = p.parent i → s.work = none) :
    WarmReference p g samples i (update p i s (.received message)) used := by
  simp only [update]
  split_ifs with hp
  · exact warmReference_finishBroadcast p g samples i s used _ h (hparent hp)
  · exact h

open DistributedTemplate
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthQueryAccounting

lemma warmReference_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (samples : ℕ → p.Ω) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : ∀ v, WarmReference p g samples v (c.workers v) (c.oracle.computation v).used)
    (ha : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hm : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hsamples : ∀ v, (c.oracle.computation v).samples = samples)
    (hnetwork : Handshake p c.workers c.oracle.communication)
    (hr : ∀ v, RoutingShape p v (c.workers v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    ∀ v, WarmReference p g samples v
      (Function.update c.workers i (update p i (c.workers i) notification) v)
      (next.computation v).used := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      intro v
      by_cases hv : v = i <;> simp_all [Function.update, update]
  | computed value =>
      obtain ⟨oracle, hanswer, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        exact warmReference_computed p g S samples i (c.workers i) (c.oracle.computation i) oracle
          c.time value (h i) (ha i) (hm i) (hsamples i) hanswer
      · simpa [Function.update, hv] using h v
  | received message =>
      obtain ⟨oracle, hanswer, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        apply warmReference_received p g samples i (c.workers i) (c.oracle.computation i).used message (h i)
        intro hp
        obtain ⟨finish, hstored, _, _⟩ :=
          DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
            c.time message.source i message.bits hanswer
        have hs := down_pending_sent p c.workers c.oracle.communication hnetwork i hp.1 finish message.bits
          (by simpa only [hp.2] using hstored)
        exact ((hr i).1.1 (Or.inr hs)).1
      · simpa [Function.update, hv] using h v

lemma warmReference_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (samples : ℕ → p.Ω) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, WarmReference p g samples v (c.workers v) (c.oracle.computation v).used)
    (ha : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hsamples : ∀ v, (c.oracle.computation v).samples = samples)
    (hm : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hnetwork : Handshake p c.workers c.oracle.communication)
    (hr : ∀ v, RoutingShape p v (c.workers v))
    (hs : DistributedTemplate.step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, WarmReference p g samples v (next.workers v) (next.oracle.computation v).used := by
  classical
  unfold DistributedTemplate.step at hs
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
        have hn := warmReference_notification p g S samples idle c i notification oracle h ha hm hsamples hnetwork hr he
        have hi : WarmReference p g samples i (update p i (c.workers i) notification) (oracle.computation i).used := by
          simpa [Function.update] using hn i
        have hqa := warmReference_query p g samples i (update p i (c.workers i) notification) (oracle.computation i).used hi
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

lemma warmReference_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    ∀ v, WarmReference p g (fun j => S.sample j seed.2) v
      ((run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)).workers v)
      ((run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)).oracle.computation v).used := by
  induction k with
  | zero => exact fun v => warmReference_initial p g _ v hε hrich
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change ∀ v, WarmReference p g (fun j => S.sample j seed.2) v
        ((run (system p g S) (algorithm p idle) 1 c).workers v)
        ((run (system p g S) (algorithm p idle) 1 c).oracle.computation v).used
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using ih
      | some next =>
          have hh := warmReference_step p g S _ idle c next ih
            (accounted_initial_run p hp g S idle deadline seed k hε hrich)
            (fun v => DistributedJacobianStrongGrowthSampleReference.samples_initial_run p g S idle deadline seed k v)
            (fun v => DistributedJacobianStrongGrowthNetworkExecution.pending_initial_run p hp g S idle deadline seed k v)
            (DistributedJacobianStrongGrowthNetworkExecution.network_initial_run p hp g S idle deadline seed k).1
            (fun v => routingShape_initial_run p g S idle deadline seed k v) hs
          simpa only [DistributedTemplate.run, hs] using hh

end LongTails.Proofs.DistributedJacobianStrongGrowthWarmReference
