import LongTails.Proofs.DistributedJacobianStrongGrowthProtocol
import LongTails.Proofs.DistributedJacobianStrongGrowthOracle

namespace LongTails.Proofs.DistributedJacobianStrongGrowthExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

def PendingMatches (p : Params) (worker : State p) (oracle : ComputationState p) : Prop :=
  oracle.pending.isSome = worker.busy ∧
    ∀ finish x, oracle.pending = some (finish, x) →
      ∃ work, worker.work = some work ∧
        LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some x

lemma pending_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (i : Fin p.n) (seed : S.Seed) :
    PendingMatches p (initialState p i) ((computation p g S).initial i seed) := by
  constructor
  · change false = (initialState p i).busy
    unfold initialState
    split_ifs <;> rfl
  · intro finish x h
    cases h

lemma pending_submit (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (i : Fin p.n) (worker next : State p) (oracle : ComputationState p) (time : Time) (x : Point p)
    (hmatch : PendingMatches p worker oracle) (hq : query p i worker = (.compute x, next)) :
    oracle.pending = none ∧ PendingMatches p next ((computation p g S).submit i oracle time x) := by
  obtain ⟨work, _, hwork, hbusy, hquery, hnext⟩ :=
    DistributedJacobianStrongGrowthProtocol.query_compute_data p i worker next x hq
  have hnone : oracle.pending = none := by
    have hh := hmatch.1
    rw [hbusy] at hh
    cases hs : oracle.pending with
    | none => rfl
    | some pending => simp [hs] at hh
  refine ⟨hnone, ?_⟩
  rw [DistributedJacobianStrongGrowthOracle.computation_submit_idle p g S i oracle time x hnone, hnext]
  constructor
  · rfl
  · intro finish y he
    have hy : x = y := congrArg Prod.snd (Option.some.inj he)
    subst y
    exact ⟨work, hwork, hquery⟩

lemma pending_complete (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (i : Fin p.n) (worker : State p) (oracle next : ComputationState p)
    (time : Time) (value : Point p) (hmatch : PendingMatches p worker oracle)
    (ha : (computation p g S).answer i oracle time = some (value, next)) :
    PendingMatches p (update p i worker (.computed value)) next := by
  obtain ⟨finish, x, hpending, _, _, hnext⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value ha
  obtain ⟨work, hwork, _⟩ := hmatch.2 finish x hpending
  have hbusy : worker.busy = true := by simpa only [hpending, Option.isSome_some] using hmatch.1.symm
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p i worker work value hwork hbusy, hnext]
  exact ⟨rfl, by intro finish x h; cases h⟩

lemma pending_idle (p : Params) (worker : State p) (oracle : ComputationState p)
    (hbusy : worker.busy = false) (hpending : oracle.pending = none) : PendingMatches p worker oracle := by
  constructor
  · simp [hpending, hbusy]
  · intro finish x h
    rw [hpending] at h
    cases h

lemma pending_none (p : Params) (worker : State p) (oracle : ComputationState p)
    (hmatch : PendingMatches p worker oracle) (hbusy : worker.busy = false) : oracle.pending = none := by
  have hh := hmatch.1
  rw [hbusy] at hh
  cases hs : oracle.pending with
  | none => rfl
  | some pending => simp [hs] at hh

lemma pending_congr (p : Params) (worker next : State p) (oracle : ComputationState p)
    (hmatch : PendingMatches p worker oracle)
    (hbusy : next.busy = worker.busy) (hwork : next.work = worker.work) : PendingMatches p next oracle := by
  refine ⟨hmatch.1.trans hbusy.symm, ?_⟩
  intro finish x h
  obtain ⟨work, hw, hq⟩ := hmatch.2 finish x h
  exact ⟨work, hwork.trans hw, hq⟩

lemma pending_child_message (p : Params) (i : Fin p.n) (worker : State p) (oracle : ComputationState p)
    (message : CommReply p) (hmatch : PendingMatches p worker oracle)
    (hchild : ¬ (i ≠ p.root ∧ message.source = p.parent i)) :
    PendingMatches p (update p i worker (.received message)) oracle := by
  apply pending_congr p worker _ oracle hmatch <;> simp [update, hchild]

lemma finishLocal_busy (p : Params) (worker : State p) (x : Point p) :
    (finishLocal p worker x).busy = false := by
  cases hs : worker.phase <;> simp [finishLocal, hs, startMedian]

lemma startRefinement_busy (p : Params) (epoch : ℕ) (worker : State p) :
    (startRefinement p epoch worker).busy = false := by
  unfold startRefinement
  split_ifs <;> rfl

lemma finishBroadcast_busy (p : Params) (worker : State p) (values : Fin p.d → ℕ)
    (hbusy : worker.busy = false) : (finishBroadcast p worker values).busy = false := by
  cases hs : worker.phase with
  | baseline => simpa [finishBroadcast, hs] using hbusy
  | warming => simpa [finishBroadcast, hs] using hbusy
  | done => simpa [finishBroadcast, hs] using hbusy
  | refinement epoch => simp only [finishBroadcast, hs, startRefinement_busy]
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · rfl
      · exact startRefinement_busy _ _ _

lemma pending_parent_message (p : Params) (i : Fin p.n) (worker : State p) (oracle : ComputationState p)
    (message : CommReply p) (hmatch : PendingMatches p worker oracle)
    (hbusy : worker.busy = false) (hparent : i ≠ p.root ∧ message.source = p.parent i) :
    PendingMatches p (update p i worker (.received message)) oracle := by
  apply pending_idle p _ oracle
  · simp only [update, ite_eq_left hparent, relay]
    exact finishBroadcast_busy p worker _ hbusy
  · exact pending_none p worker oracle hmatch hbusy

lemma pending_no_work (p : Params) (worker : State p) (oracle : ComputationState p)
    (hmatch : PendingMatches p worker oracle) (hwork : worker.work = none) : worker.busy = false := by
  have hnone : oracle.pending = none := by
    cases hs : oracle.pending with
    | none => rfl
    | some pending =>
        obtain ⟨finish, x⟩ := pending
        obtain ⟨work, hw, _⟩ := hmatch.2 finish x hs
        rw [hwork] at hw
        cases hw
  simpa only [hnone, Option.isSome_none] using hmatch.1.symm

lemma pending_query_noncompute (p : Params) (i : Fin p.n) (worker next : State p)
    (oracle : ComputationState p) (action : Action (Point p) p.n)
    (hmatch : PendingMatches p worker oracle) (hq : query p i worker = (action, next))
    (hno : ∀ x, action ≠ .compute x) : PendingMatches p next oracle := by
  cases hqueue : worker.queue with
  | cons packet rest =>
      have he : next = { worker with queue := rest } := by
        simpa only [query, hqueue] using (congrArg Prod.snd hq).symm
      rw [he]
      exact pending_congr p worker _ oracle hmatch rfl rfl
  | nil =>
      cases hwork : worker.work with
      | none =>
          have hbusy := pending_no_work p worker oracle hmatch hwork
          have hnone := pending_none p worker oracle hmatch hbusy
          simp only [query, hqueue, hwork] at hq
          split_ifs at hq with hready hroot
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            apply pending_idle p _ oracle _ hnone
            exact finishBroadcast_busy p worker _ hbusy
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            exact pending_congr p worker _ oracle hmatch rfl hwork.symm
          · have he : next = worker := (congrArg Prod.snd hq).symm
            rwa [he]
      | some work =>
          cases hbusy : worker.busy with
          | true =>
              have he : next = worker := by
                simpa [query, hqueue, hwork, hbusy] using (congrArg Prod.snd hq).symm
              rwa [he]
          | false =>
              have hnone := pending_none p worker oracle hmatch hbusy
              cases hwq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  have he : next = finishLocal p worker
                      (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) := by
                    simpa [query, hqueue, hwork, hbusy, hwq] using (congrArg Prod.snd hq).symm
                  rw [he]
                  exact pending_idle p _ oracle (finishLocal_busy p worker _) hnone
              | some x =>
                  have he : action = .compute x := by
                    simpa [query, hqueue, hwork, hbusy, hwq] using (congrArg Prod.fst hq).symm
                  exact False.elim (hno x he)

lemma pending_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (hmatch : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next))
    (hparent : ∀ message, notification = .received message →
      i ≠ p.root ∧ message.source = p.parent i → (c.workers i).busy = false) :
    ∀ v, PendingMatches p
      (Function.update c.workers i (update p i (c.workers i) notification) v) (next.computation v) := by
  classical
  cases notification with
  | wake =>
      have hn := (DistributedExecution.wake_event (system p g S) (algorithm p idle)
        c c.time i next he).1
      rw [hn]
      intro v
      simpa [update] using hmatch v
  | computed value =>
      obtain ⟨oracle, ha, hn⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      rw [hn]
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        exact pending_complete p g S i (c.workers i) (c.oracle.computation i) oracle c.time value (hmatch i) ha
      · simpa [Function.update, hv] using hmatch v
  | received message =>
      obtain ⟨oracle, _, hn⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      rw [hn]
      intro v
      by_cases hv : v = i
      · subst v
        simp [Function.update]
        by_cases hp : i ≠ p.root ∧ message.source = p.parent i
        · exact pending_parent_message p i (c.workers i) (c.oracle.computation i) message
            (hmatch i) (hparent message rfl hp) hp
        · exact pending_child_message p i (c.workers i) (c.oracle.computation i) message (hmatch i) hp
      · simpa [Function.update, hv] using hmatch v

lemma pending_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (hmatch : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hparent : ∀ i message oracle,
      event (system p g S) (algorithm p idle) c c.time = some ((i, .received message), oracle) →
      i ≠ p.root ∧ message.source = p.parent i → (c.workers i).busy = false)
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, PendingMatches p (next.workers v) (next.oracle.computation v) := by
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
          exact hmatch
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        have hm := pending_notification p g S idle c i notification oracle hmatch he
          (fun message hn hp => hparent i message oracle (by simpa only [hn] using he) hp)
        rw [he] at hs
        cases hq : query p i (update p i (c.workers i) notification) with
        | mk action worker =>
            simp only [algorithm, hq] at hs
            have hmi : PendingMatches p (update p i (c.workers i) notification) (oracle.computation i) := by
              simpa [Function.update] using hm i
            cases action with
            | compute x =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  simp [Function.update]
                  exact (pending_submit p g S i _ worker (oracle.computation i) c.time x hmi hq).2
                · simpa [Function.update, hv] using hm v
            | communicate packet =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  simp [Function.update]
                  exact pending_query_noncompute p i _ worker (oracle.computation i) (.communicate packet)
                    hmi hq (by intro x; simp)
                · simpa [Function.update, hv] using hm v
            | advance target =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                intro v
                by_cases hv : v = i
                · subst v
                  simp [Function.update]
                  exact pending_query_noncompute p i _ worker (oracle.computation i) (.advance target)
                    hmi hq (by intro x; simp)
                · simpa [Function.update, hv] using hm v

end LongTails.Proofs.DistributedJacobianStrongGrowthExecution
