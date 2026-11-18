import LongTails.Proofs.DistributedJacobianStrongGrowthProtocol
import LongTails.Proofs.DistributedExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthPhases

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

def ReadyShape (p : Params) (s : State p) : Prop :=
  (s.ready = true ∨ s.sent = true) → s.work = none ∧ s.busy = false

lemma readyShape_initial (p : Params) (v : Fin p.n) : ReadyShape p (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [ReadyShape]

lemma readyShape_startMedian (p : Params) (remaining : ℕ) (s : State p) :
    ReadyShape p (startMedian p remaining s) := by
  simp [ReadyShape, startMedian]

lemma readyShape_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    ReadyShape p (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs <;> simp [ReadyShape]

lemma readyShape_finishLocal (p : Params) (s : State p) (x : Point p) :
    ReadyShape p (finishLocal p s x) := by
  cases hs : s.phase <;> simp [ReadyShape, finishLocal, startMedian, hs]

lemma readyShape_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : ReadyShape p s) : ReadyShape p (finishBroadcast p s values) := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact readyShape_startRefinement _ _ _
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · exact readyShape_startMedian _ _ _
      · exact readyShape_startRefinement _ _ _

lemma readyShape_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : ReadyShape p s) : ReadyShape p (relay p v s values) :=
  readyShape_finishBroadcast p s values h

lemma readyShape_work_some (p : Params) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : ReadyShape p s) (hw : s.work = some work) : s.ready = false ∧ s.sent = false := by
  cases hr : s.ready <;> cases hs : s.sent <;> simp_all [ReadyShape]

lemma readyShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p)) (h : ReadyShape p s) :
    ReadyShape p (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      cases hw : s.work with
      | none => simpa [update, hw] using h
      | some work =>
          obtain ⟨hr, hs⟩ := readyShape_work_some p s work h hw
          cases hb : s.busy <;> simp [update, hw, hb, ReadyShape, hr, hs]
  | received message =>
      by_cases hp : v ≠ p.root ∧ message.source = p.parent v
      · simpa only [update, ite_eq_left hp] using readyShape_relay p v s
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (downWidth p s.phase) message.bits) h
      · simpa only [update, ite_eq_right hp, ReadyShape] using h

lemma readyShape_query (p : Params) (v : Fin p.n) (s next : State p)
    (action : DistributedTemplate.Action (Point p) p.n) (h : ReadyShape p s)
    (hq : query p v s = (action, next)) : ReadyShape p next := by
  cases hqueue : s.queue with
  | cons packet rest =>
      have he : next = { s with queue := rest } := by
        simpa only [query, hqueue] using (congrArg Prod.snd hq).symm
      rw [he]
      exact h
  | nil =>
      cases hw : s.work with
      | none =>
          simp only [query, hqueue, hw] at hq
          split_ifs at hq with hr hroot
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            exact readyShape_relay p v s _ h
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            have hb := (h (Or.inl hr.1)).2
            simp [ReadyShape, hb]
          · have he : next = s := (congrArg Prod.snd hq).symm
            rwa [he]
      | some work =>
          obtain ⟨hr, hs⟩ := readyShape_work_some p s work h hw
          cases hb : s.busy with
          | true =>
              have he : next = s := by
                simpa [query, hqueue, hw, hb] using (congrArg Prod.snd hq).symm
              rwa [he]
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  have he : next = finishLocal p s
                      (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  exact readyShape_finishLocal p s _
              | some x =>
                  have he : next = { s with busy := true } := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  simp [ReadyShape, hr, hs]

lemma readyShape_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time)
    (c next : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, ReadyShape p (c.workers v))
    (hs : DistributedTemplate.step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, ReadyShape p (next.workers v) := by
  classical
  cases he : DistributedTemplate.event (system p g S) (algorithm p idle) c c.time with
  | none =>
      unfold DistributedTemplate.step at hs
      by_cases hl : c.deadline < c.time
      · simp only [ite_eq_left hl, reduceCtorEq] at hs
      · rw [ite_eq_right hl, he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hstate := Option.some.inj hs
          subst next
          exact h
  | some result =>
      obtain ⟨⟨i, notification⟩, oracle⟩ := result
      cases hq : query p i (update p i (c.workers i) notification) with
      | mk action worker =>
          have hworker := readyShape_query p i _ worker action
            (readyShape_update p i (c.workers i) notification (h i)) hq
          have hw := (DistributedExecution.step_event_state (system p g S) (algorithm p idle)
            c next i notification oracle action worker he hq hs).1
          rw [hw]
          intro v
          by_cases hv : v = i
          · subst v
            simpa [Function.update] using hworker
          · simpa [Function.update, hv] using h v

lemma readyShape_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time) (k : ℕ)
    (c : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, ReadyShape p (c.workers v)) :
    ∀ v, ReadyShape p ((DistributedTemplate.run (system p g S) (algorithm p idle) k c).workers v) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using h
      | some next =>
          simpa only [DistributedTemplate.run, hs] using ih next (readyShape_step p g S idle c next h hs)

lemma readyShape_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : DistributedTemplate.Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n) :
    ReadyShape p ((DistributedTemplate.run (system p g S) (algorithm p idle) k
      (DistributedTemplate.initial (system p g S) (algorithm p idle) deadline seed)).workers v) := by
  exact readyShape_run p g S idle k _ (fun i => readyShape_initial p i) v

def Active : Phase → Prop
  | .median _ => True
  | .refinement _ => True
  | _ => False

def ActiveShape (p : Params) (s : State p) : Prop :=
  (s.ready = true ∨ s.sent = true) → Active s.phase

def SentQueue (p : Params) (s : State p) : Prop := s.sent = true → s.queue = []

lemma activeShape_initial (p : Params) (v : Fin p.n) : ActiveShape p (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [ActiveShape]

lemma activeShape_startMedian (p : Params) (remaining : ℕ) (s : State p) :
    ActiveShape p (startMedian p remaining s) := by
  simp [ActiveShape, Active, startMedian]

lemma activeShape_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    ActiveShape p (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs <;> simp [ActiveShape]

lemma activeShape_finishLocal (p : Params) (s : State p) (x : Point p) (h : ActiveShape p s) :
    ActiveShape p (finishLocal p s x) := by
  cases hs : s.phase <;> simp_all [ActiveShape, Active, finishLocal, startMedian]

lemma activeShape_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : ActiveShape p s) : ActiveShape p (finishBroadcast p s values) := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact activeShape_startRefinement _ _ _
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · exact activeShape_startMedian _ _ _
      · exact activeShape_startRefinement _ _ _

lemma startRefinement_sent_false (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).sent = false := by
  unfold startRefinement
  split_ifs <;> rfl

lemma finishBroadcast_sent_false (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : ActiveShape p s) : (finishBroadcast p s values).sent = false := by
  cases hs : s.phase with
  | baseline => cases ht : s.sent <;> simp_all [finishBroadcast, ActiveShape, Active]
  | warming => cases ht : s.sent <;> simp_all [finishBroadcast, ActiveShape, Active]
  | done => cases ht : s.sent <;> simp_all [finishBroadcast, ActiveShape, Active]
  | refinement epoch => simp only [finishBroadcast, hs, startRefinement_sent_false]
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · rfl
      · exact startRefinement_sent_false _ _ _

lemma sentQueue_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : ActiveShape p s) : SentQueue p (relay p v s values) := by
  intro hs
  have hf := finishBroadcast_sent_false p s values h
  change (finishBroadcast p s values).sent = true at hs
  rw [hf] at hs
  cases hs

lemma activeShape_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : ActiveShape p s) : ActiveShape p (relay p v s values) :=
  activeShape_finishBroadcast p s values h

lemma activeShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p)) (h : ActiveShape p s) (hrdy : ReadyShape p s) :
    ActiveShape p (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      cases hw : s.work with
      | none => simpa [update, hw] using h
      | some work =>
          obtain ⟨hr, hs⟩ := readyShape_work_some p s work hrdy hw
          cases hb : s.busy <;> simp [update, hw, hb, ActiveShape, hr, hs]
  | received message =>
      by_cases hp : v ≠ p.root ∧ message.source = p.parent v
      · simpa only [update, ite_eq_left hp] using activeShape_relay p v s
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (downWidth p s.phase) message.bits) h
      · simpa only [update, ite_eq_right hp, ActiveShape] using h

lemma activeShape_query (p : Params) (v : Fin p.n) (s next : State p)
    (action : DistributedTemplate.Action (Point p) p.n) (h : ActiveShape p s) (hrdy : ReadyShape p s)
    (hq : query p v s = (action, next)) : ActiveShape p next := by
  cases hqueue : s.queue with
  | cons packet rest =>
      have he : next = { s with queue := rest } := by
        simpa only [query, hqueue] using (congrArg Prod.snd hq).symm
      rw [he]
      exact h
  | nil =>
      cases hw : s.work with
      | none =>
          simp only [query, hqueue, hw] at hq
          split_ifs at hq with hr hroot
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            exact activeShape_relay p v s _ h
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            intro _
            exact h (Or.inl hr.1)
          · have he : next = s := (congrArg Prod.snd hq).symm
            rwa [he]
      | some work =>
          obtain ⟨hr, hs⟩ := readyShape_work_some p s work hrdy hw
          cases hb : s.busy with
          | true =>
              have he : next = s := by
                simpa [query, hqueue, hw, hb] using (congrArg Prod.snd hq).symm
              rwa [he]
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  have he : next = finishLocal p s
                      (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  exact activeShape_finishLocal p s _ h
              | some x =>
                  have he : next = { s with busy := true } := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  simp [ActiveShape, hr, hs]

lemma sentQueue_initial (p : Params) (v : Fin p.n) : SentQueue p (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [SentQueue]

lemma finishLocal_sent_false (p : Params) (s : State p) (x : Point p) (hsent : s.sent = false) :
    (finishLocal p s x).sent = false := by
  cases hs : s.phase <;> simp [finishLocal, startMedian, hs, hsent]

lemma sentQueue_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : SentQueue p s) (ha : ActiveShape p s) (hrdy : ReadyShape p s) :
    SentQueue p (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      cases hw : s.work with
      | none => simpa [update, hw] using h
      | some work =>
          have hs := (readyShape_work_some p s work hrdy hw).2
          cases hb : s.busy <;> simp [update, hw, hb, SentQueue, hs]
  | received message =>
      by_cases hp : v ≠ p.root ∧ message.source = p.parent v
      · simpa only [update, ite_eq_left hp] using sentQueue_relay p v s
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (downWidth p s.phase) message.bits) ha
      · simpa only [update, ite_eq_right hp, SentQueue] using h

lemma sentQueue_query (p : Params) (v : Fin p.n) (s next : State p)
    (action : DistributedTemplate.Action (Point p) p.n)
    (h : SentQueue p s) (ha : ActiveShape p s) (hrdy : ReadyShape p s)
    (hq : query p v s = (action, next)) : SentQueue p next := by
  cases hqueue : s.queue with
  | cons packet rest =>
      have he : next = { s with queue := rest } := by
        simpa only [query, hqueue] using (congrArg Prod.snd hq).symm
      rw [he]
      intro hsent
      have hnil := h hsent
      rw [hqueue] at hnil
      cases hnil
  | nil =>
      cases hw : s.work with
      | none =>
          simp only [query, hqueue, hw] at hq
          split_ifs at hq with hr hroot
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            exact sentQueue_relay p v s _ ha
          · have he := (congrArg Prod.snd hq).symm
            dsimp only at he
            rw [he]
            simp [SentQueue]
          · have he : next = s := (congrArg Prod.snd hq).symm
            rwa [he]
      | some work =>
          have hsent := (readyShape_work_some p s work hrdy hw).2
          cases hb : s.busy with
          | true =>
              have he : next = s := by
                simpa [query, hqueue, hw, hb] using (congrArg Prod.snd hq).symm
              rwa [he]
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  have he : next = finishLocal p s
                      (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  simp [SentQueue, finishLocal_sent_false p s _ hsent]
              | some x =>
                  have he : next = { s with busy := true } := by
                    simpa [query, hqueue, hw, hb, hquery] using (congrArg Prod.snd hq).symm
                  rw [he]
                  simp [SentQueue, hsent]

lemma statePredicate_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time)
    (Inv : State p → Prop)
    (hupdate : ∀ v s notification, Inv s → Inv (update p v s notification))
    (hquery : ∀ v s next action, Inv s → query p v s = (action, next) → Inv next)
    (c next : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, Inv (c.workers v))
    (hs : DistributedTemplate.step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, Inv (next.workers v) := by
  classical
  cases he : DistributedTemplate.event (system p g S) (algorithm p idle) c c.time with
  | none =>
      unfold DistributedTemplate.step at hs
      by_cases hl : c.deadline < c.time
      · simp only [ite_eq_left hl, reduceCtorEq] at hs
      · rw [ite_eq_right hl, he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hstate := Option.some.inj hs
          subst next
          exact h
  | some result =>
      obtain ⟨⟨i, notification⟩, oracle⟩ := result
      cases hq : query p i (update p i (c.workers i) notification) with
      | mk action worker =>
          have hworker := hquery i _ worker action
            (hupdate i (c.workers i) notification (h i)) hq
          have hw := (DistributedExecution.step_event_state (system p g S) (algorithm p idle)
            c next i notification oracle action worker he hq hs).1
          rw [hw]
          intro v
          by_cases hv : v = i
          · subst v
            simpa [Function.update] using hworker
          · simpa [Function.update, hv] using h v

def LocalShape (p : Params) (s : State p) : Prop :=
  ReadyShape p s ∧ ActiveShape p s ∧ SentQueue p s

lemma localShape_initial (p : Params) (v : Fin p.n) : LocalShape p (initialState p v) :=
  ⟨readyShape_initial p v, activeShape_initial p v, sentQueue_initial p v⟩

lemma localShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p)) (h : LocalShape p s) :
    LocalShape p (update p v s notification) :=
  ⟨readyShape_update p v s notification h.1, activeShape_update p v s notification h.2.1 h.1,
    sentQueue_update p v s notification h.2.2 h.2.1 h.1⟩

lemma localShape_query (p : Params) (v : Fin p.n) (s next : State p)
    (action : DistributedTemplate.Action (Point p) p.n) (h : LocalShape p s)
    (hq : query p v s = (action, next)) : LocalShape p next :=
  ⟨readyShape_query p v s next action h.1 hq, activeShape_query p v s next action h.2.1 h.1 hq,
    sentQueue_query p v s next action h.2.2 h.2.1 h.1 hq⟩

lemma localShape_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time) (k : ℕ)
    (c : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, LocalShape p (c.workers v)) :
    ∀ v, LocalShape p ((DistributedTemplate.run (system p g S) (algorithm p idle) k c).workers v) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using h
      | some next =>
          have hn := statePredicate_step p g S idle (LocalShape p)
            (localShape_update p) (localShape_query p) c next h hs
          simpa only [DistributedTemplate.run, hs] using ih next hn

lemma localShape_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : DistributedTemplate.Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n) :
    LocalShape p ((DistributedTemplate.run (system p g S) (algorithm p idle) k
      (DistributedTemplate.initial (system p g S) (algorithm p idle) deadline seed)).workers v) := by
  exact localShape_run p g S idle k _ (fun i => localShape_initial p i) v

end LongTails.Proofs.DistributedJacobianStrongGrowthPhases
