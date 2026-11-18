import LongTails.Proofs.DistributedJacobianStrongGrowthPhases
import LongTails.Proofs.DistributedJacobianStrongGrowthTree

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRouting

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthPhases

def SeenChildren (p : Params) (v : Fin p.n) (s : State p) : Prop :=
  s.collector.seen ⊆ children p v

def QueueShape (p : Params) (v : Fin p.n) (s : State p) : Prop :=
  (∀ packet ∈ s.queue, packet.1 ∈ children p v) ∧ (s.queue.map Prod.fst).Nodup

def SentCollected (p : Params) (v : Fin p.n) (s : State p) : Prop :=
  s.sent = true → children p v ⊆ s.collector.seen

lemma accept_seen_mono {n d : ℕ} (allowed : Finset (Fin n)) (s : Collector n d)
    (sender : Fin n) (values : Fin d → ℕ) : s.seen ⊆ (accept allowed s sender values).seen := by
  unfold accept
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

lemma accept_seen_subset {n d : ℕ} (allowed : Finset (Fin n)) (s : Collector n d)
    (sender : Fin n) (values : Fin d → ℕ) (h : s.seen ⊆ allowed) :
    (accept allowed s sender values).seen ⊆ allowed := by
  unfold accept
  split_ifs with hs
  · exact Finset.insert_subset hs.1 h
  · exact h

lemma seenChildren_initial (p : Params) (v : Fin p.n) : SeenChildren p v (initialState p v) := by
  unfold initialState
  split_ifs <;> exact Finset.empty_subset _

lemma queueShape_initial (p : Params) (v : Fin p.n) : QueueShape p v (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [QueueShape]

lemma sentCollected_initial (p : Params) (v : Fin p.n) : SentCollected p v (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [SentCollected]

lemma seenChildren_startMedian (p : Params) (v : Fin p.n) (remaining : ℕ) (s : State p) :
    SeenChildren p v (startMedian p remaining s) := Finset.empty_subset _

lemma seenChildren_startRefinement (p : Params) (v : Fin p.n) (epoch : ℕ) (s : State p) :
    SeenChildren p v (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs <;> exact Finset.empty_subset _

lemma seenChildren_finishLocal (p : Params) (v : Fin p.n) (s : State p) (x : Point p)
    (h : SeenChildren p v s) : SeenChildren p v (finishLocal p s x) := by
  unfold SeenChildren
  rw [DistributedJacobianStrongGrowthProtocol.finishLocal_preserves_collector]
  exact h

lemma seenChildren_finishBroadcast (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : SeenChildren p v s) : SeenChildren p v (finishBroadcast p s values) := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact seenChildren_startRefinement _ _ _ _
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · exact seenChildren_startMedian _ _ _ _
      · exact seenChildren_startRefinement _ _ _ _

lemma queueShape_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ) :
    QueueShape p v (relay p v s values) := by
  constructor
  · intro packet hp
    exact (DistributedJacobianStrongGrowthProtocol.relay_packet p v s values packet hp).1
  · change (((children p v).toList.map (fun child =>
      (child, LongTails.Algorithms.LocalExtragradientQuantization.naturalMessage (downWidth p s.phase) values))).map Prod.fst).Nodup
    simpa [List.map_map, Function.comp_def] using (children p v).nodup_toList

lemma sentCollected_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : ActiveShape p s) : SentCollected p v (relay p v s values) := by
  intro hs
  have hf := finishBroadcast_sent_false p s values h
  change (finishBroadcast p s values).sent = true at hs
  rw [hf] at hs
  cases hs

lemma seenChildren_relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (h : SeenChildren p v s) : SeenChildren p v (relay p v s values) :=
  seenChildren_finishBroadcast p v s values h

lemma seenChildren_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : SeenChildren p v s) : SeenChildren p v (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact h
      · exact h
  | received message =>
      simp only [update]
      split_ifs
      · exact seenChildren_relay _ _ _ _ h
      · exact accept_seen_subset _ _ _ _ h

lemma seenChildren_query (p : Params) (v : Fin p.n) (s : State p)
    (h : SeenChildren p v s) : SeenChildren p v (query p v s).2 := by
  unfold query
  split
  · exact h
  · split
    · split_ifs
      · exact h
      · split
        · exact h
        · exact seenChildren_finishLocal _ _ _ _ h
    · split_ifs
      · exact seenChildren_relay _ _ _ _ h
      · exact h
      · exact h

lemma queueShape_finishLocal (p : Params) (v : Fin p.n) (s : State p) (x : Point p)
    (h : QueueShape p v s) : QueueShape p v (finishLocal p s x) := by
  cases hs : s.phase <;> simpa [QueueShape, finishLocal, hs, startMedian] using h

lemma queueShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : QueueShape p v s) : QueueShape p v (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact h
      · exact h
  | received message =>
      simp only [update]
      split_ifs
      · exact queueShape_relay _ _ _ _
      · exact h

lemma queueShape_query (p : Params) (v : Fin p.n) (s : State p)
    (h : QueueShape p v s) : QueueShape p v (query p v s).2 := by
  unfold query
  split
  · rename_i packet rest hqueue
    constructor
    · intro q hq
      exact h.1 q (by simp [hqueue, hq])
    · have hn := h.2
      simp only [hqueue, List.map_cons, List.nodup_cons] at hn
      exact hn.2
  · split
    · split_ifs
      · exact h
      · split
        · exact h
        · exact queueShape_finishLocal _ _ _ _ h
    · split_ifs
      · exact queueShape_relay _ _ _ _
      · exact h
      · exact h

lemma sentCollected_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : SentCollected p v s) (ha : ActiveShape p s) :
    SentCollected p v (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact h
      · exact h
  | received message =>
      simp only [update]
      split_ifs
      · exact sentCollected_relay _ _ _ _ ha
      · intro hs
        exact Finset.Subset.trans (h hs) (accept_seen_mono _ _ _ _)

lemma sentCollected_query (p : Params) (v : Fin p.n) (s : State p)
    (h : SentCollected p v s) (ha : ActiveShape p s) (hr : ReadyShape p s) :
    SentCollected p v (query p v s).2 := by
  unfold query
  split
  · exact h
  · split
    · rename_i work hw
      have hf := (readyShape_work_some p s work hr hw).2
      split_ifs
      · exact h
      · split
        · exact h
        · intro hs
          have hn := finishLocal_sent_false p s
            (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hf
          change (finishLocal p s _).sent = true at hs
          rw [hn] at hs
          cases hs
    · split_ifs with hc
      · exact sentCollected_relay _ _ _ _ ha
      · intro _
        exact hc.2.2
      · exact h

lemma workerPredicate_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time)
    (Inv : Fin p.n → State p → Prop)
    (hupdate : ∀ v s notification, Inv v s → Inv v (update p v s notification))
    (hquery : ∀ v s next action, Inv v s → query p v s = (action, next) → Inv v next)
    (c next : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, Inv v (c.workers v))
    (hs : DistributedTemplate.step (system p g S) (algorithm p idle) c = some next) :
    ∀ v, Inv v (next.workers v) := by
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

def RoutingShape (p : Params) (v : Fin p.n) (s : State p) : Prop :=
  LocalShape p s ∧ SeenChildren p v s ∧ QueueShape p v s ∧ SentCollected p v s

lemma routingShape_initial (p : Params) (v : Fin p.n) : RoutingShape p v (initialState p v) :=
  ⟨localShape_initial p v, seenChildren_initial p v, queueShape_initial p v, sentCollected_initial p v⟩

lemma routingShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p)) (h : RoutingShape p v s) :
    RoutingShape p v (update p v s notification) :=
  ⟨localShape_update p v s notification h.1, seenChildren_update p v s notification h.2.1,
    queueShape_update p v s notification h.2.2.1,
    sentCollected_update p v s notification h.2.2.2 h.1.2.1⟩

lemma routingShape_query (p : Params) (v : Fin p.n) (s next : State p)
    (action : DistributedTemplate.Action (Point p) p.n) (h : RoutingShape p v s)
    (hq : query p v s = (action, next)) : RoutingShape p v next := by
  have hs : (query p v s).2 = next := congrArg Prod.snd hq
  refine ⟨localShape_query p v s next action h.1 hq, ?_, ?_, ?_⟩
  · rw [← hs]
    exact seenChildren_query p v s h.2.1
  · rw [← hs]
    exact queueShape_query p v s h.2.2.1
  · rw [← hs]
    exact sentCollected_query p v s h.2.2.2 h.1.2.1 h.1.1

lemma routingShape_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time) (k : ℕ)
    (c : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, RoutingShape p v (c.workers v)) :
    ∀ v, RoutingShape p v ((DistributedTemplate.run (system p g S) (algorithm p idle) k c).workers v) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using h
      | some next =>
          have hn := workerPredicate_step p g S idle (RoutingShape p)
            (routingShape_update p) (routingShape_query p) c next h hs
          simpa only [DistributedTemplate.run, hs] using ih next hn

lemma routingShape_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : DistributedTemplate.Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n) :
    RoutingShape p v ((DistributedTemplate.run (system p g S) (algorithm p idle) k
      (DistributedTemplate.initial (system p g S) (algorithm p idle) deadline seed)).workers v) :=
  routingShape_run p g S idle k _ (fun i => routingShape_initial p i) v

end LongTails.Proofs.DistributedJacobianStrongGrowthRouting
