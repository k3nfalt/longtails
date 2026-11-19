import LongTails.Proofs.DistributedJacobianStrongGrowthConservation
import LongTails.Proofs.DistributedJacobianStrongGrowthExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthNetworkExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthRouting

lemma networkEdges_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : NetworkEdges p c.oracle.communication)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    NetworkEdges p next.communication := by
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      exact h
  | computed value =>
      obtain ⟨oracle, _, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      exact h
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      exact (networkEdges_answer p S c.oracle.communication oracle h c.time message.source i message.bits ha).2

lemma computed_bookkeeping (p : Params) (i : Fin p.n) (s : State p) (value : Point p) :
    (update p i s (.computed value)).sent = s.sent ∧
    (update p i s (.computed value)).collector.seen = s.collector.seen ∧
    (update p i s (.computed value)).queue = s.queue := by
  simp only [update]
  split
  · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

lemma handshake_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    Handshake p (Function.update c.workers i (update p i (c.workers i) notification)) next.communication := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      have hu : Function.update c.workers i (update p i (c.workers i) .wake) = c.workers := by
        funext v
        by_cases hv : v = i <;> simp [update, Function.update, hv]
      erw [hu]
      exact h
  | computed value =>
      obtain ⟨oracle, _, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      have hb := computed_bookkeeping p i (c.workers i) value
      apply handshake_congr p c.workers _ c.oracle.communication h
      · intro v
        by_cases hv : v = i <;> simp_all [Function.update]
      · intro v
        by_cases hv : v = i <;> simp_all [Function.update]
      · intro v
        by_cases hv : v = i <;> simp_all [Function.update]
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      obtain ⟨finish, hstored, _, rfl⟩ :=
        DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
          c.time message.source i message.bits ha
      have hadj := hedges message.source i _ hstored
      by_cases hd : i ≠ p.root ∧ message.source = p.parent i
      · have hstored' : c.oracle.communication.messages (p.parent i) i = some (finish, message.bits) := by
          simpa only [hd.2] using hstored
        have hs := down_pending_sent p c.workers c.oracle.communication h i hd.1 finish message.bits hstored'
        have hr := hroute i
        have hseen := Finset.Subset.antisymm hr.2.1 (hr.2.2.2 hs)
        have hqueue := hr.1.2.2 hs
        simpa [update, hd, hd.2] using handshake_receive_down p hp c.workers c.oracle.communication h i hd.1
          hr.1.2.1 hseen hqueue
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d (downWidth p (c.workers i).phase) message.bits)
          finish message.bits hstored'
      · have hup : p.parent message.source = i := by
          rcases hadj.2 with hu | hu
          · exact hu
          · exfalso
            apply hd
            refine ⟨?_, hu.symm⟩
            intro hi
            have hh := hp.2.1
            rw [hi, hh] at hu
            exact hadj.1 (hu.symm.trans hi.symm)
        have hsource : message.source ≠ p.root := by
          intro hs
          have hh := hp.2.1
          rw [hs, hh] at hup
          exact hadj.1 (hs.trans hup)
        have result := handshake_receive_up p hp c.workers c.oracle.communication h message.source hsource
          finish message.bits (by simpa only [hup] using hstored)
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d (upWidth p (c.workers i).phase) message.bits)
        simpa [update, hd, hup] using result

lemma handshake_update_worker (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (i : Fin p.n) (next : State p)
    (hs : next.sent = (workers i).sent)
    (hc : next.collector.seen = (workers i).collector.seen)
    (hq : next.queue = (workers i).queue) :
    Handshake p (Function.update workers i next) network := by
  classical
  apply handshake_congr p workers _ network h
  · intro v
    by_cases hv : v = i <;> simp_all [Function.update]
  · intro v
    by_cases hv : v = i <;> simp_all [Function.update]
  · intro v
    by_cases hv : v = i <;> simp_all [Function.update]

lemma finishLocal_queue (p : Params) (s : State p) (x : Point p) :
    (finishLocal p s x).queue = s.queue := by
  cases hs : s.phase <;> simp [finishLocal, hs, startMedian]

lemma handshake_finishLocal (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (i : Fin p.n) (x : Point p) (hs : (workers i).sent = false) :
    Handshake p (Function.update workers i (finishLocal p (workers i) x)) network := by
  apply handshake_update_worker p workers network h i _
  · rw [hs]
    exact DistributedJacobianStrongGrowthPhases.finishLocal_sent_false p (workers i) x hs
  · rw [DistributedJacobianStrongGrowthProtocol.finishLocal_preserves_collector]
  · exact finishLocal_queue p (workers i) x

lemma handshake_query (p : Params) (hp : valid p) (S : Sampling p)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network) (hroute : ∀ v, RoutingShape p v (workers v))
    (i : Fin p.n) (time : Time) :
    Handshake p (Function.update workers i (query p i (workers i)).2)
      (match (query p i (workers i)).1 with
       | .communicate packet => (communication p S).submit network time i
           (packet.1, packet.2 ++ List.replicate clockBits false)
       | _ => network) := by
  classical
  cases hqueue : (workers i).queue with
  | cons packet rest =>
      rcases packet with ⟨target, bits⟩
      have hchild := (hroute i).2.2.1.1 (target, bits) (by simp [hqueue])
      have ht : target ≠ p.root ∧ p.parent target = i := (Finset.mem_filter.mp hchild).2
      have hq : (workers (p.parent target)).queue = (target, bits) :: rest := by simpa only [ht.2] using hqueue
      have hpos : 0 < (workers (p.parent target)).queue.countP (fun packet => decide (packet.1 = target)) := by simp [hq]
      have hfree := down_free_of_queued p workers network h target ht.1 hpos
      have hadj := DistributedJacobianStrongGrowthOracle.child_adjacent p hp target i ht.1 ht.2
      have hadj' : adjacent p i target := ⟨Ne.symm hadj.1, Or.inr ht.2⟩
      simp only [query, hqueue]
      rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time i target (bits ++ List.replicate clockBits false) hadj'
        (by simpa only [ht.2] using hfree)]
      simpa only [ht.2] using handshake_send_down p hp workers network h target ht.1 bits rest hq
        (time + p.l + p.β * (bits ++ List.replicate clockBits false).length,
          bits ++ List.replicate clockBits false)
  | nil =>
      cases hw : (workers i).work with
      | some work =>
          have hs := (DistributedJacobianStrongGrowthPhases.readyShape_work_some p (workers i) work (hroute i).1.1 hw).2
          cases hb : (workers i).busy with
          | true => simpa [query, hqueue, hw, hb] using h
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  simpa [query, hqueue, hw, hb, hquery] using handshake_finishLocal p workers network h i
                    (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hs
              | some x =>
                  simpa [query, hqueue, hw, hb, hquery] using
                    handshake_update_worker p workers network h i { workers i with busy := true } rfl rfl rfl
      | none =>
          by_cases hr : (workers i).ready ∧ ¬ (workers i).sent ∧ children p i ⊆ (workers i).collector.seen
          · by_cases hi : i = p.root
            · subst i
              have hseen := Finset.Subset.antisymm (hroute p.root).2.1 hr.2.2
              simpa [query, hqueue, hw, hr] using handshake_relay_root p workers network h
                ((hroute p.root).1.2.1 (Or.inl hr.1)) hseen hqueue
                (broadcastValues p (workers p.root).phase (fun j => (workers p.root).own j + (workers p.root).collector.total j))
            · have hs : (workers i).sent = false := Bool.eq_false_iff.mpr hr.2.1
              have hfree := up_free_of_not_sent p workers network h i hi hs
              have hadj := DistributedJacobianStrongGrowthOracle.child_adjacent p hp i (p.parent i) hi rfl
              simp only [query, hqueue, hw, ite_eq_left hr, ite_eq_right hi]
              rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time i (p.parent i) _ hadj hfree]
              convert handshake_send_up p hp workers network h i hi hs _ using 1
              simp [hw, hqueue]
          · simp only [query, hqueue, hw, ite_eq_right hr]
            simpa only [Function.update_eq_self] using h

lemma network_step (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hs : step (system p g S) (algorithm p idle) c = some next) :
    Handshake p next.workers next.oracle.communication ∧ NetworkEdges p next.oracle.communication := by
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
          exact ⟨h, hedges⟩
    | some result =>
        obtain ⟨⟨i, notification⟩, oracle⟩ := result
        let updated : Fin p.n → State p := Function.update c.workers i (update p i (c.workers i) notification)
        have hu : ∀ v, RoutingShape p v (updated v) := by
          intro v
          by_cases hv : v = i
          · subst v
            simpa [updated, Function.update] using routingShape_update p i (c.workers i) notification (hroute i)
          · simpa [updated, Function.update, hv] using hroute v
        have hh := handshake_notification p hp g S idle c i notification oracle h hedges hroute he
        have hn := networkEdges_notification p g S idle c i notification oracle hedges he
        have hqall := handshake_query p hp S updated oracle.communication hh hu i c.time
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
                refine ⟨?_, hn⟩
                simpa [algorithm, system] using hqall
            | communicate packet =>
                rcases packet with ⟨target, bits⟩
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                refine ⟨?_, ?_⟩
                · simpa [algorithm, system] using hqall
                · exact networkEdges_submit p S oracle.communication hn c.time i target
                    (bits ++ List.replicate clockBits false)
            | advance code =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                refine ⟨?_, hn⟩
                simpa [algorithm, system] using hqall

lemma network_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time) (k : ℕ)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (h : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v)) :
    let next := run (system p g S) (algorithm p idle) k c
    Handshake p next.workers next.oracle.communication ∧ NetworkEdges p next.oracle.communication := by
  induction k generalizing c with
  | zero => exact ⟨h, hedges⟩
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using And.intro h hedges
      | some next =>
          have hn := network_step p hp g S idle c next h hedges hroute hs
          have hr := workerPredicate_step p g S idle (RoutingShape p)
            (routingShape_update p) (routingShape_query p) c next hroute hs
          simpa only [run, hs] using ih next hn.1 hn.2 hr

lemma network_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) :
    let next := run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)
    Handshake p next.workers next.oracle.communication ∧ NetworkEdges p next.oracle.communication := by
  exact network_run p hp g S idle k _ (handshake_initial p S seed.2)
    (networkEdges_initial p S seed.2) (fun v => routingShape_initial p v)

lemma parent_event_idle (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (message : CommReply p) (next : OracleState (system p g S))
    (h : Handshake p c.workers c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, .received message), next))
    (hp : i ≠ p.root ∧ message.source = p.parent i) : (c.workers i).busy = false := by
  obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
    c c.time i message next he
  obtain ⟨finish, hstored, _, _⟩ :=
    DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
      c.time message.source i message.bits ha
  exact down_pending_idle p c.workers c.oracle.communication h (fun v => (hroute v).1.1)
    i hp.1 finish message.bits (by simpa only [hp.2] using hstored)

lemma pending_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time) (k : ℕ)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (h : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hmatch : ∀ v, DistributedJacobianStrongGrowthExecution.PendingMatches p (c.workers v) (c.oracle.computation v)) :
    ∀ v, DistributedJacobianStrongGrowthExecution.PendingMatches p
      ((run (system p g S) (algorithm p idle) k c).workers v)
      ((run (system p g S) (algorithm p idle) k c).oracle.computation v) := by
  induction k generalizing c with
  | zero => exact hmatch
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using hmatch
      | some next =>
          have hn := network_step p hp g S idle c next h hedges hroute hs
          have hr := workerPredicate_step p g S idle (RoutingShape p)
            (routingShape_update p) (routingShape_query p) c next hroute hs
          have hm := DistributedJacobianStrongGrowthExecution.pending_step p g S idle c next hmatch
            (fun i message oracle he hp => parent_event_idle p g S idle c i message oracle h hroute he hp) hs
          simpa only [run, hs] using ih next hn.1 hn.2 hr hm

lemma pending_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n) :
    let next := run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)
    DistributedJacobianStrongGrowthExecution.PendingMatches p (next.workers v) (next.oracle.computation v) := by
  exact pending_run p hp g S idle k _ (handshake_initial p S seed.2)
    (networkEdges_initial p S seed.2) (fun i => routingShape_initial p i)
    (fun i => DistributedJacobianStrongGrowthExecution.pending_initial p g S i seed.2) v

end LongTails.Proofs.DistributedJacobianStrongGrowthNetworkExecution
