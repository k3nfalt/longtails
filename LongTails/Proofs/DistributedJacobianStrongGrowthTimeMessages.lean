import LongTails.Proofs.DistributedJacobianStrongGrowthTimeState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeMessages

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthHandshake

lemma messageTimes_replace (p : Params) (workers next : Fin p.n → State p)
    (network nextNetwork : CommunicationState p)
    (hu : ∀ v, v ≠ p.root → ∀ finish bits, network.messages v (p.parent v) = some (finish, bits) →
      finish ≤ upDeadline p (epochIndex p (workers v).phase) (p.parent v))
    (hd : ∀ v, v ≠ p.root → ∀ finish bits, network.messages (p.parent v) v = some (finish, bits) →
      finish ≤ downDeadline p (epochIndex p (workers v).phase) v)
    (hsub : ∀ a b packet, nextNetwork.messages a b = some packet → network.messages a b = some packet)
    (hchange : ∀ v, v ≠ p.root → epochIndex p (next v).phase ≠ epochIndex p (workers v).phase →
      nextNetwork.messages v (p.parent v) = none ∧ nextNetwork.messages (p.parent v) v = none) :
    (∀ v, v ≠ p.root → ∀ finish bits, nextNetwork.messages v (p.parent v) = some (finish, bits) →
      finish ≤ upDeadline p (epochIndex p (next v).phase) (p.parent v)) ∧
    (∀ v, v ≠ p.root → ∀ finish bits, nextNetwork.messages (p.parent v) v = some (finish, bits) →
      finish ≤ downDeadline p (epochIndex p (next v).phase) v) := by
  constructor
  · intro v hv finish bits hpending
    by_cases he : epochIndex p (next v).phase = epochIndex p (workers v).phase
    · rw [he]
      exact hu v hv finish bits (hsub _ _ _ hpending)
    · have hn := (hchange v hv he).1
      rw [hpending] at hn
      cases hn
  · intro v hv finish bits hpending
    by_cases he : epochIndex p (next v).phase = epochIndex p (workers v).phase
    · rw [he]
      exact hd v hv finish bits (hsub _ _ _ hpending)
    · have hn := (hchange v hv he).2
      rw [hpending] at hn
      cases hn

lemma communication_answer_subset (p : Params) (S : Sampling p) (network next : CommunicationState p)
    (time : Time) (source target : Fin p.n) (bits : List Bool)
    (ha : (communication p S).answer network time = some ((target, ⟨source, bits⟩), next)) :
    ∀ a b packet, next.messages a b = some packet → network.messages a b = some packet := by
  classical
  obtain ⟨finish, _, _, rfl⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
    network next time source target bits ha
  intro a b packet hstored
  by_cases hs : a = source
  · subst a
    by_cases ht : b = target
    · subst b
      simp [Function.update] at hstored
    · simpa [Function.update, ht] using hstored
  · simpa [Function.update, hs] using hstored

lemma up_free_of_down (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (hh : Handshake p workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (finish : Time) (bits : List Bool) (hpending : network.messages (p.parent v) v = some (finish, bits)) :
    network.messages v (p.parent v) = none := by
  cases hstored : network.messages v (p.parent v) with
  | none => rfl
  | some packet =>
      have hedge := hh v hv
      unfold edgeLoad at hedge
      rw [hpending, hstored] at hedge
      cases hsent : (workers v).sent <;>
        simp only [Option.isSome_some, Bool.toNat_true, hsent, Bool.toNat_false] at hedge <;> omega

lemma communication_parent_clear (p : Params) (hp : valid p) (S : Sampling p)
    (workers : Fin p.n → State p) (network next : CommunicationState p)
    (hh : Handshake p workers network) (time : Time) (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool)
    (ha : (communication p S).answer network time = some ((v, ⟨p.parent v, bits⟩), next)) :
    next.messages v (p.parent v) = none ∧ next.messages (p.parent v) v = none := by
  classical
  obtain ⟨finish, hstored, _, rfl⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
    network next time (p.parent v) v bits ha
  have hu := up_free_of_down p workers network hh v hv finish bits hstored
  have hn := DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv
  simp [Function.update, Ne.symm hn, hu]

lemma update_computed_phase (p : Params) (v : Fin p.n) (s : State p) (value : Point p) :
    (update p v s (.computed value)).phase = s.phase := by
  cases hw : s.work with
  | none => simp [update, hw]
  | some work => cases hb : s.busy <;> simp [update, hw, hb]

lemma messageTimes_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hh : Handshake p c.workers c.oracle.communication)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    (∀ i, i ≠ p.root → ∀ finish bits, next.communication.messages i (p.parent i) = some (finish, bits) →
      finish ≤ upDeadline p (epochIndex p (Function.update c.workers v (update p v (c.workers v) notification) i).phase) (p.parent i)) ∧
    (∀ i, i ≠ p.root → ∀ finish bits, next.communication.messages (p.parent i) i = some (finish, bits) →
      finish ≤ downDeadline p (epochIndex p (Function.update c.workers v (update p v (c.workers v) notification) i).phase) i) := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time v next he).1]
      apply messageTimes_replace p c.workers _ c.oracle.communication _ ht.up ht.down
      · exact fun _ _ _ h => h
      · intro i _ hneq
        by_cases hiv : i = v
        · subst i
          simp [Function.update, update, algorithm] at hneq
        · simp [Function.update, hiv, algorithm] at hneq
  | computed value =>
      obtain ⟨oracle, _, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value next he
      apply messageTimes_replace p c.workers _ c.oracle.communication _ ht.up ht.down
      · exact fun _ _ _ h => h
      · intro i _ hneq
        by_cases hiv : i = v
        · subst i
          simp [Function.update, algorithm, update_computed_phase] at hneq
        · simp [Function.update, hiv, algorithm] at hneq
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
      apply messageTimes_replace p c.workers _ c.oracle.communication _ ht.up ht.down
      · exact communication_answer_subset p S c.oracle.communication oracle c.time message.source v message.bits ha
      · intro i hi hneq
        by_cases hiv : i = v
        · subst i
          by_cases hd : v ≠ p.root ∧ message.source = p.parent v
          · apply communication_parent_clear p hp S c.workers c.oracle.communication oracle hh c.time v hi message.bits
            have hreply : message = (⟨p.parent v, message.bits⟩ : CommReply p) := by
              cases message with
              | mk source bits => simpa only [CommReply.mk.injEq, and_true] using hd.2
            rw [← hreply]
            exact ha
          · simp [Function.update, update, hd, algorithm] at hneq
        · simp [Function.update, hiv, algorithm] at hneq

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeMessages
