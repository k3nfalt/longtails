import LongTails.Proofs.DistributedJacobianStrongGrowthHandshake
import LongTails.Proofs.DistributedJacobianStrongGrowthRouting

namespace LongTails.Proofs.DistributedJacobianStrongGrowthConservation

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthRouting

lemma parent_ne_self (p : Params) (hp : valid p) (v : Fin p.n) (hv : v ≠ p.root) :
    p.parent v ≠ v := by
  intro he
  have hd := hp.2.2.2.1 v hv
  rw [he] at hd
  omega

lemma no_reverse_edge (p : Params) (hp : valid p) (u v : Fin p.n)
    (hu : u ≠ p.root) (hv : v ≠ p.root) (he : p.parent u = v) : p.parent v ≠ u := by
  intro hf
  have hd := hp.2.2.2.1 u hu
  have hd' := hp.2.2.2.1 v hv
  rw [he] at hd
  rw [hf] at hd'
  omega

lemma handshake_send_up (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (hs : (workers v).sent = false)
    (packet : DistributedTemplate.Time × List Bool) :
    Handshake p (Function.update workers v { workers v with sent := true })
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v) (some packet))⟩ := by
  classical
  have hfree := up_free_of_not_sent p workers network h v hv hs
  intro child hc
  by_cases he : child = v
  · subst child
    have hload := h v hv
    simp only [edgeLoad, hfree, hs, Option.isSome_none, Bool.toNat_false, Nat.zero_add] at hload
    have hn := parent_ne_self p hp v hv
    simp [edgeLoad, Function.update, hn]
    omega
  · have hreverse : ¬ (p.parent child = v ∧ p.parent v = child) := by
      intro hr
      exact no_reverse_edge p hp child v hc hv hr.1 hr.2
    have hload := h child hc
    by_cases hpc : p.parent child = v
    · have hvc : p.parent v ≠ child := fun heq => hreverse ⟨hpc, heq⟩
      simpa [edgeLoad, Function.update, he, hpc, Ne.symm hvc] using hload
    · simpa [edgeLoad, Function.update, he, hpc] using hload

lemma handshake_receive_up (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpacket : network.messages v (p.parent v) = some (finish, bits)) (values : Fin p.d → ℕ) :
    Handshake p
      (Function.update workers (p.parent v) { workers (p.parent v) with
        collector := accept (children p (p.parent v)) (workers (p.parent v)).collector v values })
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v) none)⟩ := by
  classical
  have hunseen := up_pending_unseen p workers network h v hv finish bits hpacket
  have hchild : v ∈ children p (p.parent v) := by simp [children, hv]
  have haccept : (accept (children p (p.parent v)) (workers (p.parent v)).collector v values).seen =
      insert v (workers (p.parent v)).collector.seen := by
    simp [accept, hchild, hunseen]
  intro child hc
  by_cases he : child = v
  · subst child
    have hload := h v hv
    have hn := parent_ne_self p hp v hv
    simp [edgeLoad, hpacket, hunseen] at hload
    simpa [edgeLoad, Function.update, hn, Ne.symm hn, haccept] using hload
  · have hreverse : ¬ (p.parent child = v ∧ p.parent v = child) := by
      intro hr
      exact no_reverse_edge p hp child v hc hv hr.1 hr.2
    have hload := h child hc
    have hev : v ≠ child := Ne.symm he
    by_cases hpc : p.parent child = v <;>
      by_cases hcv : child = p.parent v <;>
      by_cases hpp : p.parent child = p.parent v <;>
      simp_all [edgeLoad, Function.update]

lemma handshake_send_down (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool) (rest : List (Fin p.n × List Bool))
    (hqueue : (workers (p.parent v)).queue = (v, bits) :: rest)
    (packet : DistributedTemplate.Time × List Bool) :
    Handshake p (Function.update workers (p.parent v) { workers (p.parent v) with queue := rest })
      ⟨Function.update network.messages (p.parent v)
        (Function.update (network.messages (p.parent v)) v (some packet))⟩ := by
  classical
  have hpos : 0 < (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) := by
    simp [hqueue]
  have hfree := down_free_of_queued p workers network h v hv hpos
  intro child hc
  by_cases he : child = v
  · subst child
    have hn := parent_ne_self p hp v hv
    have hload := h v hv
    simp [edgeLoad, hqueue, hfree] at hload
    simp [edgeLoad, Function.update, Ne.symm hn]
    omega
  · have hreverse : ¬ (p.parent child = v ∧ p.parent v = child) := by
      intro hr
      exact no_reverse_edge p hp child v hc hv hr.1 hr.2
    have hload := h child hc
    have hev : v ≠ child := Ne.symm he
    by_cases hpc : p.parent child = v <;>
      by_cases hcv : child = p.parent v <;>
      by_cases hpp : p.parent child = p.parent v <;>
      simp_all [edgeLoad, Function.update]

lemma relay_queue_count (p : Params) (v child : Fin p.n) (s : State p) (values : Fin p.d → ℕ) :
    (relay p v s values).queue.countP (fun packet => decide (packet.1 = child)) =
      if child ∈ children p v then 1 else 0 := by
  classical
  change ((children p v).toList.map _).countP _ = _
  simp only [List.countP_map, Function.comp_def]
  change (children p v).toList.count child = _
  by_cases hc : child ∈ children p v
  · rw [ite_eq_left hc]
    exact List.count_eq_one_of_mem (children p v).nodup_toList (by simpa using hc)
  · rw [ite_eq_right hc]
    exact List.count_eq_zero_of_not_mem (by simpa using hc)

lemma finishBroadcast_seen_empty (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (ha : DistributedJacobianStrongGrowthPhases.Active s.phase) :
    (finishBroadcast p s values).collector.seen = ∅ := by
  cases hs : s.phase <;> simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
  · simp only [finishBroadcast, hs]
    split_ifs
    · rfl
    · unfold startRefinement
      split_ifs <;> rfl
  · simp only [finishBroadcast, hs]
    unfold startRefinement
    split_ifs <;> rfl

lemma handshake_relay_root (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (ha : DistributedJacobianStrongGrowthPhases.Active (workers p.root).phase)
    (hseen : (workers p.root).collector.seen = children p p.root)
    (hqueue : (workers p.root).queue = []) (values : Fin p.d → ℕ) :
    Handshake p (Function.update workers p.root (relay p p.root (workers p.root) values)) network := by
  classical
  have hnew : (relay p p.root (workers p.root) values).collector.seen = ∅ :=
    finishBroadcast_seen_empty p (workers p.root) values ha
  intro child hc
  have hload := h child hc
  by_cases hp : p.parent child = p.root
  · simpa [edgeLoad, Function.update, hc, hp, hseen, hqueue, hnew, relay_queue_count,
      children] using hload
  · simpa [edgeLoad, Function.update, hc, hp] using hload

lemma handshake_receive_down (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root)
    (ha : DistributedJacobianStrongGrowthPhases.ActiveShape p (workers v))
    (hseen : (workers v).collector.seen = children p v)
    (hqueue : (workers v).queue = []) (values : Fin p.d → ℕ)
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpacket : network.messages (p.parent v) v = some (finish, bits)) :
    Handshake p (Function.update workers v (relay p v (workers v) values))
      ⟨Function.update network.messages (p.parent v)
        (Function.update (network.messages (p.parent v)) v none)⟩ := by
  classical
  have hsent := down_pending_sent p workers network h v hv finish bits hpacket
  have hactive := ha (Or.inr hsent)
  have hnew : (relay p v (workers v) values).collector.seen = ∅ :=
    finishBroadcast_seen_empty p (workers v) values hactive
  have hns : (relay p v (workers v) values).sent = false :=
    DistributedJacobianStrongGrowthPhases.finishBroadcast_sent_false p (workers v) values ha
  intro child hc
  have hload := h child hc
  by_cases he : child = v
  · subst child
    have hn := parent_ne_self p hp v hv
    unfold edgeLoad at hload
    rw [hpacket, hsent] at hload
    simp only [Option.isSome_some, Bool.toNat_true] at hload
    have hz : (network.messages v (p.parent v)).isSome.toNat +
        (if v ∈ (workers (p.parent v)).collector.seen then 1 else 0) +
        (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) = 0 := by omega
    simpa [edgeLoad, Function.update, hn, Ne.symm hn, hns] using hz
  · have hev : v ≠ child := Ne.symm he
    have hreverse : ¬ (p.parent child = v ∧ p.parent v = child) := by
      intro hr
      exact no_reverse_edge p hp child v hc hv hr.1 hr.2
    have hn := parent_ne_self p hp v hv
    have hnc := parent_ne_self p hp child hc
    by_cases hpc : p.parent child = v <;>
      by_cases hcv : child = p.parent v <;>
      by_cases hpp : p.parent child = p.parent v <;>
      simp_all [edgeLoad, Function.update, relay_queue_count]

lemma handshake_congr (p : Params) (workers next : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (hs : ∀ v, (next v).sent = (workers v).sent)
    (hc : ∀ v, (next v).collector.seen = (workers v).collector.seen)
    (hq : ∀ v, (next v).queue = (workers v).queue) : Handshake p next network := by
  intro child hn
  simpa only [edgeLoad, hs, hc, hq] using h child hn

def NetworkEdges (p : Params) (network : CommunicationState p) : Prop :=
  ∀ source target packet, network.messages source target = some packet → adjacent p source target

lemma networkEdges_initial (p : Params) (S : Sampling p) (seed : S.Seed) :
    NetworkEdges p ((communication p S).initial seed) := by
  intro source target packet h
  simp [communication] at h

lemma networkEdges_insert (p : Params) (network : CommunicationState p)
    (h : NetworkEdges p network) (source target : Fin p.n)
    (packet : DistributedTemplate.Time × List Bool) (hadj : adjacent p source target) :
    NetworkEdges p ⟨Function.update network.messages source
      (Function.update (network.messages source) target (some packet))⟩ := by
  classical
  intro a b value hv
  by_cases ha : a = source
  · subst a
    by_cases hb : b = target
    · subst b
      exact hadj
    · exact h source b value (by simpa [Function.update, hb] using hv)
  · exact h a b value (by simpa [Function.update, ha] using hv)

lemma networkEdges_erase (p : Params) (network : CommunicationState p)
    (h : NetworkEdges p network) (source target : Fin p.n) :
    NetworkEdges p ⟨Function.update network.messages source
      (Function.update (network.messages source) target none)⟩ := by
  classical
  intro a b value hv
  by_cases ha : a = source
  · subst a
    by_cases hb : b = target
    · subst b
      simp [Function.update] at hv
    · exact h source b value (by simpa [Function.update, hb] using hv)
  · exact h a b value (by simpa [Function.update, ha] using hv)

lemma networkEdges_submit (p : Params) (S : Sampling p) (network : CommunicationState p)
    (h : NetworkEdges p network) (time : DistributedTemplate.Time)
    (source target : Fin p.n) (bits : List Bool) :
    NetworkEdges p ((communication p S).submit network time source (target, bits)) := by
  classical
  by_cases hadj : adjacent p source target
  · cases hs : network.messages source target with
    | none =>
        rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time source target bits hadj hs]
        exact networkEdges_insert p network h source target _ hadj
    | some packet => simpa [communication, hadj, hs] using h
  · simpa [communication, hadj] using h

lemma networkEdges_answer (p : Params) (S : Sampling p) (network next : CommunicationState p)
    (h : NetworkEdges p network) (time : DistributedTemplate.Time)
    (source target : Fin p.n) (bits : List Bool)
    (hanswer : (communication p S).answer network time = some ((target, ⟨source, bits⟩), next)) :
    adjacent p source target ∧ NetworkEdges p next := by
  obtain ⟨finish, hstored, _, rfl⟩ :=
    DistributedJacobianStrongGrowthOracle.communication_received_data p S network next time source target bits hanswer
  exact ⟨h source target _ hstored, networkEdges_erase p network h source target⟩

end LongTails.Proofs.DistributedJacobianStrongGrowthConservation
