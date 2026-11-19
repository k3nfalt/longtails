import LongTails.Proofs.DistributedJacobianStrongGrowthPhases
import LongTails.Proofs.DistributedJacobianStrongGrowthOracle

namespace LongTails.Proofs.DistributedJacobianStrongGrowthHandshake

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

noncomputable def edgeLoad (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (child : Fin p.n) : ℕ := by
  classical
  exact (network.messages child (p.parent child)).isSome.toNat +
    (if child ∈ (workers (p.parent child)).collector.seen then 1 else 0) +
    (workers (p.parent child)).queue.countP (fun packet => decide (packet.1 = child)) +
    (network.messages (p.parent child) child).isSome.toNat

def Handshake (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p) : Prop :=
  ∀ child, child ≠ p.root → edgeLoad p workers network child = (workers child).sent.toNat

lemma initial_bookkeeping (p : Params) (v : Fin p.n) :
    (initialState p v).sent = false ∧ (initialState p v).collector.seen = ∅ ∧
      (initialState p v).queue = [] := by
  unfold initialState
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

lemma handshake_initial (p : Params) (S : Sampling p) (seed : S.Seed) :
    Handshake p (initialState p) ((communication p S).initial seed) := by
  classical
  intro child _
  have hc := initial_bookkeeping p child
  have hp := initial_bookkeeping p (p.parent child)
  simp [edgeLoad, communication, hc.1, hp.2.1, hp.2.2]

lemma down_pending_sent (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent child) child = some (finish, bits)) :
    (workers child).sent = true := by
  have he := h child hc
  unfold edgeLoad at he
  rw [hpending] at he
  cases hs : (workers child).sent <;> simp [hs] at he ⊢

lemma up_free_of_not_sent (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (hsent : (workers child).sent = false) : network.messages child (p.parent child) = none := by
  have he := h child hc
  unfold edgeLoad at he
  rw [hsent] at he
  cases hpending : network.messages child (p.parent child) with
  | none => rfl
  | some packet => simp [hpending] at he

lemma down_pending_idle (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network)
    (hshape : ∀ v, DistributedJacobianStrongGrowthPhases.ReadyShape p (workers v))
    (child : Fin p.n) (hc : child ≠ p.root) (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent child) child = some (finish, bits)) :
    (workers child).busy = false :=
  (hshape child (Or.inr (down_pending_sent p workers network h child hc finish bits hpending))).2

lemma down_pending_queue_empty (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (hshape : ∀ v, DistributedJacobianStrongGrowthPhases.SentQueue p (workers v))
    (child : Fin p.n) (hc : child ≠ p.root) (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent child) child = some (finish, bits)) :
    (workers child).queue = [] :=
  hshape child (down_pending_sent p workers network h child hc finish bits hpending)

lemma up_pending_unseen (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (child : Fin p.n) (hc : child ≠ p.root) (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages child (p.parent child) = some (finish, bits)) :
    child ∉ (workers (p.parent child)).collector.seen := by
  classical
  intro hseen
  have he := h child hc
  unfold edgeLoad at he
  rw [hpending, ite_eq_left hseen] at he
  cases hs : (workers child).sent
  · simp [hs] at he
  · simp [hs] at he
    omega

lemma down_free_of_queued (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (child : Fin p.n) (hc : child ≠ p.root)
    (hq : 0 < (workers (p.parent child)).queue.countP (fun packet => decide (packet.1 = child))) :
    network.messages (p.parent child) child = none := by
  classical
  have he := h child hc
  unfold edgeLoad at he
  cases hpending : network.messages (p.parent child) child with
  | none => rfl
  | some packet =>
      rw [hpending] at he
      cases hs : (workers child).sent <;> simp only [hs, Option.isSome_some, Bool.toNat_true, Bool.toNat_false] at he <;> omega

end LongTails.Proofs.DistributedJacobianStrongGrowthHandshake
