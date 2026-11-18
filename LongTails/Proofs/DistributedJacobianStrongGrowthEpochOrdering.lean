import LongTails.Proofs.DistributedJacobianStrongGrowthPhaseProgress

namespace LongTails.Proofs.DistributedJacobianStrongGrowthEpochOrdering

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthConservation

noncomputable def downLoad (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (child : Fin p.n) : ℕ :=
  (workers (p.parent child)).queue.countP (fun packet => decide (packet.1 = child)) +
    (network.messages (p.parent child) child).isSome.toNat

def EpochOrdering (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p) : Prop :=
  ∀ child, child ≠ p.root → epochIndex p (workers (p.parent child)).phase =
    epochIndex p (workers child).phase + downLoad p workers network child

lemma epochOrdering_initial (p : Params) (S : Sampling p) (seed : S.Seed)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    EpochOrdering p (initialState p) ((communication p S).initial seed) := by
  intro child _
  simp [epochIndex, initialState, not_le.mpr hε, hrich, downLoad, communication]

lemma downLoad_zero_of_up (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (child : Fin p.n) (hc : child ≠ p.root) (packet : DistributedTemplate.Time × List Bool)
    (hpacket : network.messages child (p.parent child) = some packet) :
    downLoad p workers network child = 0 := by
  classical
  have he := h child hc
  unfold edgeLoad at he
  rw [hpacket] at he
  simp only [Option.isSome_some, Bool.toNat_true] at he
  unfold downLoad
  cases hs : (workers child).sent <;> simp only [hs, Bool.toNat_false, Bool.toNat_true] at he <;> omega

lemma downLoad_zero_of_seen (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (child : Fin p.n) (hc : child ≠ p.root)
    (hseen : child ∈ (workers (p.parent child)).collector.seen) :
    downLoad p workers network child = 0 := by
  classical
  have he := h child hc
  unfold edgeLoad at he
  rw [ite_eq_left hseen] at he
  unfold downLoad
  cases hs : (workers child).sent <;> simp only [hs, Bool.toNat_false, Bool.toNat_true] at he <;> omega

lemma downLoad_one_of_down (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (child : Fin p.n) (hc : child ≠ p.root) (packet : DistributedTemplate.Time × List Bool)
    (hpacket : network.messages (p.parent child) child = some packet) :
    downLoad p workers network child = 1 := by
  classical
  have he := h child hc
  unfold edgeLoad at he
  rw [hpacket] at he
  simp only [Option.isSome_some, Bool.toNat_true] at he
  unfold downLoad
  rw [hpacket]
  simp only [Option.isSome_some, Bool.toNat_true]
  cases hs : (workers child).sent <;> simp only [hs, Bool.toNat_false, Bool.toNat_true] at he <;> omega

lemma epoch_eq_of_up (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (ho : EpochOrdering p workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (packet : DistributedTemplate.Time × List Bool)
    (hpacket : network.messages child (p.parent child) = some packet) :
    epochIndex p (workers (p.parent child)).phase = epochIndex p (workers child).phase := by
  simpa only [downLoad_zero_of_up p workers network h child hc packet hpacket, Nat.add_zero] using ho child hc

lemma epochOrdering_congr (p : Params) (workers next : Fin p.n → State p)
    (network nextNetwork : CommunicationState p) (h : EpochOrdering p workers network)
    (hi : ∀ v, epochIndex p (next v).phase = epochIndex p (workers v).phase)
    (hq : ∀ v, (next v).queue = (workers v).queue)
    (hn : ∀ child, child ≠ p.root → nextNetwork.messages (p.parent child) child = network.messages (p.parent child) child) :
    EpochOrdering p next nextNetwork := by
  intro child hc
  simpa only [downLoad, hi, hq, hn child hc] using h child hc

lemma up_write_preserves_down (p : Params) (hp : valid p) (network : CommunicationState p)
    (v : Fin p.n) (hv : v ≠ p.root) (value : Option (DistributedTemplate.Time × List Bool))
    (child : Fin p.n) (hc : child ≠ p.root) :
    (Function.update network.messages v (Function.update (network.messages v) (p.parent v) value))
      (p.parent child) child = network.messages (p.parent child) child := by
  classical
  by_cases hpc : p.parent child = v
  · have hn := no_reverse_edge p hp child v hc hv hpc
    simp [Function.update, hpc, Ne.symm hn]
  · simp [Function.update, hpc]

lemma epochOrdering_send_up (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (packet : DistributedTemplate.Time × List Bool) :
    EpochOrdering p (Function.update workers v { workers v with sent := true })
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v) (some packet))⟩ := by
  classical
  apply epochOrdering_congr p workers _ network _ h
  · intro u
    by_cases hu : u = v <;> simp_all [Function.update]
  · intro u
    by_cases hu : u = v <;> simp_all [Function.update]
  · exact up_write_preserves_down p hp network v hv _

lemma epochOrdering_receive_up (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (values : Fin p.d → ℕ) :
    EpochOrdering p
      (Function.update workers (p.parent v) { workers (p.parent v) with
        collector := accept (children p (p.parent v)) (workers (p.parent v)).collector v values })
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v) none)⟩ := by
  classical
  apply epochOrdering_congr p workers _ network _ h
  · intro u
    by_cases hu : u = p.parent v <;> simp_all [Function.update]
  · intro u
    by_cases hu : u = p.parent v <;> simp_all [Function.update]
  · exact up_write_preserves_down p hp network v hv _

lemma epochOrdering_send_down (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (ho : EpochOrdering p workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (bits : List Bool) (rest : List (Fin p.n × List Bool))
    (hqueue : (workers (p.parent v)).queue = (v, bits) :: rest)
    (packet : DistributedTemplate.Time × List Bool) :
    EpochOrdering p (Function.update workers (p.parent v) { workers (p.parent v) with queue := rest })
      ⟨Function.update network.messages (p.parent v)
        (Function.update (network.messages (p.parent v)) v (some packet))⟩ := by
  classical
  have hpos : 0 < (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) := by simp [hqueue]
  have hfree := down_free_of_queued p workers network h v hv hpos
  intro child hc
  have hepoch := ho child hc
  by_cases he : child = v
  · subst child
    have hn := parent_ne_self p hp v hv
    simpa [downLoad, Function.update, hn, Ne.symm hn, hqueue, hfree, Nat.add_assoc] using hepoch
  · have hev := Ne.symm he
    have hnc := parent_ne_self p hp child hc
    by_cases hcv : child = p.parent v <;>
      by_cases hpp : p.parent child = p.parent v <;>
      simp_all [downLoad, Function.update]

lemma epochOrdering_relay_root (p : Params) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (ho : EpochOrdering p workers network)
    (ha : DistributedJacobianStrongGrowthPhases.Active (workers p.root).phase)
    (hb : PhaseBounds p (workers p.root).phase)
    (hseen : (workers p.root).collector.seen = children p p.root)
    (hqueue : (workers p.root).queue = []) (values : Fin p.d → ℕ) :
    EpochOrdering p (Function.update workers p.root (relay p p.root (workers p.root) values)) network := by
  classical
  have hi : epochIndex p (relay p p.root (workers p.root) values).phase =
      epochIndex p (workers p.root).phase + 1 := epochIndex_finishBroadcast p _ values hb ha
  intro child hc
  have hepoch := ho child hc
  by_cases hp : p.parent child = p.root
  · have hchild : child ∈ children p p.root := by simp [children, hc, hp]
    have hs : child ∈ (workers (p.parent child)).collector.seen := by simpa only [hp, hseen] using hchild
    have hz := downLoad_zero_of_seen p workers network h child hc hs
    have hd : network.messages p.root child = none := by
      unfold downLoad at hz
      rw [hp, hqueue] at hz
      simpa using hz
    rw [hz, Nat.add_zero] at hepoch
    simp [downLoad, Function.update, hc, hp, hi, relay_queue_count, hchild, hd]
    simpa only [hp] using hepoch
  · simpa [downLoad, Function.update, hc, hp] using hepoch

lemma epochOrdering_receive_down (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (h : Handshake p workers network)
    (ho : EpochOrdering p workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (ha : DistributedJacobianStrongGrowthPhases.Active (workers v).phase)
    (hb : PhaseBounds p (workers v).phase)
    (hseen : (workers v).collector.seen = children p v) (hqueue : (workers v).queue = [])
    (values : Fin p.d → ℕ) (packet : DistributedTemplate.Time × List Bool)
    (hpacket : network.messages (p.parent v) v = some packet) :
    EpochOrdering p (Function.update workers v (relay p v (workers v) values))
      ⟨Function.update network.messages (p.parent v)
        (Function.update (network.messages (p.parent v)) v none)⟩ := by
  classical
  have hi : epochIndex p (relay p v (workers v) values).phase = epochIndex p (workers v).phase + 1 :=
    epochIndex_finishBroadcast p _ values hb ha
  have hn := parent_ne_self p hp v hv
  intro child hc
  have hepoch := ho child hc
  by_cases he : child = v
  · subst child
    have hd := downLoad_one_of_down p workers network h v hv packet hpacket
    have hq0 : (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) = 0 := by
      simpa [downLoad, hpacket] using hd
    rw [hd] at hepoch
    simpa [downLoad, Function.update, hn, Ne.symm hn, hi, hq0] using hepoch
  · by_cases hpc : p.parent child = v
    · have hchild : child ∈ children p v := by simp [children, hc, hpc]
      have hs : child ∈ (workers (p.parent child)).collector.seen := by simpa only [hpc, hseen] using hchild
      have hz := downLoad_zero_of_seen p workers network h child hc hs
      have hd : network.messages v child = none := by
        unfold downLoad at hz
        rw [hpc, hqueue] at hz
        simpa using hz
      rw [hz, Nat.add_zero] at hepoch
      simp [downLoad, Function.update, he, hpc, Ne.symm hn,
        hi, relay_queue_count, hchild, hd]
      simpa only [hpc] using hepoch
    · by_cases hpp : p.parent child = p.parent v
      · simpa [downLoad, Function.update, he, hpc, hpp, hn] using hepoch
      · simpa [downLoad, Function.update, he, hpc, hpp, hn] using hepoch

end LongTails.Proofs.DistributedJacobianStrongGrowthEpochOrdering
