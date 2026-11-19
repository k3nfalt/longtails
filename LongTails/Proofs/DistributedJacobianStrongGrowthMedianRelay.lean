import LongTails.Proofs.DistributedJacobianStrongGrowthMedianContent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianRelay

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.LocalExtragradientQuantization
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthMedianReference
open DistributedJacobianStrongGrowthMedianState
open DistributedJacobianStrongGrowthMedianContent

lemma medianDecision_broadcast (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (s : State p) (remaining : ℕ) (hs : s.phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hstate : MedianState p codes i s) :
    medianDecision p codes (epochIndex p s.phase) = broadcastValues p s.phase
      (fun j => LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countBelow codes j
        (s.lower j + 2 ^ (remaining - 1))) := by
  have hl := (hstate remaining hs).1
  have hr : warmWidth p (localDepth p) -
      (warmWidth p (localDepth p) - remaining + 1) = remaining - 1 := by omega
  funext j
  simp only [medianDecision, medianValues_root p hp, hs, epochIndex, hr, broadcastValues, hl]

lemma finishBroadcast_collector (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (ha : DistributedJacobianStrongGrowthPhases.Active s.phase) :
    (finishBroadcast p s values).collector = emptyCollector (fun _ => 0) := by
  cases hs : s.phase <;> simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
  · simp only [finishBroadcast, hs]
    split_ifs
    · rfl
    · unfold startRefinement
      split_ifs <;> rfl
  · simp only [finishBroadcast, hs]
    unfold startRefinement
    split_ifs <;> rfl

lemma medianContent_relay (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (remaining : ℕ)
    (hs : (workers v).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hcodes : (workers v).warmCodes = fun j => (codes v j).val)
    (hclear : v ≠ p.root → network.messages v (p.parent v) = none ∧
      network.messages (p.parent v) v = none) :
    MedianContent p codes (Function.update workers v
      (relay p v (workers v) (medianDecision p codes (epochIndex p (workers v).phase)))) network := by
  let values := medianDecision p codes (epochIndex p (workers v).phase)
  have ha : DistributedJacobianStrongGrowthPhases.Active (workers v).phase := by simp [hs, DistributedJacobianStrongGrowthPhases.Active]
  have hb : PhaseBounds p (workers v).phase := by simp [PhaseBounds, hs]; omega
  have hepoch := epochIndex_finishBroadcast p (workers v) values hb ha
  apply medianContent_replace p codes workers network h v _ hclear
  · change MedianState p codes v (finishBroadcast p (workers v) values)
    dsimp only [values]
    rw [medianDecision_broadcast p hp codes v (workers v) remaining hs hpos hle (h.states v)]
    exact medianState_broadcast p codes v remaining (workers v) hs hle (h.states v) hcodes
  · intro _
    change CollectorCorrect p v _ (finishBroadcast p (workers v) values).collector
    rw [finishBroadcast_collector p (workers v) values ha]
    exact collectorCorrect_empty p v _
  · intro child bits hmem _
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hmem
    have hbits : bits = naturalMessage (downWidth p (workers v).phase) values := (Prod.mk.inj hu).2.symm
    change bits = naturalMessage 1 (medianDecision p codes
      (epochIndex p (finishBroadcast p (workers v) values).phase - 1))
    rw [hepoch, Nat.add_sub_cancel]
    simpa only [downWidth, values, hs] using hbits

lemma median_root_values (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (remaining : ℕ)
    (hs : (workers p.root).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hfull : children p p.root ⊆ (workers p.root).collector.seen) :
    broadcastValues p (workers p.root).phase
      (fun j => (workers p.root).own j + (workers p.root).collector.total j) =
      medianDecision p codes (epochIndex p (workers p.root).phase) := by
  have he : epochIndex p (workers p.root).phase < warmWidth p (localDepth p) := by
    simp only [hs, epochIndex]
    omega
  have hown : (workers p.root).own =
      medianValues p codes (epochIndex p (workers p.root).phase) p.root := by
    simpa only [hs, epochIndex] using (h.states p.root remaining hs).2
  have htotal : (fun j => (workers p.root).own j + (workers p.root).collector.total j) =
      subtreeValues p p.root (medianValues p codes (epochIndex p (workers p.root).phase)) := by
    funext j
    rw [hown]
    exact collectorCorrect_complete p hp p.root _ _ (h.collectors p.root he) hfull j
  rw [htotal]
  funext j
  simp only [broadcastValues, hs, medianDecision]

lemma medianContent_relay_root (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (remaining : ℕ)
    (hs : (workers p.root).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hcodes : (workers p.root).warmCodes = fun j => (codes p.root j).val)
    (hfull : children p p.root ⊆ (workers p.root).collector.seen) :
    MedianContent p codes (Function.update workers p.root (relay p p.root (workers p.root)
      (broadcastValues p (workers p.root).phase
        (fun j => (workers p.root).own j + (workers p.root).collector.total j)))) network := by
  rw [median_root_values p hp codes workers network h remaining hs hpos hle hfull]
  exact medianContent_relay p hp codes workers network h p.root remaining hs hpos hle hcodes
    (fun hn => False.elim (hn rfl))

lemma medianContent_receive_down (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (remaining : ℕ)
    (hs : (workers v).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hcodes : (workers v).warmCodes = fun j => (codes v j).val)
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent v) v = some (finish, bits)) :
    MedianContent p codes (Function.update workers v
      (update p v (workers v) (.received ⟨p.parent v, bits⟩)))
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩ := by
  classical
  have he : epochIndex p (workers v).phase < warmWidth p (localDepth p) := by
    simp only [hs, epochIndex]
    omega
  have hd := medianContent_decode_down p codes workers network h v hv finish bits hpending he
  have hu : network.messages v (p.parent v) = none := by
    cases hstored : network.messages v (p.parent v) with
    | none => rfl
    | some packet =>
        have hb := hh v hv
        unfold DistributedJacobianStrongGrowthHandshake.edgeLoad at hb
        rw [hpending, hstored] at hb
        cases hsent : (workers v).sent <;>
          simp only [Option.isSome_some, Bool.toNat_true, hsent, Bool.toNat_false] at hb <;> omega
  let nextNetwork : CommunicationState p :=
    ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩
  have hn := DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv
  have herase := medianContent_erase p codes workers network h (p.parent v) v
  have hrelay := medianContent_relay p hp codes workers nextNetwork herase v remaining hs hpos hle hcodes
    (by intro _; simp [nextNetwork, Function.update, Ne.symm hn, hu])
  simp only [update]
  rw [ite_eq_left (show v ≠ p.root ∧ True from ⟨hv, trivial⟩)]
  rw [show downWidth p (workers v).phase = 1 by simp [downWidth, hs], hd]
  exact hrelay

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianRelay
