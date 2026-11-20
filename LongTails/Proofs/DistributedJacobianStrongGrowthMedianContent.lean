import LongTails.Proofs.DistributedJacobianStrongGrowthMedianState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianContent

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthMedianReference
open DistributedJacobianStrongGrowthMedianState

noncomputable def medianDecision (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) : Fin p.d → ℕ :=
  fun j => if (p.n : ℕ) / 2 < subtreeValues p p.root (medianValues p codes epoch) j then 1 else 0

lemma medianDecision_fits (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) :
    ∀ j, medianDecision p codes epoch j < 2 ^ 1 := by
  intro j
  unfold medianDecision
  split_ifs <;> decide

structure MedianContent (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p) : Prop where
  states : ∀ v, MedianState p codes v (workers v)
  collectors : ∀ v, epochIndex p (workers v).phase < warmWidth p (localDepth p) →
    CollectorCorrect p v (medianValues p codes (epochIndex p (workers v).phase)) (workers v).collector
  upward : ∀ child, child ≠ p.root → ∀ finish bits,
    network.messages child (p.parent child) = some (finish, bits) →
    epochIndex p (workers child).phase < warmWidth p (localDepth p) →
    bits = naturalMessage (countWidth p.n)
      (subtreeValues p child (medianValues p codes (epochIndex p (workers child).phase))) ++
        List.replicate 64 false
  downward : ∀ child, child ≠ p.root → ∀ finish bits,
    network.messages (p.parent child) child = some (finish, bits) →
    epochIndex p (workers child).phase < warmWidth p (localDepth p) →
    bits = naturalMessage 1 (medianDecision p codes (epochIndex p (workers child).phase)) ++
      List.replicate 64 false
  queued : ∀ v child bits, (child, bits) ∈ (workers v).queue →
    epochIndex p (workers v).phase ≤ warmWidth p (localDepth p) →
    bits = naturalMessage 1 (medianDecision p codes (epochIndex p (workers v).phase - 1))

lemma medianContent_initial (p : Params) (S : Sampling p) (seed : S.Seed)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    MedianContent p codes (initialState p) ((communication p S).initial seed) := by
  constructor
  · exact medianState_initial p codes
  · intro v _
    simpa only [initialState, ite_eq_right (not_le.mpr hε), ite_eq_left hrich, epochIndex] using
      collectorCorrect_empty p v (medianValues p codes 0)
  · intro child hc finish bits hpending
    simp [communication] at hpending
  · intro child hc finish bits hpending
    simp [communication] at hpending
  · intro v child bits hmem
    simp [initialState, not_le.mpr hε, hrich] at hmem

lemma medianContent_decode_up (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (finish : Time) (bits : List Bool) (hpending : network.messages child (p.parent child) = some (finish, bits))
    (he : epochIndex p (workers child).phase < warmWidth p (localDepth p)) :
    receiveNaturals p.d (countWidth p.n) bits =
      subtreeValues p child (medianValues p codes (epochIndex p (workers child).phase)) := by
  rw [h.upward child hc finish bits hpending he]
  exact LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message _ _
    (median_subtree_fits p child codes _) _

lemma medianContent_decode_down (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (finish : Time) (bits : List Bool) (hpending : network.messages (p.parent child) child = some (finish, bits))
    (he : epochIndex p (workers child).phase < warmWidth p (localDepth p)) :
    receiveNaturals p.d 1 bits = medianDecision p codes (epochIndex p (workers child).phase) := by
  rw [h.downward child hc finish bits hpending he]
  exact LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message _ _
    (medianDecision_fits p codes _) _

lemma medianContent_congr (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers next : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hphase : ∀ v, (next v).phase = (workers v).phase)
    (hlower : ∀ v, (next v).lower = (workers v).lower)
    (hown : ∀ v, (next v).own = (workers v).own)
    (hcollector : ∀ v, (next v).collector = (workers v).collector)
    (hqueue : ∀ v, (next v).queue = (workers v).queue) :
    MedianContent p codes next network := by
  constructor
  · intro v
    exact medianState_congr p codes v _ _ (hphase v) (hlower v) (hown v) (h.states v)
  · intro v he
    rw [hphase] at he
    simpa only [hphase, hcollector] using h.collectors v he
  · intro child hc finish bits hpending he
    rw [hphase] at he
    simpa only [hphase] using h.upward child hc finish bits hpending he
  · intro child hc finish bits hpending he
    rw [hphase] at he
    simpa only [hphase] using h.downward child hc finish bits hpending he
  · intro v child bits hmem he
    rw [hqueue] at hmem
    rw [hphase] at he
    simpa only [hphase] using h.queued v child bits hmem he

lemma medianContent_network_sub (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network next : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hsub : ∀ u v packet, next.messages u v = some packet → network.messages u v = some packet) :
    MedianContent p codes workers next := by
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc finish bits hpending he
    exact h.upward child hc finish bits (hsub _ _ _ hpending) he
  · intro child hc finish bits hpending he
    exact h.downward child hc finish bits (hsub _ _ _ hpending) he
  · exact h.queued

lemma medianContent_computed (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (i : Fin p.n) (value : Point p) :
    MedianContent p codes (Function.update workers i (update p i (workers i) (.computed value))) network := by
  classical
  apply medianContent_congr p codes workers _ network h
  all_goals
    intro v
    by_cases hv : v = i
    · subst v
      cases hw : (workers i).work <;> cases hb : (workers i).busy <;>
        simp [Function.update, update, hw, hb]
    · simp [Function.update, hv]

lemma medianContent_send_up (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root) (finish : Time) :
    MedianContent p codes workers
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v)
        (some (finish, naturalMessage (countWidth p.n)
          (subtreeValues p v (medianValues p codes (epochIndex p (workers v).phase))) ++
            List.replicate 64 false)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending he
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm
    · exact h.upward child hc time bits (by simpa [Function.update, hcv] using hpending) he
  · intro child hc time bits hpending he
    by_cases hpc : p.parent child = v
    · have hcv : child ≠ p.parent v := by
        intro heq
        exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child v hc hv hpc heq.symm
      exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) he
    · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) he
  · exact h.queued

lemma medianContent_send_down (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root) (finish : Time) :
    MedianContent p codes workers
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v
        (some (finish, naturalMessage 1
          (medianDecision p codes (epochIndex p (workers v).phase)) ++ List.replicate 64 false)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending he
    by_cases hcp : child = p.parent v
    · have hpc : p.parent child ≠ v := by
        exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp v child hv hc hcp.symm
      have hn : p.parent (p.parent v) ≠ v := by simpa only [hcp] using hpc
      exact h.upward child hc time bits (by simpa [Function.update, hcp, hn] using hpending) he
    · exact h.upward child hc time bits (by simpa [Function.update, hcp] using hpending) he
  · intro child hc time bits hpending he
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm
    · by_cases hpc : p.parent child = p.parent v
      · exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) he
      · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) he
  · exact h.queued

lemma medianContent_erase (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (source target : Fin p.n) :
    MedianContent p codes workers
      ⟨Function.update network.messages source (Function.update (network.messages source) target none)⟩ := by
  classical
  apply medianContent_network_sub p codes workers network _ h
  intro u v packet hpending
  by_cases hu : u = source
  · subst u
    by_cases hv : v = target
    · simp [Function.update, hv] at hpending
    · simpa [Function.update, hv] using hpending
  · simpa [Function.update, hu] using hpending

lemma medianContent_queued_epoch (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool) (rest : List (Fin p.n × List Bool))
    (hq : (workers (p.parent v)).queue = (v, bits) :: rest)
    (he : epochIndex p (workers v).phase < warmWidth p (localDepth p)) :
    bits = naturalMessage 1 (medianDecision p codes (epochIndex p (workers v).phase)) := by
  have hpos : 0 < (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) := by
    simp [hq]
  have hf := DistributedJacobianStrongGrowthHandshake.down_free_of_queued p workers network hh v hv hpos
  have hb := hh v hv
  unfold DistributedJacobianStrongGrowthHandshake.edgeLoad at hb
  have hcount : (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) = 1 := by
    cases hs : (workers v).sent <;> simp only [hs, Bool.toNat_false, Bool.toNat_true] at hb <;> omega
  have ho' := ho v hv
  simp only [DistributedJacobianStrongGrowthEpochOrdering.downLoad, hcount, hf,
    Option.isSome_none, Bool.toNat_false, Nat.add_zero] at ho'
  have hbits := h.queued (p.parent v) v bits (by simp [hq]) (by omega)
  simpa only [ho', Nat.add_sub_cancel] using hbits

lemma medianContent_set_collector (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n)
    (collector : LongTails.Algorithms.DistributedLocalExtragradientTree.Collector p.n p.d)
    (hc : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      CollectorCorrect p v (medianValues p codes (epochIndex p (workers v).phase)) collector) :
    MedianContent p codes (Function.update workers v { workers v with collector := collector }) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update, MedianState] using h.states v
    · simpa [Function.update, hi] using h.states i
  · intro i he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hc (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.collectors i (by simpa [Function.update, hi] using he)
  · intro child hchild finish bits hpending he
    by_cases hv : child = v
    · subst child
      simpa [Function.update] using h.upward v hchild finish bits hpending (by simpa [Function.update] using he)
    · simpa [Function.update, hv] using h.upward child hchild finish bits hpending (by simpa [Function.update, hv] using he)
  · intro child hchild finish bits hpending he
    by_cases hv : child = v
    · subst child
      simpa [Function.update] using h.downward v hchild finish bits hpending (by simpa [Function.update] using he)
    · simpa [Function.update, hv] using h.downward child hchild finish bits hpending (by simpa [Function.update, hv] using he)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using h.queued v child bits (by simpa [Function.update] using hmem)
        (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

lemma medianContent_accept (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v child : Fin p.n) (values : Fin p.d → ℕ)
    (hvalues : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      values = subtreeValues p child (medianValues p codes (epochIndex p (workers v).phase))) :
    MedianContent p codes (Function.update workers v { workers v with collector :=
        (LongTails.Algorithms.DistributedLocalExtragradientTree.accept
          (LongTails.Algorithms.DistributedLocalExtragradientTree.children p v)
          (workers v).collector child values) }) network := by
  apply medianContent_set_collector p codes workers network h v
  intro he
  rw [hvalues he]
  exact collectorCorrect_accept p v _ _ (h.collectors v he) child

lemma upWidth_of_early_epoch (p : Params) (phase : Phase) (hn : phase ≠ .baseline)
    (he : epochIndex p phase < warmWidth p (localDepth p)) : upWidth p phase = countWidth p.n := by
  cases phase <;> simp_all [epochIndex, upWidth]

lemma medianContent_receive_up (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (child : Fin p.n) (hc : child ≠ p.root) (finish : Time) (bits : List Bool)
    (hpending : network.messages child (p.parent child) = some (finish, bits))
    (hn : (workers (p.parent child)).phase ≠ .baseline) :
    MedianContent p codes (Function.update workers (p.parent child)
      (update p (p.parent child) (workers (p.parent child)) (.received ⟨child, bits⟩)))
      ⟨Function.update network.messages child (Function.update (network.messages child) (p.parent child) none)⟩ := by
  classical
  have hreverse : ¬ (p.parent child ≠ p.root ∧ child = p.parent (p.parent child)) := by
    intro hr
    exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child (p.parent child)
      hc hr.1 rfl hr.2.symm
  have hepoch := DistributedJacobianStrongGrowthEpochOrdering.epoch_eq_of_up p workers network hh ho
    child hc (finish, bits) hpending
  have haccept := medianContent_accept p codes workers network h (p.parent child) child
    (receiveNaturals p.d (upWidth p (workers (p.parent child)).phase) bits) (by
      intro he
      rw [upWidth_of_early_epoch p _ hn he, hepoch]
      exact medianContent_decode_up p codes workers network h child hc finish bits hpending
        (by simpa only [hepoch] using he))
  have herase := medianContent_erase p codes _ network haccept child (p.parent child)
  simpa only [update, ite_eq_right hreverse] using herase

lemma medianContent_replace (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (next : State p)
    (hclear : v ≠ p.root → network.messages v (p.parent v) = none ∧
      network.messages (p.parent v) v = none)
    (hstate : MedianState p codes v next)
    (hcollector : epochIndex p next.phase < warmWidth p (localDepth p) →
      CollectorCorrect p v (medianValues p codes (epochIndex p next.phase)) next.collector)
    (hqueue : ∀ child bits, (child, bits) ∈ next.queue →
      epochIndex p next.phase ≤ warmWidth p (localDepth p) →
      bits = naturalMessage 1 (medianDecision p codes (epochIndex p next.phase - 1))) :
    MedianContent p codes (Function.update workers v next) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hstate
    · simpa [Function.update, hi] using h.states i
  · intro i he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hcollector (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.collectors i (by simpa [Function.update, hi] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      rw [(hclear hc).1] at hpending
      cases hpending
    · simpa [Function.update, hv] using h.upward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      rw [(hclear hc).2] at hpending
      cases hpending
    · simpa [Function.update, hv] using h.downward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hqueue child bits (by simpa [Function.update] using hmem)
        (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianContent
