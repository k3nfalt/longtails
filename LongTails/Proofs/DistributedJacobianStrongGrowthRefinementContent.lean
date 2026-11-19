import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementBroadcast

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementContent

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementState

structure RefinementContent (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p) : Prop where
  states : ∀ v, RefinementState p g samples v (workers v)
  collectors : ∀ v epoch, (workers v).phase = .refinement epoch →
    CollectorCorrect p v (refinementValues p g samples epoch) (workers v).collector
  upward : ∀ child, child ≠ p.root → ∀ finish bits,
    network.messages child (p.parent child) = some (finish, bits) →
    ∀ epoch, (workers child).phase = .refinement epoch →
    bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
      (subtreeValues p child (refinementValues p g samples epoch)) ++ List.replicate 64 false
  downward : ∀ child, child ≠ p.root → ∀ finish bits,
    network.messages (p.parent child) child = some (finish, bits) →
    ∀ epoch, (workers child).phase = .refinement epoch →
    bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
      (subtreeValues p p.root (refinementValues p g samples epoch)) ++ List.replicate 64 false
  queued : ∀ v child bits, (child, bits) ∈ (workers v).queue →
    warmWidth p (localDepth p) < epochIndex p (workers v).phase →
    bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
      (subtreeValues p p.root (refinementValues p g samples
        (epochIndex p (workers v).phase - warmWidth p (localDepth p) - 1)))

lemma refinementContent_initial (p : Params) (S : Sampling p) (seed : S.Seed)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    RefinementContent p g samples (initialState p) ((communication p S).initial seed) := by
  constructor
  · exact fun v => refinementState_initial p g samples v hε hrich
  · intro v epoch hs
    simp [initialState, not_le.mpr hε, hrich] at hs
  · intro child hc finish bits hpending
    simp [communication] at hpending
  · intro child hc finish bits hpending
    simp [communication] at hpending
  · intro v child bits hmem
    simp [initialState, not_le.mpr hε, hrich] at hmem

lemma refinementContent_decode_up (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (finish : Time) (bits : List Bool) (hpending : network.messages child (p.parent child) = some (finish, bits))
    (epoch : ℕ) (hs : (workers child).phase = .refinement epoch) :
    receiveNaturals p.d (refinementWidth p (localDepth p) + countWidth p.n) bits =
      subtreeValues p child (refinementValues p g samples epoch) := by
  rw [h.upward child hc finish bits hpending epoch hs]
  exact LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message _ _
    (refinementSubtree_fits p g samples epoch child) _

lemma refinementContent_decode_down (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (finish : Time) (bits : List Bool) (hpending : network.messages (p.parent child) child = some (finish, bits))
    (epoch : ℕ) (hs : (workers child).phase = .refinement epoch) :
    receiveNaturals p.d (refinementWidth p (localDepth p) + countWidth p.n) bits =
      subtreeValues p p.root (refinementValues p g samples epoch) := by
  rw [h.downward child hc finish bits hpending epoch hs]
  exact LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message _ _
    (refinementSubtree_fits p g samples epoch p.root) _

lemma refinementContent_root_total (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (epoch : ℕ)
    (hs : (workers p.root).phase = .refinement epoch) (hw : (workers p.root).work = none)
    (hfull : LongTails.Algorithms.DistributedLocalExtragradientTree.children p p.root ⊆
      (workers p.root).collector.seen) :
    (fun j => (workers p.root).own j + (workers p.root).collector.total j) =
      subtreeValues p p.root (refinementValues p g samples epoch) := by
  have hown : (workers p.root).own = refinementValues p g samples epoch p.root := by
    simpa only [hw] using ((h.states p.root).1 epoch hs).2
  funext j
  rw [hown]
  exact collectorCorrect_complete p hp p.root _ _ (h.collectors p.root epoch hs) hfull j

lemma refinementContent_congr (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers next : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hstates : ∀ v, RefinementState p g samples v (next v))
    (href : ∀ v epoch, (next v).phase = .refinement epoch → (workers v).phase = .refinement epoch)
    (hepoch : ∀ v, epochIndex p (next v).phase = epochIndex p (workers v).phase)
    (hcollector : ∀ v, (next v).collector = (workers v).collector)
    (hqueue : ∀ v, (next v).queue ⊆ (workers v).queue) :
    RefinementContent p g samples next network := by
  constructor
  · exact hstates
  · intro v epoch hs
    simpa only [hcollector] using h.collectors v epoch (href v epoch hs)
  · intro child hc finish bits hpending epoch hs
    exact h.upward child hc finish bits hpending epoch (href child epoch hs)
  · intro child hc finish bits hpending epoch hs
    exact h.downward child hc finish bits hpending epoch (href child epoch hs)
  · intro v child bits hmem he
    rw [hepoch] at he
    simpa only [hepoch] using h.queued v child bits (hqueue v hmem) he

lemma refinementContent_network_sub (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network next : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hsub : ∀ u v packet, next.messages u v = some packet → network.messages u v = some packet) :
    RefinementContent p g samples workers next := by
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc finish bits hpending epoch hs
    exact h.upward child hc finish bits (hsub _ _ _ hpending) epoch hs
  · intro child hc finish bits hpending epoch hs
    exact h.downward child hc finish bits (hsub _ _ _ hpending) epoch hs
  · exact h.queued

lemma refinementContent_erase (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (source target : Fin p.n) :
    RefinementContent p g samples workers
      ⟨Function.update network.messages source (Function.update (network.messages source) target none)⟩ := by
  classical
  apply refinementContent_network_sub p g samples workers network _ h
  intro u v packet hpending
  by_cases hu : u = source
  · subst u
    by_cases hv : v = target
    · simp [Function.update, hv] at hpending
    · simpa [Function.update, hv] using hpending
  · simpa [Function.update, hu] using hpending

lemma refinementContent_computed (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (S : Sampling p)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (i : Fin p.n)
    (oracle next : ComputationState p) (time : Time) (value : Point p)
    (ha : DistributedJacobianStrongGrowthQueryAccounting.Accounted p (workers i) oracle.used)
    (hm : DistributedJacobianStrongGrowthExecution.PendingMatches p (workers i) oracle)
    (hsamples : oracle.samples = samples)
    (hanswer : (computation p g S).answer i oracle time = some (value, next)) :
    RefinementContent p g samples
      (Function.update workers i (update p i (workers i) (.computed value))) network := by
  classical
  apply refinementContent_congr p g samples workers _ network h
  · intro v
    by_cases hv : v = i
    · subst v
      simpa only [Function.update_self] using refinementState_computed p g samples S i (workers i)
        oracle next time value (h.states i) ha hm hsamples hanswer
    · simpa [Function.update, hv] using h.states v
  · intro v epoch hs
    by_cases hv : v = i
    · subst v
      simpa only [Function.update_self, (refinement_computed_fields p i (workers i) value).1] using hs
    · simpa [Function.update, hv] using hs
  all_goals
    intro v
    by_cases hv : v = i
    · subst v
      cases hw : (workers i).work <;> cases hb : (workers i).busy <;>
        simp [Function.update, update, hw, hb]
    · simp [Function.update, hv]

lemma refinementContent_finishLocal (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (i : Fin p.n)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (hn : (workers i).phase ≠ .baseline) (hw : (workers i).work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none) :
    RefinementContent p g samples (Function.update workers i
      (finishLocal p (workers i) (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work))) network := by
  classical
  apply refinementContent_congr p g samples workers _ network h
  · intro v
    by_cases hv : v = i
    · subst v
      simpa only [Function.update_self] using refinementState_finishLocal p g samples i (workers i)
        work (h.states i) hn hw hq
    · simpa [Function.update, hv] using h.states v
  · intro v epoch hs
    by_cases hv : v = i
    · subst v
      simp only [Function.update_self] at hs
      cases hp : (workers i).phase <;> simp_all [finishLocal, startMedian]
    · simpa [Function.update, hv] using hs
  · intro v
    by_cases hv : v = i
    · subst v
      simpa only [Function.update_self] using epochIndex_finishLocal p (workers i) _ hn
    · simp [Function.update, hv]
  · intro v
    by_cases hv : v = i
    · subst v
      simpa only [Function.update_self] using
        DistributedJacobianStrongGrowthProtocol.finishLocal_preserves_collector p (workers i) _
    · simp [Function.update, hv]
  · intro v
    by_cases hv : v = i
    · subst v
      simp only [Function.update_self, DistributedJacobianStrongGrowthNetworkExecution.finishLocal_queue]
      exact fun _ hi => hi
    · simp [Function.update, hv]

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementContent
