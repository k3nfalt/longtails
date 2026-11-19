import LongTails.Proofs.DistributedJacobianStrongGrowthEpochExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthMedianSearch

namespace LongTails.Proofs.DistributedJacobianStrongGrowthPayload

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthEpochExecution

lemma up_pending_sent (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network) (child : Fin p.n) (hc : child ≠ p.root)
    (packet : Time × List Bool) (hpending : network.messages child (p.parent child) = some packet) :
    (workers child).sent = true := by
  have he := h child hc
  unfold edgeLoad at he
  rw [hpending] at he
  cases hs : (workers child).sent <;> simp [hs] at he ⊢

lemma upWidth_of_equal_epoch (p : Params) (sender receiver : Phase)
    (hs : PhaseBounds p sender) (hr : PhaseBounds p receiver)
    (ha : Active sender) (hn : receiver ≠ .baseline)
    (he : epochIndex p sender = epochIndex p receiver) : upWidth p sender = upWidth p receiver := by
  have hw := warmWidth_pos p
  cases sender <;> cases receiver <;> simp_all [PhaseBounds, Active, epochIndex, upWidth] <;> omega

lemma pending_up_width (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : Handshake p workers network) (ho : EpochOrdering p workers network)
    (hb : ∀ v, PhaseBounds p (workers v).phase)
    (hn : ∀ v, (workers v).phase ≠ .baseline)
    (ha : ∀ v, ActiveShape p (workers v))
    (child : Fin p.n) (hc : child ≠ p.root) (packet : Time × List Bool)
    (hpending : network.messages child (p.parent child) = some packet) :
    upWidth p (workers child).phase = upWidth p (workers (p.parent child)).phase := by
  exact upWidth_of_equal_epoch p _ _ (hb child) (hb (p.parent child))
    (ha child (Or.inr (up_pending_sent p workers network h child hc packet hpending)))
    (hn (p.parent child)) (epoch_eq_of_up p workers network h ho child hc packet hpending).symm

lemma pending_up_width_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (child : Fin p.n) (hc : child ≠ p.root) (packet : Time × List Bool)
    (hpending : (run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).oracle.communication.messages
        child (p.parent child) = some packet) :
    let c := run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)
    upWidth p (c.workers child).phase = upWidth p (c.workers (p.parent child)).phase := by
  exact pending_up_width p _ _ (network_initial_run p hp g S idle deadline seed k).1
    (epochOrdering_initial_run p hp g S idle deadline seed k hε hrich)
    (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
    (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich)
    (fun v => (localShape_initial_run p g S idle deadline seed k v).2.1)
    child hc packet hpending

open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.DistributedQuantization

noncomputable def lowerAfter {n d width : ℕ} (codes : Fin n → Grid d width) : ℕ → Fin d → ℕ
  | 0 => fun _ => 0
  | k + 1 => nextLower (width - (k + 1)) (lowerAfter codes k)
      (fun j => decide (n / 2 < countBelow codes j (lowerAfter codes k j + 2 ^ (width - (k + 1)))))

lemma lowerAfter_search {n d width : ℕ} (codes : Fin n → Grid d width) (j : Fin d)
    (k : ℕ) (hk : k ≤ width) :
    binarySearch (fun threshold => decide (n / 2 < countBelow codes j threshold))
      (width - k) (lowerAfter codes k j) = medianCode codes j := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have he := ih (by omega)
      have hr : width - k = (width - (k + 1)) + 1 := by omega
      rw [hr, binarySearch] at he
      by_cases ht : n / 2 < countBelow codes j (lowerAfter codes k j + 2 ^ (width - (k + 1))) <;>
        simpa [lowerAfter, nextLower, ht] using he

lemma lowerAfter_final {n d width : ℕ} (codes : Fin n → Grid d width) (j : Fin d) :
    lowerAfter codes width j = medianCode codes j := by
  simpa only [Nat.sub_self, binarySearch] using lowerAfter_search codes j width le_rfl

lemma lowerAfter_final_grid {n d width : ℕ} (hn : 0 < n) (codes : Fin n → Grid d width) (j : Fin d) :
    lowerAfter codes width j =
      (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val := by
  rw [lowerAfter_final, DistributedJacobianStrongGrowthMedianSearch.medianCode_eq hn]

lemma median_decision_step {n d width : ℕ} (codes : Fin n → Grid d width) (k : ℕ) :
    nextLower (width - (k + 1)) (lowerAfter codes k)
      (fun j => decide ((if n / 2 < countBelow codes j
        (lowerAfter codes k j + 2 ^ (width - (k + 1))) then 1 else 0 : ℕ) = 1)) =
      lowerAfter codes (k + 1) := by
  funext j
  by_cases ht : n / 2 < countBelow codes j (lowerAfter codes k j + 2 ^ (width - (k + 1))) <;>
    simp [lowerAfter, nextLower, ht]

lemma median_final_reference (p : Params) (s : State p) (hs : s.phase = .median 1)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hlower : s.lower = lowerAfter codes (warmWidth p (localDepth p) - 1)) :
    (finishBroadcast p s (broadcastValues p s.phase
      (fun j => countBelow codes j (s.lower j + 1)))).current =
      LongTails.Algorithms.DistributedLocalExtragradient.projectBall p p.x0 p.R
        (p.x0 + reconstruct (warmSpacing p (localDepth p))
          (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes)) := by
  apply DistributedJacobianStrongGrowthProtocol.median_broadcast_reference p s hs _ codes
  have hw : warmWidth p (localDepth p) - 1 + 1 = warmWidth p (localDepth p) :=
    Nat.sub_add_cancel (warmWidth_pos p)
  have hm := median_decision_step codes (warmWidth p (localDepth p) - 1)
  rw [hw, Nat.sub_self] at hm
  have hf : lowerAfter codes (warmWidth p (localDepth p)) =
      fun j => (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val := by
    funext j
    exact lowerAfter_final_grid p.n.pos codes j
  rw [← hf]
  simpa [broadcastValues, hs, hlower] using hm

end LongTails.Proofs.DistributedJacobianStrongGrowthPayload
