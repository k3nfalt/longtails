import LongTails.Proofs.DistributedJacobianStrongGrowthPayloadAggregation
import LongTails.Proofs.DistributedJacobianStrongGrowthWarmReference

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianReference

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPayload

lemma median_lower_step (p : Params) (s : State p) (remaining : ℕ)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hlower : s.lower = lowerAfter codes (warmWidth p (localDepth p) - remaining)) :
    nextLower (remaining - 1) s.lower
      (fun j => decide ((if (p.n : ℕ) / 2 < countBelow codes j
        (s.lower j + 2 ^ (remaining - 1)) then 1 else 0 : ℕ) = 1)) =
      lowerAfter codes (warmWidth p (localDepth p) - (remaining - 1)) := by
  have hi : warmWidth p (localDepth p) - remaining + 1 =
      warmWidth p (localDepth p) - (remaining - 1) := by omega
  have hr : warmWidth p (localDepth p) -
      (warmWidth p (localDepth p) - remaining + 1) = remaining - 1 := by omega
  have h := median_decision_step codes (warmWidth p (localDepth p) - remaining)
  rw [hr, hi] at h
  simpa only [hlower] using h

lemma median_broadcast_lower (p : Params) (s : State p) (remaining : ℕ)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hs : s.phase = .median remaining)
    (hpos : 1 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hlower : s.lower = lowerAfter codes (warmWidth p (localDepth p) - remaining)) :
    (finishBroadcast p s (broadcastValues p s.phase
      (fun j => countBelow codes j (s.lower j + 2 ^ (remaining - 1))))).lower =
      lowerAfter codes (warmWidth p (localDepth p) - (remaining - 1)) := by
  simpa only [finishBroadcast, hs, ite_eq_left hpos, startMedian, broadcastValues] using
    median_lower_step p s remaining codes (by omega) hle hlower

lemma median_broadcast_own (p : Params) (s : State p) (remaining : ℕ) (i : Fin p.n)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (hs : s.phase = .median remaining)
    (hpos : 1 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hlower : s.lower = lowerAfter codes (warmWidth p (localDepth p) - remaining))
    (hcodes : s.warmCodes = fun j => (codes i j).val) :
    (finishBroadcast p s (broadcastValues p s.phase
      (fun j => countBelow codes j (s.lower j + 2 ^ (remaining - 1))))).own =
      fun j => if (codes i j).val <
        lowerAfter codes (warmWidth p (localDepth p) - (remaining - 1)) j +
          2 ^ (remaining - 1 - 1) then 1 else 0 := by
  have h := median_lower_step p s remaining codes (by omega) hle hlower
  simp only [finishBroadcast, hs, ite_eq_left hpos, startMedian, broadcastValues]
  rw [h, hcodes]

lemma finishLocal_warming_own (p : Params) (s : State p) (x : Point p)
    (hs : s.phase = .warming) :
    (finishLocal p s x).own = fun j =>
      if (finishLocal p s x).warmCodes j < 2 ^ (warmWidth p (localDepth p) - 1)
      then 1 else 0 := by
  simp [finishLocal, hs, startMedian]

lemma warm_own_reference (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : DistributedJacobianStrongGrowthWarmReference.WarmReference p g samples i s used)
    (hs : s.phase = .warming) (hw : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none) :
    (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)).own =
      fun j => if
        (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.warmCodes p
          (warmCount p (localDepth p)) (warmWidth p (localDepth p))
          (warmSpacing p (localDepth p)) g samples i j).val <
            2 ^ (warmWidth p (localDepth p) - 1) then 1 else 0 := by
  rw [finishLocal_warming_own p s _ hs]
  have hf := DistributedJacobianStrongGrowthWarmReference.warmReference_finishLocal
    p g samples i s used work h hw hq
  rw [hf.2 (DistributedJacobianStrongGrowthWarmReference.finishLocal_not_warming p s _)]

open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthPayloadAggregation

noncomputable def medianValues (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) :
    Fin p.n → Fin p.d → ℕ :=
  fun i j => if (codes i j).val < lowerAfter codes epoch j +
    2 ^ (warmWidth p (localDepth p) - (epoch + 1)) then 1 else 0

lemma medianValues_le_one (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) :
    ∀ i j, medianValues p codes epoch i j ≤ 1 := by
  intro i j
  unfold medianValues
  split_ifs <;> omega

lemma medianValues_root (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) :
    subtreeValues p p.root (medianValues p codes epoch) =
      fun j => countBelow codes j (lowerAfter codes epoch j +
        2 ^ (warmWidth p (localDepth p) - (epoch + 1))) := by
  funext j
  simp [subtreeValues, DistributedJacobianStrongGrowthTree.subtree_root p hp,
    medianValues, countBelow]

lemma median_collector_root (p : Params) (hp : valid p) (s : State p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ)
    (hc : CollectorCorrect p p.root (medianValues p codes epoch) s.collector)
    (hfull : children p p.root ⊆ s.collector.seen)
    (hown : s.own = medianValues p codes epoch p.root) :
    (fun j => s.own j + s.collector.total j) =
      fun j => countBelow codes j (lowerAfter codes epoch j +
        2 ^ (warmWidth p (localDepth p) - (epoch + 1))) := by
  rw [← medianValues_root p hp codes epoch]
  funext j
  rw [hown]
  exact collectorCorrect_complete p hp p.root _ s.collector hc hfull j

lemma median_subtree_fits (p : Params) (v : Fin p.n)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (epoch : ℕ) :
    ∀ j, subtreeValues p v (medianValues p codes epoch) j < 2 ^ countWidth p.n :=
  subtreeValues_count_fits p v _ (medianValues_le_one p codes epoch)

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianReference
