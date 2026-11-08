import LongTails.Proofs.BirchCollectionPoolPublish
import LongTails.Proofs.BirchCollectionAcceptedOrder

namespace LongTails.Proofs.BirchCollectionPoolCertificate

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionAcceptedOrder
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Proofs.BirchCollectionScaledReset (window_structural)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)

lemma pool_certificate {m K B lower upper window : ℕ} (s : Pool m)
    (hs : Data s B lower upper window (1 / (divisor upper window : ℝ)))
    (hK : 0 < K) (hl : 0 < lower) (hu : lower ≤ upper) (hc : s.cuts.length = K + 1) :
    Structural (run s.events) (resetOrdering (ordering s))
      (controls lower upper window (s.trace.nextRaw - B * s.accepted.length)) K B := by
  let o := ordering s
  have hlabel (n : ℕ) (hn : n < s.accepted.length) : o.label n = s.accepted[n] := label_eq_getElem o n hn
  have hcut (k : ℕ) (hk : k ≤ K) : k < s.cuts.length := by rw [hc]; omega
  have hlen : o.labels.length = s.accepted.length := rfl
  have hpos : 0 < o.labels.length := by
    have h := hs.main.positive 0 (hcut 1 hK)
    rw [hs.main.cutStart] at h
    exact h.trans_le (hs.main.cutBound 1 (hcut 1 hK))
  have hend : o.cut K = o.labels.length := by
    change cutIndex s.cuts K = s.accepted.length
    have h := hs.main.cutLast
    rw [List.getLast?_eq_getElem?, hc, Nat.add_sub_cancel] at h
    exact h
  have hlog : LogData s.trace o K window := by
    refine ⟨hpos, hs.main.unique, hs.main.markerCount.trans hc, hs.main.cutStart, hend,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      exact hs.main.positive k (hcut (k + 1) hk)
    · intro k hk
      exact hs.main.cutBound k (hcut k hk)
    · intro n hn
      rw [hlabel n hn]
      exact hs.main.labels _ (List.getElem_mem hn)
    · intro k hk
      exact hs.main.markers k (hcut k hk)
    · intro n hn
      rw [hlabel n hn]
      exact (hs.main.directions n hn).prior
    · intro n hn
      have h := hs.main.directions n hn
      exact ⟨h.frontierBound, h.delayBound, by rw [hlabel n hn]; exact h.includes⟩
  let D := s.trace.nextRaw - B * s.accepted.length
  apply window_structural (m + 1) K B lower upper window D s.events o hs.legal
    (hs.represented.symm ▸ hlog.valid) hl hu
  · rw [hs.represented]
    exact hlog.frontier
  · intro k hk
    exact hs.main.mass k (hcut (k + 1) hk)
  · rw [hs.represented]
    intro n hn
    have hn' : n < s.accepted.length := hn
    simp only [Ordering.refresh, hlen, ite_eq_left hn', hlabel n hn']
    exact (hs.main.directions n hn').refresh
  · rw [hs.represented]
    intro n hn
    have hn' : n < s.accepted.length := hn
    simp only [Ordering.movement, hlen, ite_eq_left hn', hlabel n hn']
    exact (hs.main.directions n hn').movement
  · rw [hs.represented]
    intro n hn
    rw [hlabel n hn]
    exact (hs.main.directions n hn).raw
  · rw [hs.represented, hlen]
    dsimp only [D]
    omega

end LongTails.Proofs.BirchCollectionPoolCertificate
