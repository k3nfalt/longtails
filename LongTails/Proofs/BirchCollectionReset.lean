import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Setups.BirchCollections

namespace LongTails.Proofs.BirchCollectionReset

open Finset
open LongTails.Algorithms.BirchCollectionProfiles
open LongTails.Setups.BirchCollections

lemma reset_structural (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering)
    (c : Controls) (K B : ℕ)
    (ho : o.Valid s K) (hc : c.Valid)
    (hrefresh : ∀ n, n < o.labels.length → o.refresh s n = 1)
    (hfront : ∀ n, n < o.labels.length → o.frontier n ≤ n ∧
      range (o.frontier n) ⊆ o.history s n ∧
      (∑ j ∈ Ico (o.frontier n) n, o.movement s j) ≤ 1 / 4)
    (hlo : ∀ k, k < K → c.lowerMass ≤ ∑ j ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s j)
    (hhi : ∀ k, k < K →
      (∑ j ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s j) ≤ c.upperMass)
    (hbatch : ∀ n, n < o.labels.length → B ≤ (o.raw s n).card)
    (hcost : ∀ n, n < o.labels.length → (o.raw s n).card ≤
      (B : ℝ) * c.amplification * o.movement s n)
    (hwaste : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤ c.waste) :
    Structural s (resetOrdering o) c K B := by
  refine ⟨ho, hc, hrefresh 0 ho.1, hfront, hlo, hhi, ?_, ?_, hwaste, ?_⟩
  · intro n hn
    change o.refresh s n * B ≤ (o.raw s n).card
    rw [hrefresh n hn, one_mul]
    exact_mod_cast hbatch n hn
  · intro n hn
    exact Or.inr (hcost n hn)
  · intro n hn
    dsimp only [resetOrdering, id_eq]
    refine ⟨le_rfl, hrefresh n hn, fun h => (lt_irrefl n h).elim, ?_, ?_⟩
    · intro j hj hj'
      omega
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp
      exact (hrefresh n hn).le

end LongTails.Proofs.BirchCollectionReset
