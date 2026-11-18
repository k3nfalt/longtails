import LongTails.Proofs.FrontierChainOracle
import LongTails.Proofs.FrontierChainTruncation

namespace LongTails.Proofs.FrontierChainSimulation

open FrontierChain FrontierChainNoise FrontierChainPrefix FrontierChainTruncation
open FrontierChainWall FrontierChainOracle SoftRadialProjection HolderNoiseHardOracle

variable {d k : ℕ}

noncomputable def partialOracle (π : Fin (k + 1) ↪ Fin d) (p : ℝ) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (b : Bool) : EuclideanSpace ℝ (Fin d) :=
  let z := project (radius k) x
  let v := if b then
    field π (lookahead π r z) + (1 / p - 1) • noiseField π (lookahead π r z)
    else field π (truncate π r z) - noiseField π (truncate π r z)
  derivative (radius k) x v + (1 / 5 : ℝ) • x

lemma partialOracle_eq (π : Fin (k + 1) ↪ Fin d) (p : ℝ) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (b : Bool)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |project (radius k) x (π j)| ≤ 1 / 4) :
    partialOracle π p r x b = canonicalOracle π p x b := by
  cases b
  · rw [canonicalOracle_false]
    simp only [partialOracle, Bool.false_eq_true, ite_false]
    rw [← residual_truncate π r _ hx]
  · simp only [partialOracle, ite_true]
    rw [← field_lookahead π r _ hx, ← noise_lookahead π r _ hx]
    simp only [canonicalOracle, oracleValue, coinError, ite_true, wallField, projectedNoise,
      map_add, map_smul]
    abel

lemma partialOracle_false_prefix (π π' : Fin (k + 1) ↪ Fin d) (p : ℝ) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hπ : ∀ j : Fin (k + 1), j.val < r → π j = π' j) :
    partialOracle π p r x false = partialOracle π' p r x false := by
  let z := project (radius k) x
  have he := truncate_prefix π π' r z hπ
  have hs (ρ : Fin (k + 1) ↪ Fin d) (j : Fin (k + 1)) (hj : r ≤ j.val) :
      |truncate ρ r z (ρ j)| ≤ 1 / 4 := by
    rw [truncate_coordinate, ite_eq_right (by omega)]
    norm_num
  have hr := residual_prefix π π' (truncate π r z) r hπ (hs π)
    (by rw [he]; exact hs π')
  simp only [partialOracle, Bool.false_eq_true, ite_false]
  change derivative (radius k) x (field π (truncate π r z) - noiseField π (truncate π r z)) + _ = _
  rw [hr, he]

lemma partialOracle_true_prefix (π π' : Fin (k + 1) ↪ Fin d) (p : ℝ) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j) :
    partialOracle π p r x true = partialOracle π' p r x true := by
  let z := project (radius k) x
  have he := lookahead_prefix π π' r z hπ
  have hs := lookahead_small π r z
  have hs' : ∀ j : Fin (k + 1), r ≤ j.val → |lookahead π r z (π' j)| ≤ 1 / 4 := by
    rw [he]
    exact lookahead_small π' r z
  have hf := field_prefix π π' (lookahead π r z) r hπ hs hs'
  have hn := noise_prefix π π' (lookahead π r z) r hπ hs hs'
  simp only [partialOracle, ite_true]
  change derivative (radius k) x (field π (lookahead π r z) + _ • noiseField π (lookahead π r z)) + _ = _
  rw [hf, hn, he]

end LongTails.Proofs.FrontierChainSimulation
