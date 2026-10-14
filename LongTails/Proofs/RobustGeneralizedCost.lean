import LongTails.Algorithms.RobustGeneralizedAccelerated
import LongTails.Proofs.StochasticGeneralizedWeights
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped BigOperators

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

lemma estimatorCost_le (p : Params) (hR : 0 < p.R) (hε : 0 < p.ε)
    {a : ℝ} (ha : 0 < a) (hℓ : 0 < confidence p) :
    (estimatorCost p a : ℝ) ≤ (pilotGroups p : ℝ)+1+
      1073741824*p.σ^2*(confidence p)^2/p.ε*a+
      (pilotGroups p : ℝ)*2359296*p.σ^2*(confidence p)^2/p.R^2*a^2 := by
  have hm := StochasticGeneralized.rounded_batch_le
    (show 0 ≤ 1073741824*p.σ^2*a*(confidence p)^2/p.ε by positivity)
  have hr := StochasticGeneralized.rounded_batch_le
    (show 0 ≤ 576*p.σ^2/(radius p a)^2 by positivity)
  have he : 576*p.σ^2/(radius p a)^2 = 2359296*p.σ^2*(confidence p)^2/p.R^2*a^2 := by
    unfold radius
    field_simp; ring
  change (pilotSize p a : ℝ) ≤ 1+576*p.σ^2/(radius p a)^2 at hr
  rw [he] at hr
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ (pilotGroups p : ℝ) by positivity)
  change (correctionSize p a : ℝ) ≤ _ at hm
  change (pilotGroups p : ℝ)*(pilotSize p a : ℝ) ≤ _ at hh
  unfold estimatorCost
  push_cast
  exact (add_le_add hh hm).trans_eq (by ring)

lemma weighted_calls_le (m : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) {C D K S : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : ∀ i < n, 0 ≤ a i)
    (hm : ∀ i < n, (m i : ℝ) ≤ K+C*a i+D*(a i)^2)
    (hs : (∑ i ∈ Finset.range n, a i) ≤ S) :
    ((∑ i ∈ Finset.range n, m i : ℕ) : ℝ) ≤ K*n+C*S+D*S^2 := by
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun i hi => hm i (Finset.mem_range.mp hi))
  have hn : 0 ≤ ∑ i ∈ Finset.range n, a i :=
    Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  have hsq : (∑ i ∈ Finset.range n, (a i)^2) ≤ S^2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))).trans
      (pow_le_pow_left₀ hn hs 2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have h1 := mul_le_mul_of_nonneg_left hs hC
  have h2 := mul_le_mul_of_nonneg_left hsq hD
  push_cast
  simpa only [Nat.cast_sum] using (show (∑ i ∈ Finset.range n, (m i : ℝ)) ≤
    K*n+C*S+D*S^2 by nlinarith only [hsum, h1, h2])

lemma public_cost_bound {k n H W V : ℝ} (hn0 : 0 ≤ n)
    (hH : 1 ≤ H) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hk : k ≤ 65*H) (hn : n ≤ 16385*W) :
    2*(k+1)*n+(1099511627776+1236950581248*k)*V ≤
      (4194304*W+140737488355328*V)*H := by
  have hkp : k+1 ≤ 66*H := by linarith
  have hfirst : 2*(k+1)*n ≤ 2162820*H*W := by
    calc
      _ ≤ 2*(66*H)*(16385*W) := by gcongr
      _ = _ := by ring
  have hc : 1099511627776+1236950581248*k ≤ 140737488355328*H := by
    nlinarith only [hk, hH]
  have hsecond := mul_le_mul_of_nonneg_right hc hV
  have hHW : 0 ≤ H*W := mul_nonneg (by linarith) hW
  nlinarith only [hfirst, hsecond, hHW]

end OracleTemplate.RobustGeneralized
