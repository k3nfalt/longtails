import LongTails.Algorithms.AdaptiveRobustGeneralizedAccelerated
import LongTails.Proofs.StochasticGeneralizedWeights
import LongTails.Proofs.AdaptiveRobustGeneralizedTuning
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

namespace OracleTemplate.AdaptiveRobustGeneralized

lemma one_le_log_four : 1 ≤ Real.log 4 := by
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  have h := Real.log_two_gt_d9
  push_cast
  linarith

lemma log_four_div_ge {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : 1 ≤ Real.log (4/y) :=
  one_le_log_four.trans (Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hy]; linarith))

lemma inverse_log_charge {y τ : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    1/Real.log (4/y) ≤ (1/Real.log (4/τ))*(1+y/τ) := by
  have hly := log_four_div_ge hy hy1
  have hlt := log_four_div_ge hτ hτ1
  rcases le_or_gt y τ with h | h
  · have hl : Real.log (4/τ) ≤ Real.log (4/y) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hy h)
    calc
      _ ≤ 1/Real.log (4/τ) := one_div_le_one_div_of_le (by linarith) hl
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith [show 0 ≤ y/τ by positivity])
  · have hsplit : Real.log (4/τ) = Real.log (4/y)+Real.log (y/τ) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hlog : Real.log (y/τ) ≤ y/τ-1 := Real.log_le_sub_one_of_pos (by positivity)
    have hτlog : τ*Real.log (y/τ) ≤ y-τ := by
      have := mul_le_mul_of_nonneg_left hlog hτ.le
      rw [mul_sub, mul_div_cancel₀ _ hτ.ne', mul_one] at this
      exact this
    have hmono : τ*Real.log (4/τ) ≤ y*Real.log (4/y) := by
      rw [hsplit]
      nlinarith
    have hpos : 0 < Real.log (4/y) := by linarith
    have hpos' : 0 < Real.log (4/τ) := by linarith
    calc
      1/Real.log (4/y) ≤ (y/τ)*(1/Real.log (4/τ)) := by
        rw [div_le_iff₀ hpos]
        field_simp
        linarith [hmono]
      _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma ratio_le (p : Params) (a : ℝ) :
    ratio p a ≤ 576*p.σ^2/(radius p a)^2+Real.exp (-28*level p) := by
  unfold ratio
  have h1 : 0 ≤ 576*p.σ^2/(radius p a)^2 := by positivity
  have h2 := Real.exp_pos (-28*level p)
  exact (min_le_right _ _).trans (max_le (by linarith) (by linarith))

lemma noise_ratio_eq (p : Params) (hR : 0 < p.R) {a : ℝ} (ha : 0 < a) (hℓ : 0 < confidence p) :
    576*p.σ^2/(radius p a)^2 = 2359296*p.σ^2*(confidence p)^2/p.R^2*a^2 := by
  unfold radius
  field_simp
  ring

lemma estimatorCost_le (p : Params) (hR : 0 < p.R) (hε : 0 < p.ε)
    {a : ℝ} (ha : 0 < a) (hℓ : 0 < confidence p) (hL : 1 ≤ level p)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (estimatorCost p a : ℝ) ≤
      2+28*level p*(1/Real.log (4/τ))*(1+Real.exp (-28*level p)/τ)+
      1073741824*p.σ^2*confidence p/p.ε*a+
      (28*level p*(1/Real.log (4/τ))/τ+22*level p)*
        (2359296*p.σ^2*(confidence p)^2/p.R^2)*a^2 := by
  let x := 576*p.σ^2/(radius p a)^2
  let y := ratio p a
  let L := level p
  let φτ := 1/Real.log (4/τ)
  have hx : 0 ≤ x := by positivity
  have hy := ratio_pos p a
  have hy1 := ratio_le_one p a
  have hly := log_four_div_ge hy hy1
  have hlt := log_four_div_ge hτ hτ1
  have hφτ : 0 ≤ φτ := by dsimp [φτ]; positivity
  have hz : 0 ≤ 28*L/Real.log (4/y) := by positivity
  have hk : (pilotGroups p a : ℝ) ≤ 1+28*L/Real.log (4/y) := by
    unfold pilotGroups
    push_cast
    exact max_le (by linarith) ((Nat.ceil_lt_add_one hz).le.trans (by linarith))
  have hr : (pilotSize p a : ℝ) ≤ 1+x := by
    unfold pilotSize
    push_cast
    exact max_le (by linarith) ((Nat.ceil_lt_add_one hx).le.trans (by linarith))
  have hm : (correctionSize p a : ℝ) ≤ 1+1073741824*p.σ^2*confidence p/p.ε*a := by
    unfold correctionSize
    push_cast
    have h0 : 0 ≤ 1073741824*p.σ^2*a*confidence p/p.ε := by positivity
    refine max_le (by nlinarith [show 0 ≤ 1073741824*p.σ^2*confidence p/p.ε*a by positivity])
      ((Nat.ceil_lt_add_one h0).le.trans ?_)
    rw [show 1073741824*p.σ^2*a*confidence p/p.ε = 1073741824*p.σ^2*confidence p/p.ε*a by ring]
    linarith
  have hk21 : (pilotGroups p a : ℝ) ≤ 22*L := by
    have hd : 28*L/Real.log (4/y) ≤ 28*L := div_le_self (by positivity) hly
    have h4 : 28*L/Real.log (4/y) ≤ 28*L/Real.log 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith [one_le_log_four])
      exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hy]; linarith)
    have hl4 : 4/3 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      have h := Real.log_two_gt_d9
      push_cast
      linarith
    have h5 : 28*L/Real.log 4 ≤ 21*L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hcharge := inverse_log_charge hy hy1 hτ hτ1
  have hyle : y ≤ x+Real.exp (-28*L) := ratio_le p a
  have hkφ : 28*L/Real.log (4/y) ≤ 28*L*φτ*(1+(x+Real.exp (-28*L))/τ) := by
    have h1 : 1/Real.log (4/y) ≤ φτ*(1+(x+Real.exp (-28*L))/τ) := by
      apply hcharge.trans
      apply mul_le_mul_of_nonneg_left _ hφτ
      have := div_le_div_of_nonneg_right hyle hτ.le
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 28*L by positivity)
    calc 28*L/Real.log (4/y) = 28*L*(1/Real.log (4/y)) := by ring
      _ ≤ 28*L*(φτ*(1+(x+Real.exp (-28*L))/τ)) := h2
      _ = _ := by ring
  have hkr : (pilotGroups p a : ℝ)*(pilotSize p a : ℝ) ≤
      1+28*L*φτ*(1+(x+Real.exp (-28*L))/τ)+22*L*x := by
    have hk0 : (0 : ℝ) ≤ (pilotGroups p a : ℝ) := by positivity
    calc
      _ ≤ (pilotGroups p a : ℝ)*(1+x) := mul_le_mul_of_nonneg_left hr hk0
      _ = (pilotGroups p a : ℝ)+(pilotGroups p a : ℝ)*x := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hk21 hx]
  have hxe := noise_ratio_eq p hR ha hℓ
  unfold estimatorCost
  push_cast
  change (pilotGroups p a : ℝ)*(pilotSize p a : ℝ)+(correctionSize p a : ℝ) ≤ _
  have hsplit : 28*L*φτ*(1+(x+Real.exp (-28*L))/τ) =
      28*L*φτ*(1+Real.exp (-28*L)/τ)+28*L*φτ/τ*x := by
    field_simp
    ring
  rw [hsplit] at hkr
  have hfin : 28*L*φτ/τ*x+22*L*x =
      (28*L*φτ/τ+22*L)*(2359296*p.σ^2*(confidence p)^2/p.R^2)*a^2 := by
    change 28*L*φτ/τ*(576*p.σ^2/(radius p a)^2)+22*L*(576*p.σ^2/(radius p a)^2) = _
    rw [hxe]
    ring
  dsimp only [L, φτ] at hkr hfin ⊢
  linarith

lemma weighted_calls_le (m : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) {C D K S amax : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : ∀ i < n, 0 ≤ a i) (hmax : ∀ i < n, a i ≤ amax)
    (hm : ∀ i < n, (m i : ℝ) ≤ K+C*a i+D*(a i)^2)
    (hs : (∑ i ∈ Finset.range n, a i) ≤ S) (hamax : 0 ≤ amax) :
    ((∑ i ∈ Finset.range n, m i : ℕ) : ℝ) ≤ K*n+C*S+D*(amax*S) := by
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun i hi => hm i (Finset.mem_range.mp hi))
  have hsq : (∑ i ∈ Finset.range n, (a i)^2) ≤ amax*S := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, amax*a i := Finset.sum_le_sum (fun i hi => by
        have h0 := ha i (Finset.mem_range.mp hi)
        have h1 := hmax i (Finset.mem_range.mp hi)
        nlinarith)
      _ = amax*∑ i ∈ Finset.range n, a i := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hamax
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have h1 := mul_le_mul_of_nonneg_left hs hC
  have h2 := mul_le_mul_of_nonneg_left hsq hD
  push_cast
  simpa only [Nat.cast_sum] using (show (∑ i ∈ Finset.range n, (m i : ℝ)) ≤
    K*n+C*S+D*(amax*S) by nlinarith only [hsum, h1, h2])

end OracleTemplate.AdaptiveRobustGeneralized
