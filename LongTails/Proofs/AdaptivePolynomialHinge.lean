import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace LongTails.Proofs.AdaptivePolynomialHinge

lemma hasDerivAt_join (f g df dg : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hc : f c = g c) (hd : df c = dg c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then df x else dg x) x := by
  rcases lt_trichotomy x c with hx | rfl | hx
  · simp only [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    simp only [ite_eq_left hy.le]
  · simp only [le_refl, ↓reduceIte]
    have hl : HasDerivWithinAt (fun y => if y ≤ x then f y else g y)
        (df x) (Iic x) x := by
      apply (hf x).hasDerivWithinAt.congr
      · intro y hy
        simp only [ite_eq_left (show y ≤ x from hy)]
      · simp
    have hr : HasDerivWithinAt (fun y => if y ≤ x then f y else g y)
        (df x) (Ioi x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr
      · intro y hy
        simp only [ite_eq_right (not_le.mpr (show x < y from hy))]
      · simpa using hc
    have hh := hl.union hr
    simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hh
  · simp only [ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    simp only [ite_eq_right (not_le.mpr hy)]



def weight (n : ℕ) (t : ℝ) : ℝ := t ^ n * ((n + 1 : ℕ) - (n : ℝ) * t)

lemma weight_nonnegative (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ weight n t := by
  unfold weight
  apply mul_nonneg (pow_nonneg ht _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

lemma power_le_weight (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ n ≤ weight n t := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : 1 ≤ ((n + 1 : ℕ) : ℝ) - (n : ℝ) * t := by
    push_cast
    nlinarith
  simpa [weight] using mul_le_mul_of_nonneg_left h (pow_nonneg ht n)

lemma weight_succ_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    weight (n + 1) t ≤ weight n t := by
  have h := mul_nonneg (mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)
    (pow_nonneg ht n)) (sq_nonneg (1 - t))
  unfold weight
  push_cast
  rw [pow_succ]
  nlinarith

lemma weight_le_one (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : weight n t ≤ 1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih => exact (weight_succ_le n t ht).trans ih

lemma weight_zero (n : ℕ) (hn : 0 < n) : weight n 0 = 0 := by
  simp [weight, ne_of_gt hn]

lemma weight_one (n : ℕ) : weight n 1 = 1 := by simp [weight]

def slope (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * (n + 1 : ℕ) * t ^ (n - 1) * (1 - t)

lemma slope_nonnegative (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ slope n t := by
  unfold slope
  positivity

lemma slope_weight_bound (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    slope n t ≤ 2 * (n : ℝ) * (n + 1 : ℕ) * (weight n t + (1 / 2 : ℝ) ^ n) := by
  have hpow : t ^ (n - 1) * t = t ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hp := power_le_weight n t ht ht1
  have hw := weight_nonnegative n t ht ht1
  have hhalf : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hn0 : 0 ≤ (n : ℝ) * (n + 1 : ℕ) := by positivity
  have hs : t ^ (n - 1) * (1 - t) ≤
      2 * (weight n t + (1 / 2 : ℝ) ^ n) := by
    by_cases h : 1 / 2 ≤ t
    · have hm := mul_le_mul_of_nonneg_left h (pow_nonneg ht (n - 1))
      have hsmall := mul_nonneg (pow_nonneg ht (n - 1)) ht
      nlinarith
    · have hm := pow_le_pow_left₀ ht (le_of_lt (lt_of_not_ge h)) (n - 1)
      have he : (1 / 2 : ℝ) ^ (n - 1) = 2 * (1 / 2 : ℝ) ^ n := by
        have hh : (1 / 2 : ℝ) ^ (n - 1) * (1 / 2) = (1 / 2 : ℝ) ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        linarith
      rw [he] at hm
      have hsmall := mul_nonneg (pow_nonneg ht (n - 1)) ht
      nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hn0
  unfold slope
  nlinarith only [hh]

lemma weight_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (weight n) (slope n t) t := by
  have h := ((hasDerivAt_id t).pow n).mul
    ((hasDerivAt_const t ((n + 1 : ℕ) : ℝ)).sub ((hasDerivAt_id t).const_mul (n : ℝ)))
  convert h using 1
  · funext x
    simp [weight]
  · simp only [id_eq, Pi.pow_apply, Pi.sub_apply]
    by_cases hn : n = 0
    · simp [slope, hn]
    · have he : t ^ (n - 1) * t = t ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      unfold slope
      push_cast
      rw [← he]
      ring

noncomputable def primitive (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n + 1) - (n : ℝ) / (n + 2 : ℕ) * t ^ (n + 2)

lemma primitive_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (primitive n) (weight n t) t := by
  have h := ((hasDerivAt_id t).pow (n + 1)).sub
    (((hasDerivAt_id t).pow (n + 2)).const_mul ((n : ℝ) / (n + 2 : ℕ)))
  convert h using 1
  · rfl
  · simp only [Nat.add_sub_cancel, id_eq]
    unfold weight
    push_cast
    rw [pow_succ]
    field_simp

lemma primitive_one (n : ℕ) : primitive n 1 = 1 - (n : ℝ) / (n + 2 : ℕ) := by
  simp [primitive]

lemma slope_zero (n : ℕ) (hn : 2 ≤ n) : slope n 0 = 0 := by
  have h : n - 1 ≠ 0 := by omega
  simp [slope, h]

lemma slope_one (n : ℕ) : slope n 1 = 0 := by simp [slope]

noncomputable def ramp (n : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then primitive n t else t - (n : ℝ) / (n + 2 : ℕ)

noncomputable def mixing (n : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then weight n t else 1

noncomputable def curvature (n : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then slope n t else 0

lemma ramp_hasDerivAt (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    HasDerivAt (ramp n) (mixing n t) t := by
  have hi := hasDerivAt_join (primitive n)
    (fun y => y - (n : ℝ) / (n + 2 : ℕ)) (weight n) (fun _ => 1) 1
    (primitive_hasDerivAt n) (fun y => (hasDerivAt_id y).sub_const _)
    (primitive_one n) (weight_one n)
  exact hasDerivAt_join (fun _ => 0) _ (fun _ => 0) _ 0
    (fun y => hasDerivAt_const y 0) hi (by simp [primitive])
    (by simp [weight_zero n (by omega)]) t

lemma mixing_hasDerivAt (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    HasDerivAt (mixing n) (curvature n t) t := by
  have hi := hasDerivAt_join (weight n) (fun _ => 1)
    (slope n) (fun _ => 0) 1 (weight_hasDerivAt n)
    (fun y => hasDerivAt_const y 1) (weight_one n) (slope_one n)
  exact hasDerivAt_join (fun _ => 0) _ (fun _ => 0) _ 0
    (fun y => hasDerivAt_const y 0) hi
    (by simp [weight_zero n (by omega)]) (by simp [slope_zero n hn]) t

lemma mixing_bounds (n : ℕ) (t : ℝ) : 0 ≤ mixing n t ∧ mixing n t ≤ 1 := by
  by_cases h : t ≤ 0
  · simp [mixing, h]
  · by_cases h' : t ≤ 1
    · simpa [mixing, h, h'] using
        And.intro (weight_nonnegative n t (le_of_not_ge h) h')
          (weight_le_one n t (le_of_not_ge h))
    · simp [mixing, h, h']

lemma curvature_bounds (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    0 ≤ curvature n t ∧ curvature n t ≤
      2 * (n : ℝ) * (n + 1 : ℕ) * (mixing n t + (1 / 2 : ℝ) ^ n) := by
  by_cases h : t ≤ 0
  · simp only [curvature, mixing, h, ↓reduceIte]
    constructor <;> positivity
  · by_cases h' : t ≤ 1
    · simpa only [curvature, mixing, h, h', ↓reduceIte] using
        And.intro (slope_nonnegative n t (le_of_not_ge h) h')
          (slope_weight_bound n (by omega) t (le_of_not_ge h) h')
    · simp only [curvature, mixing, h, h', ↓reduceIte]
      constructor <;> positivity

lemma deriv_ramp (n : ℕ) (hn : 2 ≤ n) : deriv (ramp n) = mixing n :=
  funext fun t => (ramp_hasDerivAt n hn t).deriv

lemma deriv_mixing (n : ℕ) (hn : 2 ≤ n) : deriv (mixing n) = curvature n :=
  funext fun t => (mixing_hasDerivAt n hn t).deriv

lemma ramp_convex (n : ℕ) (hn : 2 ≤ n) : ConvexOn ℝ Set.univ (ramp n) := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (ramp_hasDerivAt n hn t).differentiableAt
  · rw [deriv_ramp n hn]
    exact fun t => (mixing_hasDerivAt n hn t).differentiableAt
  · intro t
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      deriv_ramp n hn, deriv_mixing n hn] using (curvature_bounds n hn t).1

lemma ramp_nonnegative (n : ℕ) (hn : 2 ≤ n) (t : ℝ) : 0 ≤ ramp n t := by
  have hm : Monotone (ramp n) := monotone_of_hasDerivAt_nonneg
    (fun x => ramp_hasDerivAt n hn x) (fun x => (mixing_bounds n x).1)
  by_cases ht : t ≤ 0
  · simp [ramp, ht]
  · have h := hm (le_of_not_ge ht)
    simpa [ramp] using h

end LongTails.Proofs.AdaptivePolynomialHinge
