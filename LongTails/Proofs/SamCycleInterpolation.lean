import LongTails.Proofs.SmoothInterpolation
import LongTails.Algorithms.NormalizedSam

open InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SamCycle

abbrev Space := EuclideanSpace ℝ (Fin 2)

def pair (a b : ℝ) : Space := WithLp.toLp 2 ![a, b]

@[simp] lemma pair_zero : pair 0 0 = 0 := by
  ext i
  fin_cases i <;> rfl

lemma pair_inner (a b c d : ℝ) : ⟪pair a b, pair c d⟫ = a * c + b * d := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, pair, mul_comm]

lemma pair_norm_sq (a b : ℝ) : ‖pair a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, pair_inner]
  ring

lemma pair_sub (a b c d : ℝ) : pair a b - pair c d = pair (a-c) (b-d) := by
  ext i
  fin_cases i <;> rfl

lemma pair_add (a b c d : ℝ) : pair a b + pair c d = pair (a+c) (b+d) := by
  ext i
  fin_cases i <;> rfl

lemma pair_smul (r a b : ℝ) : r • pair a b = pair (r*a) (r*b) := by
  ext i
  fin_cases i <;> rfl

noncomputable def point (μ t : ℝ) : Fin 5 → Space :=
  ![pair 0 0, pair (3*t/200) (2*μ*t/25), pair (3*t/200) (-2*μ*t/25),
    pair (3*t/200+3/5) (2*μ*t/25+4/5), pair (3*t/200+3/5) (-2*μ*t/25-4/5)]

noncomputable def grad (μ t : ℝ) : Fin 5 → Space :=
  ![pair 0 0, pair (3*μ*t/100) (μ*t/25), pair (3*μ*t/100) (-μ*t/25),
    pair 0 (4/25), pair 0 (-4/25)]

noncomputable def value (μ t : ℝ) : Fin 5 → ℝ := ![0, μ*t^2/5000, μ*t^2/5000, 1/20, 1/20]

set_option maxHeartbeats 2000000 in
lemma certificate {μ t : ℝ} (hm : 0 ≤ μ) (hmb : μ ≤ 1/100)
    (ht : 0 ≤ t) (htb : t ≤ 1/10) (i j : Fin 5) :
    ‖grad μ t j - grad μ t i‖ ^ 2 + μ * 1 * ‖point μ t j - point μ t i‖ ^ 2 -
      2 * μ * ⟪grad μ t j - grad μ t i, point μ t j - point μ t i⟫ ≤
        2 * (1 - μ) * (value μ t j - value μ t i - ⟪grad μ t i, point μ t j - point μ t i⟫) := by
  have hm1 : μ ≤ 1 := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hm2 : μ^2 ≤ μ := by nlinarith
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hmt : μ*t ≤ μ := mul_le_of_le_one_right hm ht1
  have hmt2 : μ*t^2 ≤ μ := mul_le_of_le_one_right hm ht2
  have hm2t : μ^2*t ≤ μ := (mul_le_of_le_one_right (sq_nonneg μ) ht1).trans hm2
  have hm2t2 : μ^2*t^2 ≤ μ := (mul_le_of_le_one_right (sq_nonneg μ) ht2).trans hm2
  have hm3 : μ^3 ≤ μ := by nlinarith [mul_nonneg hm (sub_nonneg.mpr hm2)]
  have hm3t2 : μ^3*t^2 ≤ μ := (mul_le_of_le_one_right (pow_nonneg hm 3) ht2).trans hm3
  have hn1 : 0 ≤ μ*t^2*(11+172*μ-256*μ^2) :=
    mul_nonneg (mul_nonneg hm (sq_nonneg t)) (by nlinarith)
  have hn2 : 0 ≤ μ*t^2*(7-80*μ) :=
    mul_nonneg (mul_nonneg hm (sq_nonneg t)) (by linarith)
  have hn3 : 0 ≤ μ^2*t^2*(1-2*μ) :=
    mul_nonneg (mul_nonneg (sq_nonneg μ) (sq_nonneg t)) (by linarith)
  have hn4 : 0 ≤ (μ*t+8)*(2-10*μ-μ^2*t) :=
    mul_nonneg (by positivity) (by nlinarith)
  fin_cases i <;> fin_cases j <;>
    norm_num [point, grad, value, pair_sub, pair_norm_sq, pair_inner] <;>
    nlinarith [mul_nonneg hm (sq_nonneg t), mul_nonneg (sq_nonneg μ) ht,
      mul_nonneg (sq_nonneg μ) (sq_nonneg t), mul_nonneg (pow_nonneg hm 3) (sq_nonneg t)]

lemma exists_model {μ t : ℝ} (hm : 0 < μ) (hmb : μ ≤ 1/100)
    (ht : 0 < t) (htb : t ≤ 1/10) :
    ∃ f : Space → ℝ,
      (∀ a, HasGradientAt f (gradient f a) a) ∧
      (∀ a b, f a + ⟪gradient f a, b-a⟫ + μ/2*‖b-a‖^2 ≤ f b) ∧
      (∀ a b, ‖gradient f a-gradient f b‖ ≤ ‖a-b‖) ∧
      (∀ i, f (point μ t i) = value μ t i ∧ gradient f (point μ t i) = grad μ t i) ∧
      f 0 = 0 ∧ IsMinOn f Set.univ 0 := by
  obtain ⟨f, G, hf, hc, hl, hi⟩ := SmoothInterpolation.strong_interpolation hm.le
    (show μ < 1 by linarith) (point μ t) (grad μ t) (value μ t)
    (certificate hm.le hmb ht.le htb)
  have hg : ∀ a, gradient f a = G a := fun a => (hf a).gradient
  have h0 := hi 0
  norm_num [point, grad, value] at h0
  refine ⟨f, ?_, ?_, ?_, ?_, h0.1, ?_⟩
  · intro a
    rw [hg]
    exact hf a
  · simpa only [hg] using hc
  · simpa only [hg, one_mul] using hl
  · simpa only [hg] using hi
  · intro a _
    change f 0 ≤ f a
    have h := hc 0 a
    rw [h0.1, h0.2, inner_zero_left, sub_zero] at h
    have hn : 0 ≤ μ / 2 * ‖a‖ ^ 2 := by positivity
    linarith [h0.1]

end LongTails.Proofs.SamCycle
