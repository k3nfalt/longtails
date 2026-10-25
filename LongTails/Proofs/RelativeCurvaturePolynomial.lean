import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

namespace LongTails.Proofs.RelativeCurvaturePolynomial

open Polynomial

lemma chebyshev_unit_bound (n : ℕ) {x : ℝ} (hx : -1 ≤ x) (hx₁ : x ≤ 1) :
    |(Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx hx₁, Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

lemma arcosh_gap {a x : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hx : 1 + a ≤ x) :
    Real.sqrt a / 2 ≤ Real.arcosh x := by
  have hx₁ : 1 ≤ x := by linarith
  have hs : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha₁
  have hs0 := Real.sqrt_nonneg a
  have hsq : a ≤ x ^ 2 - 1 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hsq
  have harg : 1 + Real.sqrt a ≤ x + Real.sqrt (x ^ 2 - 1) := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + Real.sqrt a) harg
  have hl := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + Real.sqrt a)
  have hb : Real.sqrt a / 2 ≤ 1 - (1 + Real.sqrt a)⁻¹ := by
    apply (le_sub_iff_add_le).mpr
    apply (mul_le_mul_iff_left₀ (show 0 < 1 + Real.sqrt a by positivity)).mp
    rw [add_mul, inv_mul_cancel₀ (by positivity : 1 + Real.sqrt a ≠ 0)]
    nlinarith
  exact hb.trans (hl.trans hlog)

lemma chebyshev_growth (n : ℕ) {a x : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hx : 1 + a ≤ x) :
    Real.exp ((n : ℝ) * Real.sqrt a / 2) / 2 ≤ (Chebyshev.T ℝ (n : ℤ)).eval x := by
  have hx₁ : 1 ≤ x := by linarith
  have harg := mul_le_mul_of_nonneg_left (arcosh_gap ha ha₁ hx) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he := Real.exp_le_exp.mpr harg
  rw [← Real.cosh_arcosh hx₁, Chebyshev.T_real_cosh]
  simp only [Int.cast_natCast]
  rw [Real.cosh_eq]
  have hp := Real.exp_pos (-((n : ℝ) * Real.arcosh x))
  rw [show (n : ℝ) * Real.sqrt a / 2 = (n : ℝ) * (Real.sqrt a / 2) by ring]
  linarith

lemma transformed_interval {a eig : ℝ} (ha : 0 ≤ a) (he : -a ≤ eig) (he₁ : eig ≤ 1) :
    -1 ≤ ((1 - a) - 2 * eig) / (1 + a) ∧ ((1 - a) - 2 * eig) / (1 + a) ≤ 1 := by
  have hp : 0 < 1 + a := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

lemma transformed_gap {a eig : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (he : eig ≤ -2 * a) :
    1 + a ≤ ((1 - a) - 2 * eig) / (1 + a) := by
  apply (le_div_iff₀ (show 0 < 1 + a by positivity)).mpr
  nlinarith

lemma filter_quadratic_bound {ι : Type*} [Fintype ι] (eig coeff : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (he : ∀ i, eig i ≤ 1)
    (hcoeff : ∑ i, coeff i ^ 2 ≤ 1) (n : ℕ) :
    ∑ i, (eig i + a) * ((Chebyshev.T ℝ (n : ℤ)).eval
      (((1 - a) - 2 * eig i) / (1 + a)) * coeff i) ^ 2 ≤ 2 := by
  have hpoint (i : ι) : (eig i + a) * ((Chebyshev.T ℝ (n : ℤ)).eval
      (((1 - a) - 2 * eig i) / (1 + a)) * coeff i) ^ 2 ≤ (1 + a) * coeff i ^ 2 := by
    by_cases hi : -a ≤ eig i
    · obtain ⟨hl, hu⟩ := transformed_interval ha hi (he i)
      have hb := chebyshev_unit_bound n hl hu
      have hp : ((Chebyshev.T ℝ (n : ℤ)).eval (((1 - a) - 2 * eig i) / (1 + a))) ^ 2 ≤ 1 := by
        obtain ⟨h₀, h₁⟩ := abs_le.mp hb
        nlinarith
      have hs := mul_le_mul_of_nonneg_right hp (sq_nonneg (coeff i))
      have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ eig i + a by linarith)
      have he' := mul_le_mul_of_nonneg_right (he i) (sq_nonneg (coeff i))
      nlinarith
    · have hn := mul_nonpos_of_nonpos_of_nonneg (show eig i + a ≤ 0 by linarith) (sq_nonneg
        ((Chebyshev.T ℝ (n : ℤ)).eval (((1 - a) - 2 * eig i) / (1 + a)) * coeff i))
      exact hn.trans (mul_nonneg (by positivity) (sq_nonneg _))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [← Finset.mul_sum] at hsum
  have hm := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ 1 + a by positivity)
  linarith

lemma sufficient_filter_degree {a d : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (hd : 1 ≤ d)
    (n : ℕ) (hn : 2 * Real.log (16 * d / a) / Real.sqrt a ≤ n) :
    128 * d / a ≤ Real.exp ((n : ℝ) * Real.sqrt a) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hd0 : 0 < d := by linarith
  have hx : 0 < 16 * d / a := by positivity
  have hnx := (div_le_iff₀ hs).mp hn
  have he := Real.exp_le_exp.mpr hnx
  have heq : Real.exp (2 * Real.log (16 * d / a)) = (16 * d / a) ^ 2 := by
    rw [show (2 : ℝ) * Real.log (16 * d / a) = Real.log (16 * d / a) + Real.log (16 * d / a) by ring,
      Real.exp_add, Real.exp_log hx]
    ring
  rw [heq] at he
  have hr : 8 ≤ 16 * d / a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_right hr hx.le
  have hbound : 128 * d / a ≤ (16 * d / a) ^ 2 := by convert hm using 1 <;> ring
  exact hbound.trans he

end LongTails.Proofs.RelativeCurvaturePolynomial
