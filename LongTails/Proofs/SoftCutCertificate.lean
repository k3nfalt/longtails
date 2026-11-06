import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SoftCutCertificate

lemma capped_square_sum {ι : Type*} [Fintype ι] (θ : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    ∑ i, θ i ^ 2 ≤ ∑ i, θ i := by
  apply Finset.sum_le_sum
  intro i _
  nlinarith [(hθ i).1, (hθ i).2]

lemma weighted_error_sq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : ι → ℝ) (e x : ι → E) (y : E) (R V W : ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hW : 0 ≤ W) (hy : ‖y‖ ≤ R)
    (hop : ‖∑ i, θ i • e i‖ ^ 2 ≤ V * ∑ i, θ i ^ 2)
    (hintercept : ∑ i, ⟪e i, x i⟫ ^ 2 ≤ W) :
    (∑ i, θ i * ⟪e i, x i - y⟫) ^ 2 ≤
      2 * (R ^ 2 * V + W) * ∑ i, θ i := by
  have hs := capped_square_sum θ hθ
  have hs0 : 0 ≤ ∑ i, θ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ (fun i => ⟪e i, x i⟫)
  have hc' : (∑ i, θ i * ⟪e i, x i⟫) ^ 2 ≤ (∑ i, θ i) * W := by
    exact hc.trans ((mul_le_mul_of_nonneg_left hintercept hs0).trans
      (mul_le_mul_of_nonneg_right hs hW))
  have hi := abs_real_inner_le_norm (∑ i, θ i • e i) y
  have hn : 0 ≤ ‖∑ i, θ i • e i‖ := norm_nonneg _
  have hi' : |⟪∑ i, θ i • e i, y⟫| ≤ ‖∑ i, θ i • e i‖ * R :=
    hi.trans (mul_le_mul_of_nonneg_left hy hn)
  have hi2 : ⟪∑ i, θ i • e i, y⟫ ^ 2 ≤ R ^ 2 * V * ∑ i, θ i := by
    have hsq := sq_le_sq₀ (abs_nonneg ⟪∑ i, θ i • e i, y⟫)
      (mul_nonneg hn hR) |>.2 hi'
    rw [sq_abs, mul_pow] at hsq
    have hbound := mul_le_mul_of_nonneg_right
      (hop.trans (mul_le_mul_of_nonneg_left hs hV)) (sq_nonneg R)
    nlinarith
  have heq : (∑ i, θ i * ⟪e i, x i - y⟫) =
      (∑ i, θ i * ⟪e i, x i⟫) - ⟪∑ i, θ i • e i, y⟫ := by
    simp [inner_sub_right, sum_inner, real_inner_smul_left, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  nlinarith [sq_nonneg ((∑ i, θ i * ⟪e i, x i⟫) + ⟪∑ i, θ i • e i, y⟫)]

lemma normalized_certificate {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : ι → ℝ) (v e x : ι → E) (y : E) (α margin : ℝ)
    (hS : 0 < ∑ i, θ i)
    (hcut : margin ≤ ∑ i, θ i * (⟪v i + e i, y - x i⟫ + α / 2))
    (herror : |∑ i, θ i * ⟪e i, x i - y⟫| ≤ margin) :
    ∑ i, (θ i / ∑ j, θ j) * ⟪v i, x i - y⟫ ≤ α / 2 := by
  have heq : (∑ i, θ i * (⟪v i + e i, y - x i⟫ + α / 2)) =
      (α / 2) * (∑ i, θ i) - (∑ i, θ i * ⟪v i, x i - y⟫) -
      (∑ i, θ i * ⟪e i, x i - y⟫) := by
    simp only [inner_add_left, inner_sub_right, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [heq] at hcut
  have herr := (abs_le.mp herror).1
  have hnum : (∑ i, θ i * ⟪v i, x i - y⟫) ≤ (α / 2) * (∑ i, θ i) := by
    linarith
  have hout := (div_le_iff₀ hS).2 hnum
  simpa only [Finset.sum_div, div_mul_eq_mul_div] using hout

lemma weighted_error_le_margin {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : ι → ℝ) (e x : ι → E) (y : E) (R V W margin : ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hW : 0 ≤ W) (hy : ‖y‖ ≤ R)
    (hop : ‖∑ i, θ i • e i‖ ^ 2 ≤ V * ∑ i, θ i ^ 2)
    (hintercept : ∑ i, ⟪e i, x i⟫ ^ 2 ≤ W)
    (hmargin : 0 ≤ margin)
    (hbudget : 2 * (R ^ 2 * V + W) * Fintype.card ι ≤ margin ^ 2) :
    |∑ i, θ i * ⟪e i, x i - y⟫| ≤ margin := by
  have hsq := weighted_error_sq θ e x y R V W hθ hR hV hW hy hop hintercept
  have hS : ∑ i, θ i ≤ (Fintype.card ι : ℝ) := by
    calc
      ∑ i, θ i ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hθ i).2
      _ = _ := by simp
  have hbound := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ 2 * (R ^ 2 * V + W) by positivity)
  have habs := sq_abs (∑ i, θ i * ⟪e i, x i - y⟫)
  nlinarith [abs_nonneg (∑ i, θ i * ⟪e i, x i - y⟫)]

lemma profile_support {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℝ → E → ℝ) (w s : ι → ℝ) (v x : ι → E)
    (a z δ : ℝ) (y : E) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hsupport : ∀ i, s i * (z - a) + ⟪v i, y - x i⟫ ≤ f z y - f a (x i))
    (hcertificate : ∑ i, w i * ⟪v i, x i - y⟫ ≤ δ) :
    (∑ i, w i * f a (x i)) + (∑ i, w i * s i) * (z - a) ≤ f z y + δ := by
  have hi := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hsupport i) (hw i))
  have heq : (∑ i, w i * (s i * (z - a) + ⟪v i, y - x i⟫)) =
      (∑ i, w i * s i) * (z - a) - (∑ i, w i * ⟪v i, x i - y⟫) := by
    have heach (i : ι) : w i * (s i * (z - a) + ⟪v i, y - x i⟫) =
        (w i * s i) * (z - a) - w i * ⟪v i, x i - y⟫ := by
      simp only [inner_sub_right]
      ring
    simp_rw [heach, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hrhs : (∑ i, w i * (f z y - f a (x i))) =
      f z y - ∑ i, w i * f a (x i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum, one_mul]
  rw [heq, hrhs] at hi
  linarith

end LongTails.Proofs.SoftCutCertificate
