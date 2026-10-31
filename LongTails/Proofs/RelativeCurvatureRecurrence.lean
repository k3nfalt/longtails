import LongTails.Proofs.RelativeCurvaturePolynomial
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace LongTails.Proofs.RelativeCurvatureRecurrence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def exactFilter (Z : E →L[ℝ] E) (u : E) : ℕ → E
  | 0 => u
  | 1 => Z u
  | n + 2 => (2 : ℝ) • Z (exactFilter Z u (n + 1)) - exactFilter Z u n

lemma coordinate_filter (Z : E →L[ℝ] E) (l : E →ₗ[ℝ] ℝ) (eig : ℝ)
    (hl : ∀ v, l (Z v) = eig * l v) (u : E) (n : ℕ) :
    l (exactFilter Z u n) = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval eig * l u := by
  induction n using Nat.twoStepInduction with
  | zero => simp [exactFilter]
  | one => simp [exactFilter, hl]
  | more n ih₀ ih₁ =>
    rw [exactFilter, map_sub, map_smul, hl, ih₀, ih₁]
    push_cast
    rw [Polynomial.Chebyshev.T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    simp only [smul_eq_mul]
    ring

lemma recurrence_error (Z : E →L[ℝ] E) (hZ : ‖Z‖ ≤ 5) (u : E) (w : ℕ → E)
    {τ : ℝ} (hτ : 0 ≤ τ) (h₀ : w 0 = u) (h₁ : ‖w 1 - Z u‖ ≤ τ)
    (hrec : ∀ n, ‖w (n + 2) - ((2 : ℝ) • Z (w (n + 1)) - w n)‖ ≤ 2 * τ)
    (n : ℕ) : ‖w n - exactFilter Z u n‖ ≤ τ * 12 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [exactFilter, h₀, hτ]
  | one => simpa only [exactFilter, pow_one] using h₁.trans (by linarith : τ ≤ τ * 12)
  | more n ih₀ ih₁ =>
    have hz : ‖Z (w (n + 1) - exactFilter Z u (n + 1))‖ ≤
        5 * ‖w (n + 1) - exactFilter Z u (n + 1)‖ :=
      (Z.le_opNorm _).trans (mul_le_mul_of_nonneg_right hZ (norm_nonneg _))
    have he : w (n + 2) - exactFilter Z u (n + 2) =
        (w (n + 2) - ((2 : ℝ) • Z (w (n + 1)) - w n)) +
          ((2 : ℝ) • Z (w (n + 1) - exactFilter Z u (n + 1)) -
            (w n - exactFilter Z u n)) := by
      rw [exactFilter, map_sub, smul_sub]
      abel
    have hnorm : ‖w (n + 2) - exactFilter Z u (n + 2)‖ ≤
        2 * τ + 10 * ‖w (n + 1) - exactFilter Z u (n + 1)‖ +
          ‖w n - exactFilter Z u n‖ := by
      rw [he]
      have h := (norm_add_le
        (w (n + 2) - ((2 : ℝ) • Z (w (n + 1)) - w n))
        ((2 : ℝ) • Z (w (n + 1) - exactFilter Z u (n + 1)) - (w n - exactFilter Z u n))).trans
        (add_le_add (hrec n) (norm_sub_le
          ((2 : ℝ) • Z (w (n + 1) - exactFilter Z u (n + 1))) (w n - exactFilter Z u n)))
      norm_num only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
      linarith
    have hp : (1 : ℝ) ≤ 12 ^ n := one_le_pow₀ (by norm_num)
    have hpt := mul_le_mul_of_nonneg_left hp hτ
    rw [pow_succ] at ih₁
    rw [pow_succ, pow_succ]
    nlinarith

end LongTails.Proofs.RelativeCurvatureRecurrence
