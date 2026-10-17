import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic

namespace LongTails.Proofs.QuarticPrefixPath

variable {E : Type} [NormedAddCommGroup E]

lemma path_cauchy (x : ℕ → E) (n : ℕ) :
    ‖x n - x 0‖ ^ 2 ≤ (n : ℝ) * ∑ i ∈ Finset.range n, ‖x (i + 1) - x i‖ ^ 2 := by
  have he : ∑ i ∈ Finset.range n, (x (i + 1) - x i) = x n - x 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; abel
  have hn := norm_sum_le (Finset.range n) (fun i => x (i + 1) - x i)
  rw [he] at hn
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun i => ‖x (i + 1) - x i‖)
  simpa only [Finset.card_range] using hs.trans hc

lemma prefix_energy (x : ℕ → E) (F : ℕ → ℝ) {α C Δ : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (hstep : ∀ i < n, α * ‖x (i + 1) - x i‖ ^ 2 ≤ C * (F i - F (i + 1)))
    (hgap : F 0 - F n ≤ Δ) :
    α * ∑ i ∈ Finset.range n, ‖x (i + 1) - x i‖ ^ 2 ≤ C * Δ := by
  have hs := Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  have he : ∑ i ∈ Finset.range n, (F i - F (i + 1)) = F 0 - F n := by
    clear hstep hgap hs
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [he] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hgap hC)

lemma prefix_distance (x : ℕ → E) (F : ℕ → ℝ) {α C Δ : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (n : ℕ) (hstep : ∀ i < n, α * ‖x (i + 1) - x i‖ ^ 2 ≤ C * (F i - F (i + 1)))
    (hgap : F 0 - F n ≤ Δ) : α * ‖x n - x 0‖ ^ 2 ≤ C * n * Δ := by
  have he := prefix_energy x F hC n hstep hgap
  have hd := mul_le_mul_of_nonneg_left (path_cauchy x n) hα
  have hh := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hd, hh]

end LongTails.Proofs.QuarticPrefixPath
