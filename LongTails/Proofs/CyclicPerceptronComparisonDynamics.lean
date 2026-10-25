import LongTails.Proofs.CyclicPerceptronBlocks

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronComparisonDynamics

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks

structure Comparison (d : ℕ) where
  U : Features d
  V : Features d
  R : Features d
  B : ℝ
  positivePairs : ℕ

noncomputable def comparisonStep {d : ℕ} (b : Bool) (β : ℝ)
    (s : Comparison d) (u : Features d) : Comparison d :=
  ⟨s.U + u, s.V + (if b then u else 0), s.R + (if b then 0 else u),
    s.B + ⟪s.R, u⟫ - β, s.positivePairs + (if b then 0 else 1)⟩

noncomputable def comparisonBias {d : ℕ} (s : Comparison d) : ℝ := s.B + ⟪s.V, s.U⟫

lemma comparison_partition {d : ℕ} (b : Bool) (β : ℝ) (s : Comparison d)
    (u : Features d) (h : s.R + s.V = s.U) :
    (comparisonStep b β s u).R + (comparisonStep b β s u).V =
      (comparisonStep b β s u).U := by
  cases b <;> simp only [comparisonStep, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [← h]; module

lemma positive_bias_step {d : ℕ} (β : ℝ) (s : Comparison d)
    (u : Features d) (h : s.R + s.V = s.U) :
    comparisonBias (comparisonStep false β s u) = comparisonBias s + ⟪s.U, u⟫ - β := by
  simp only [comparisonBias, comparisonStep, Bool.false_eq_true, ↓reduceIte, add_zero,
    inner_add_right]
  rw [← h, inner_add_left]
  ring

lemma negative_bias_step {d : ℕ} (β : ℝ) (s : Comparison d)
    (u : Features d) (h : s.R + s.V = s.U) :
    comparisonBias (comparisonStep true β s u) =
      comparisonBias s + 2 * ⟪s.U, u⟫ + ‖u‖ ^ 2 - β := by
  simp only [comparisonBias, comparisonStep, ↓reduceIte, inner_add_left, inner_add_right,
    real_inner_self_eq_norm_sq]
  have hp : ⟪s.R, u⟫ + ⟪s.V, u⟫ = ⟪s.U, u⟫ := by rw [← h, inner_add_left]
  linarith [real_inner_comm u s.U]

structure ComparisonBound {d : ℕ} (j : ℝ) (s : Comparison d) : Prop where
  U_bound : ‖s.U‖ ≤ j
  V_bound : ‖s.V‖ ≤ j
  R_bound : ‖s.R‖ ≤ j
  B_bound : |s.B| ≤ j ^ 2 + j

lemma comparison_bound_step {d : ℕ} (b : Bool) (β j : ℝ) (s : Comparison d)
    (u : Features d) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hj : 0 ≤ j)
    (hu : ‖u‖ ≤ 1) (hs : ComparisonBound j s) :
    ComparisonBound (j + 1) (comparisonStep b β s u) := by
  constructor
  · exact (norm_add_le _ _).trans (by linarith [hs.U_bound])
  · have ht : ‖(if b then u else 0)‖ ≤ (1 : ℝ) := by cases b <;> simp_all
    exact (norm_add_le _ _).trans (by linarith [hs.V_bound])
  · have ht : ‖(if b then 0 else u)‖ ≤ (1 : ℝ) := by cases b <;> simp_all
    exact (norm_add_le _ _).trans (by linarith [hs.R_bound])
  · change |s.B + ⟪s.R, u⟫ - β| ≤ (j + 1) ^ 2 + (j + 1)
    have hi : |⟪s.R, u⟫| ≤ j := by
      have hm := mul_le_mul hs.R_bound hu (norm_nonneg u) hj
      exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
    have ht := abs_sub (s.B + ⟪s.R, u⟫) β
    have ht' := abs_add_le s.B ⟪s.R, u⟫
    rw [abs_of_nonneg hβ] at ht
    nlinarith [hs.B_bound]

end LongTails.Proofs.CyclicPerceptronComparisonDynamics
