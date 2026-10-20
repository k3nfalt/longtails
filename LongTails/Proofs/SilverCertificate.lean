import LongTails.Algorithms.SilverSchedule
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.SilverCertificate

open LongTails.Algorithms.SilverSchedule
open scoped RealInnerProductSpace

lemma ratio_pos : 0 < ratio := by
  unfold ratio
  positivity

lemma ratio_gt_two : 2 < ratio := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  unfold ratio
  nlinarith

lemma ratio_lt_three : ratio < 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  unfold ratio
  nlinarith

lemma ratio_square : ratio ^ 2 = 2 * ratio + 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold ratio
  nlinarith

lemma ratio_inverse : 1 / ratio = ratio - 2 := by
  apply (div_eq_iff (ne_of_gt ratio_pos)).2
  nlinarith [ratio_square]

lemma steps_length (k : ℕ) : (steps k).length + 1 = 2 ^ k := by
  induction k with
  | zero => simp [steps]
  | succ k ih =>
    simp only [steps, List.length_append, List.length_singleton, pow_succ]
    omega

lemma steps_sum (k : ℕ) : (steps k).sum = ratio ^ k - 1 := by
  induction k with
  | zero => simp [steps]
  | succ k ih =>
    simp only [steps, List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih, pow_succ]
    rw [div_eq_mul_inv, ← one_div, ratio_inverse]
    ring

lemma steps_positive (k : ℕ) : ∀ h ∈ steps k, 0 < h := by
  induction k with
  | zero => simp [steps]
  | succ k ih =>
    intro h hh
    simp only [steps, List.mem_append, List.mem_singleton] at hh
    rcases hh with (hh | rfl) | hh
    · exact ih h hh
    · exact add_pos_of_pos_of_nonneg zero_lt_one
        (div_nonneg (pow_nonneg (le_of_lt ratio_pos) _) (le_of_lt ratio_pos))
    · exact ih h hh

lemma join_step (k : ℕ) :
    1 + ratio ^ k / ratio = (ratio - 2) * ((steps k).sum + 1) + 1 := by
  rw [steps_sum, sub_add_cancel, div_eq_mul_inv, ← one_div, ratio_inverse]
  ring

noncomputable def historyMass : ℕ → ℝ
  | 0 => 0
  | k + 1 => (2 + 2 * ratio) * historyMass k + ratio ^ (k + 2) - ratio

lemma historyMass_join (k : ℕ) :
    historyMass (k + 1) = (2 + 2 * ratio) * historyMass k +
      ratio * (2 * (steps k).sum + (1 + ratio ^ k / ratio)) := by
  rw [historyMass, steps_sum, pow_add, ratio_square, div_eq_mul_inv, ← one_div, ratio_inverse]
  nlinarith [congrArg (fun x : ℝ => ratio ^ k * x) ratio_square]

lemma historyMass_bound (k : ℕ) :
    historyMass k ≤ 2 * ((2 + 2 * ratio) ^ k - ratio ^ k) := by
  induction k with
  | zero => simp [historyMass]
  | succ k ih =>
    have hp : 0 ≤ 2 + 2 * ratio := by linarith [ratio_pos]
    have hs := mul_le_mul_of_nonneg_left ih hp
    have hr : 0 ≤ ratio ^ k := pow_nonneg (le_of_lt ratio_pos) _
    have hr2 := congrArg (fun x : ℝ => ratio ^ k * x) ratio_square
    simp only [historyMass, pow_succ]
    nlinarith [ratio_pos, mul_nonneg hr (le_of_lt ratio_pos)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def history (S F T f : ℝ) (x g : E) : ℝ :=
  2 * F - 2 * S * f + T - ‖x‖ ^ 2 - S * (S + 1) * ‖g‖ ^ 2

noncomputable def defect (f₁ f₂ : ℝ) (x₁ x₂ g₁ g₂ : E) : ℝ :=
  2 * (f₁ - f₂) - 2 * ⟪g₂, x₁ - x₂⟫ - ‖g₁ - g₂‖ ^ 2

lemma defect_translate (f₁ f₂ : ℝ) (x₁ x₂ g₁ g₂ o : E) :
    defect f₁ f₂ (x₁ - o) (x₂ - o) g₁ g₂ = defect f₁ f₂ x₁ x₂ g₁ g₂ := by
  have he : x₁ - o - (x₂ - o) = x₁ - x₂ := by module
  simp only [defect, he]

lemma history_join_identity (S F₁ F₂ T₁ T₂ f₁ f₂ : ℝ) (a b c d : E) :
    let μ := (ratio - 2) * (S + 1) + 1
    let p := a - μ • c
    history (2 * S + μ) (F₁ + μ * f₁ + F₂)
        (T₁ + μ * (‖c‖ ^ 2 - 2 * ⟪c, a⟫) + T₂) f₂ b d =
      history S F₁ T₁ f₁ a c +
        (1 + 2 * ratio) * history S F₂ (T₂ + 2 * ⟪p - b, p⟫) f₂ (b - p) d +
        ratio * (2 * S * (f₁ + f₂) - 4 * F₂ - 2 * ⟪p - b, a + b⟫ - 2 * T₂ -
          S * (‖c‖ ^ 2 + ‖d‖ ^ 2) + 2 * ⟪c + d, p - b⟫) +
        ratio * defect f₁ f₂ a b c d + ratio * (μ - 1) * defect f₂ f₁ b a d c := by
  dsimp only
  simp only [history, defect, ← real_inner_self_eq_norm_sq, inner_sub_left,
    inner_sub_right, inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    real_inner_comm b a, real_inner_comm c a, real_inner_comm c b, real_inner_comm d c]
  linear_combination
    (-(S + 1) * (2 * S * ⟪c, c⟫ * ratio - 3 * S * ⟪c, c⟫ + S * ⟪d, d⟫ +
      2 * ⟪c, c⟫ * ratio - 2 * ⟪c, c⟫ - 2 * f₁ + 2 * f₂)) * ratio_square

end LongTails.Proofs.SilverCertificate
