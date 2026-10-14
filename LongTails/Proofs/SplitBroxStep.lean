import LongTails.Algorithms.SplitBrox
import Mathlib.Tactic

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

lemma weight_le_one (n : ℕ) : weight n ≤ 1 := by
  unfold weight
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma mix_mem {C : Set E} (hC : Convex ℝ C) {x y : E}
    (hx : x ∈ C) (hy : y ∈ C) (n : ℕ) : mix n y x ∈ C := by
  exact hC hy hx (sub_nonneg.mpr (weight_le_one n)) (le_of_lt (weight_pos n)) (by ring)

def potentialWeight (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1) / 2

lemma potentialWeight_nonneg (n : ℕ) : 0 ≤ potentialWeight n := by
  unfold potentialWeight; positivity

lemma potential_weight_identity (n : ℕ) :
    potentialWeight (n + 1) * (1 - weight n) = potentialWeight n := by
  unfold potentialWeight weight
  push_cast
  field_simp
  ring

lemma potential_weight_error (n : ℕ) :
    potentialWeight (n + 1) * (weight n ^ 2 / 2) ≤ 1 := by
  unfold potentialWeight weight
  push_cast
  have hn : 0 < (n : ℝ) + 2 := by positivity
  field_simp
  nlinarith

lemma cut_step {f : E → ℝ} {g x y u : E} {fstar L r : ℝ}
    (n : ℕ) (hL : 0 ≤ L)
    (hupper : f (mix n y u) ≤ f (mix n y x) +
      ⟪g, mix n y u - mix n y x⟫ + L / 2 * ‖mix n y u - mix n y x‖ ^ 2)
    (hlower : f (mix n y x) + ⟪g, y - mix n y x⟫ ≤ f y)
    (hcut : f (mix n y x) + ⟪g, u - mix n y x⟫ ≤ fstar)
    (hdist : ‖u - x‖ ≤ r) :
    f (mix n y u) - fstar ≤ (1 - weight n) * (f y - fstar) +
      L * weight n ^ 2 / 2 * r ^ 2 := by
  have he : mix n y u - mix n y x = weight n • (u - x) := by unfold mix; module
  have hi : ⟪g, mix n y u - mix n y x⟫ =
      (1 - weight n) * ⟪g, y - mix n y x⟫ + weight n * ⟪g, u - mix n y x⟫ := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    congr 1
    unfold mix
    module
  rw [hi, he, norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos n), mul_pow] at hupper
  have h1 := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr (weight_le_one n))
  have h2 := mul_le_mul_of_nonneg_left hcut (le_of_lt (weight_pos n))
  have hd := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ L * weight n ^ 2 / 2 by positivity)
  nlinarith

lemma weighted_cut_step {f : E → ℝ} {y u : E} {fstar L r : ℝ}
    (n : ℕ) (hL : 0 ≤ L)
    (hstep : f (mix n y u) - fstar ≤ (1 - weight n) * (f y - fstar) +
      L * weight n ^ 2 / 2 * r ^ 2) :
    potentialWeight (n + 1) * (f (mix n y u) - fstar) ≤
      potentialWeight n * (f y - fstar) + L * r ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hstep (potentialWeight_nonneg (n + 1))
  have he := mul_le_mul_of_nonneg_right (potential_weight_error n)
    (show 0 ≤ L * r ^ 2 by positivity)
  rw [mul_add, ← mul_assoc, potential_weight_identity] at h
  nlinarith

lemma radius_pos {b : ℝ} (hb : 0 < b) (j : ℕ) : 0 < radius b j := by
  unfold radius; positivity

lemma radius_succ (b : ℝ) (j : ℕ) : radius b (j + 1) = 2 * radius b j := by
  unfold radius
  rw [pow_succ]
  ring

lemma doublings_charge (j : ℕ) : (j + 1 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 2 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ]]
    push_cast
    have hpow : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith

end OracleTemplate.SplitBrox
