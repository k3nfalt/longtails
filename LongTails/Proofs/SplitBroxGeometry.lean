import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inward_linear_nonneg {C : Set E} (hC : Convex ℝ C)
    {x g p y : E} {r : ℝ} (hp : p ∈ C) (hy : y ∈ C)
    (hr : 0 ≤ r) (hyr : ‖y - x‖ ≤ r)
    (hmin : ∀ z ∈ C, ‖z - x‖ ≤ r → ⟪g, y⟫ ≤ ⟪g, z⟫)
    (hin : ⟪y - x, p - y⟫ < 0) : 0 ≤ ⟪g, p - y⟫ := by
  let a : ℝ := -⟪y - x, p - y⟫
  let b : ℝ := ‖p - y‖ ^ 2 + 1
  let θ : ℝ := min 1 (a / b)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hθ : 0 < θ := lt_min zero_lt_one (div_pos ha hb)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθb : θ * b ≤ a := (le_div_iff₀ hb).mp (min_le_right _ _)
  have hm : θ * ‖p - y‖ ^ 2 ≤ a := by dsimp [b] at hθb; nlinarith
  have hz : (1 - θ) • y + θ • p ∈ C :=
    hC hy hp (by linarith) (le_of_lt hθ) (by ring)
  have heq : (1 - θ) • y + θ • p - x = (y - x) + θ • (p - y) := by module
  have hn : ‖(1 - θ) • y + θ • p - x‖ ^ 2 ≤ r ^ 2 := by
    rw [heq, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_smul_right]
    have hs : ‖y - x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyr 2
    have hmul := mul_le_mul_of_nonneg_left hm (le_of_lt hθ)
    dsimp [a] at hmul
    nlinarith
  have hnr : ‖(1 - θ) • y + θ • p - x‖ ≤ r := by nlinarith [norm_nonneg ((1 - θ) • y + θ • p - x)]
  have h := hmin _ hz hnr
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [inner_sub_right]
  nlinarith

lemma interior_linear_nonneg {C : Set E} (hC : Convex ℝ C)
    {x g p y : E} {r : ℝ} (hp : p ∈ C) (hy : y ∈ C)
    (hyr : ‖y - x‖ < r)
    (hmin : ∀ z ∈ C, ‖z - x‖ ≤ r → ⟪g, y⟫ ≤ ⟪g, z⟫) :
    0 ≤ ⟪g, p - y⟫ := by
  let a : ℝ := r - ‖y - x‖
  let b : ℝ := ‖p - y‖ + 1
  let θ : ℝ := min 1 (a / b)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hθ : 0 < θ := lt_min zero_lt_one (div_pos ha hb)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθb : θ * b ≤ a := (le_div_iff₀ hb).mp (min_le_right _ _)
  have hm : θ * ‖p - y‖ ≤ a := by dsimp [b] at hθb; nlinarith
  have hz : (1 - θ) • y + θ • p ∈ C :=
    hC hy hp (by linarith) (le_of_lt hθ) (by ring)
  have heq : (1 - θ) • y + θ • p - x = (y - x) + θ • (p - y) := by module
  have hnr : ‖(1 - θ) • y + θ • p - x‖ ≤ r := by
    rw [heq]
    calc
      _ ≤ ‖y - x‖ + ‖θ • (p - y)‖ := norm_add_le _ _
      _ = ‖y - x‖ + θ * ‖p - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
      _ ≤ r := by dsimp [a] at hm; linarith
  have h := hmin _ hz hnr
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [inner_sub_right]
  nlinarith

lemma local_strict_cut_contraction {C : Set E} (hC : Convex ℝ C)
    {x g p y : E} {r : ℝ} (hp : p ∈ C) (hy : y ∈ C)
    (hr : 0 ≤ r) (hyr : ‖y - x‖ ≤ r)
    (hmin : ∀ z ∈ C, ‖z - x‖ ≤ r → ⟪g, y⟫ ≤ ⟪g, z⟫)
    (hcut : ⟪g, p⟫ < ⟪g, y⟫) :
    ‖y - x‖ = r ∧ ‖y - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - r ^ 2 := by
  have hneg : ⟪g, p - y⟫ < 0 := by rw [inner_sub_right]; linarith
  have ha : 0 ≤ ⟪y - x, p - y⟫ := by
    by_contra h
    have h := inward_linear_nonneg hC hp hy hr hyr hmin (lt_of_not_ge h)
    linarith
  have hb : ‖y - x‖ = r := by
    apply le_antisymm hyr
    by_contra h
    have h := interior_linear_nonneg hC hp hy (lt_of_not_ge h) hmin
    linarith
  refine ⟨hb, ?_⟩
  have he : ‖p - x‖ ^ 2 = ‖p - y‖ ^ 2 + ‖y - x‖ ^ 2 +
      2 * ⟪y - x, p - y⟫ := by
    rw [show p - x = (p - y) + (y - x) by module, norm_add_sq_real,
      real_inner_comm (p - y) (y - x)]
    ring
  rw [norm_sub_rev p x, norm_sub_rev p y, hb] at he
  linarith

end OracleTemplate.SplitBrox
