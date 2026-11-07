import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Proofs.LogFreeLineSearch

noncomputable def cubicModel (φ₀ a h τ t : ℝ) : ℝ := φ₀ - a * t + h * t ^ 2 / 2 + τ * t ^ 3 / 6

lemma model_le_of_small {φ₀ a h τ t : ℝ} (ha : 0 ≤ a) (hha : h ≤ a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hτ : τ * t ^ 2 ≤ a) :
    cubicModel φ₀ a h τ t ≤ φ₀ - a * t / 3 := by
  unfold cubicModel
  have h1 : h * t ^ 2 / 2 ≤ a * t / 2 := by
    have : h * t ^ 2 ≤ a * t := by
      calc h * t ^ 2 = (h * t) * t := by ring
        _ ≤ (a * 1) * t := by
          apply mul_le_mul_of_nonneg_right _ ht0
          exact mul_le_mul hha ht1 ht0 ha
        _ = a * t := by ring
    linarith
  have h2 : τ * t ^ 3 / 6 ≤ a * t / 6 := by
    have : τ * t ^ 3 ≤ a * t := by
      calc τ * t ^ 3 = (τ * t ^ 2) * t := by ring
        _ ≤ a * t := mul_le_mul_of_nonneg_right hτ ht0
    linarith
  linarith

lemma grid_descent {φ₀ a h τ e : ℝ} (φ : ℝ → ℝ) (ha : 0 ≤ a) (hha : h ≤ a)
    (happrox : ∀ t ∈ ({1, 1 / 2, 1 / 4, 1 / 8, -1} : Set ℝ),
      φ t ≤ cubicModel φ₀ a h τ t + e) :
    ∃ t ∈ ({1, 1 / 2, 1 / 4, 1 / 8, -1} : Set ℝ), φ t ≤ φ₀ - a / 48 + e := by
  by_cases hτ0 : τ ≤ a
  · refine ⟨1, by simp, ?_⟩
    have hm := model_le_of_small (φ₀ := φ₀) (t := 1) ha hha (by norm_num) le_rfl
      (by simpa using hτ0)
    have := happrox 1 (by simp)
    linarith
  replace hτ0 := lt_of_not_ge hτ0
  have hτpos : 0 < τ := lt_of_le_of_lt ha hτ0
  by_cases hbig : 64 * a < τ
  · refine ⟨-1, by simp, ?_⟩
    have := happrox (-1) (by simp)
    unfold cubicModel at this
    nlinarith
  replace hbig := le_of_not_gt hbig
  by_cases h4 : 4 * a < τ
  · by_cases h16 : 16 * a < τ
    · refine ⟨1 / 8, by simp, ?_⟩
      have hm := model_le_of_small (φ₀ := φ₀) (t := 1 / 8) (h := h) (τ := τ) ha hha
        (by norm_num) (by norm_num) (by nlinarith)
      have := happrox (1 / 8) (by simp)
      linarith
    · replace h16 := le_of_not_gt h16
      refine ⟨1 / 4, by simp, ?_⟩
      have hm := model_le_of_small (φ₀ := φ₀) (t := 1 / 4) (h := h) (τ := τ) ha hha
        (by norm_num) (by norm_num) (by nlinarith)
      have := happrox (1 / 4) (by simp)
      linarith
  · replace h4 := le_of_not_gt h4
    refine ⟨1 / 2, by simp, ?_⟩
    have hm := model_le_of_small (φ₀ := φ₀) (t := 1 / 2) (h := h) (τ := τ) ha hha
      (by norm_num) (by norm_num) (by nlinarith)
    have := happrox (1 / 2) (by simp)
    linarith

end LongTails.Proofs.LogFreeLineSearch
