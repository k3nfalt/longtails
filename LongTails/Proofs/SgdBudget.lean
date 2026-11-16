import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace OracleTemplate.StochasticNonconvex

lemma tuning {L Δ σ ε : ℝ} (hL : 0 < L) (_hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let η := 1 / (L + 2 * L * σ ^ 2 / ε ^ 2)
    let K := ⌈4 * L * Δ / ε ^ 2 + 8 * L * Δ * σ ^ 2 / ε ^ 4⌉₊ + 1
    0 < η ∧ η * L ≤ 1 ∧
      ∀ value : ℝ, η / 2 * K * value ≤ Δ + K * (L * η ^ 2 / 2 * σ ^ 2) →
        value ≤ ε ^ 2 := by
  dsimp only
  let η := 1 / (L + 2 * L * σ ^ 2 / ε ^ 2)
  let K := ⌈4 * L * Δ / ε ^ 2 + 8 * L * Δ * σ ^ 2 / ε ^ 4⌉₊ + 1
  have hden : 0 < L + 2 * L * σ ^ 2 / ε ^ 2 := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have heq : η * (L + 2 * L * σ ^ 2 / ε ^ 2) = 1 := by
    dsimp [η]
    field_simp
  have hηL : η * L ≤ 1 := by
    have := mul_nonneg hη.le (show 0 ≤ 2 * L * σ ^ 2 / ε ^ 2 by positivity)
    nlinarith [heq]
  refine ⟨hη, hηL, ?_⟩
  intro value hv
  have heq' : η * (L * ε ^ 2 + 2 * L * σ ^ 2) = ε ^ 2 := by
    calc
      _ = (η * (L + 2 * L * σ ^ 2 / ε ^ 2)) * ε ^ 2 := by field_simp
      _ = ε ^ 2 := by rw [heq, one_mul]
  have hnoise : L * η * σ ^ 2 ≤ ε ^ 2 / 2 := by
    have := mul_nonneg (mul_nonneg hη.le hL.le) (sq_nonneg ε)
    nlinarith [heq']
  have hformula : 4 * Δ / (η * ε ^ 2) =
      4 * L * Δ / ε ^ 2 + 8 * L * Δ * σ ^ 2 / ε ^ 4 := by
    dsimp [η]
    field_simp
    ring
  have hceil : 4 * Δ / (η * ε ^ 2) ≤ (K : ℝ) := by
    rw [hformula]
    exact (Nat.le_ceil _).trans (by dsimp [K]; exact_mod_cast Nat.le_succ _)
  have hinit := (div_le_iff₀ (mul_pos hη (sq_pos_of_pos hε))).mp hceil
  have hKr : (0 : ℝ) < K := by dsimp [K]; positivity
  have hn := mul_le_mul_of_nonneg_left hnoise (show 0 ≤ (K : ℝ) * η / 2 by positivity)
  have hcoef : 0 < η / 2 * K := by positivity
  apply (mul_le_mul_iff_right₀ hcoef).mp
  nlinarith

end OracleTemplate.StochasticNonconvex
