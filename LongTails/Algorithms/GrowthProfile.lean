import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace LongTails.Algorithms.GrowthProfile

variable {n : ℕ}

noncomputable def share (h : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ := h i / (1 - t + t * h i)

noncomputable def normalized (h : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  n * share h t i / ∑ j, share h t j

noncomputable def parameter (h : Fin n → ℝ) (ρ : ℝ) : ℝ := by
  classical
  exact if ht : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ ∑ i, normalized h s i ^ 2 = n * ρ then ht.choose else 0

noncomputable def profile (h : Fin n → ℝ) (ρ : ℝ) := normalized h (parameter h ρ)

end LongTails.Algorithms.GrowthProfile
