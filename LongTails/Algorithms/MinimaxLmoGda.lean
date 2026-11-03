import LongTails.Setups.MinimaxLmo

namespace LongTails.Algorithms.MinimaxLmoGda

open OracleTemplate
open LongTails.Setups.UscgConstant (Space constantMomentum)
open LongTails.Setups.MinimaxLmo (lmoGda)

noncomputable def constantGda {d₁ d₂ : ℕ} (lmo : Space d₁ → Space d₁) (x₁ : Space d₁) (y₁ : Space d₂) (T : ℕ)
    (γ a β c : ℝ) : Algorithm (Space d₁ × Space d₂) (Space d₁ × Space d₂) (Space d₁) :=
  lmoGda lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) T (PMF.uniformOfFintype (Fin (T + 1))) x₁ y₁

end LongTails.Algorithms.MinimaxLmoGda
