import LongTails.Setups.SmoothHessianLipschitzGd
import LongTails.Proofs.RecoveryFractalBudget

namespace LongTails.Theorems.RecoveryFractalGdStationarity

open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈262144 * (8 + Real.logb 2 (2 + p.L * p.Δ / p.ε ^ 2)) ^ (4 / 3 : ℝ) * (p.Δ * p.L ^ (2 / 3 : ℝ) * p.ρ ^ (1 / 6 : ℝ) / p.ε ^ (11 / 6 : ℝ) + Real.sqrt (p.L * p.Δ) / p.ε + p.L ^ (11 / 17 : ℝ) * p.Δ ^ (15 / 17 : ℝ) * p.ρ ^ (2 / 17 : ℝ) / p.ε ^ (28 / 17 : ℝ) + 1)⌉₊

theorem result : Convergence LongTails.Setups.SmoothHessianLipschitzGd.spec budget := by
  refine ⟨method, ?_, ?_⟩
  · intro p hp f O ho
    obtain ⟨hL, hρ, hΔ, hε⟩ := hp
    obtain ⟨hf, hlip, hH, hgap, hO⟩ := ho
    dsimp only
    filter_upwards [] with ω
    change ‖gradient f (execute O (method p) (budget p) ω.1 ω.2)‖ ≤ p.ε
    have hb : budget p = fun _ => ⌈rateExpression p⌉₊ := by
      funext i
      rw [rateExpression_expanded p hL hρ hΔ hε]
      rfl
    rw [hb]
    exact rate_output_accuracy p hL hρ hΔ hε f hf hH hlip hgap O hO _ le_rfl ω.1 ω.2
  · intro p hp
    exact LongTails.Proofs.RecoveryFractalExecution.allowed p hp.1

end LongTails.Theorems.RecoveryFractalGdStationarity
