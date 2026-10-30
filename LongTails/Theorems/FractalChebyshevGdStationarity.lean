import LongTails.Setups.HessianLipschitzGradientStationarity
import LongTails.Proofs.RestartedChebyshevConvergence

namespace OracleTemplate.RestartedScheduleGD.FractalChebyshevGdStationarity

open LongTails.Setups.HessianLipschitzGradientStationarity

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈1000 * Real.logb 2 (2 + p.L ^ 2 / (p.ρ * p.ε)) * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 9 : ℝ) * p.L * p.Δ / p.ε ^ 2 + (p.L ^ 2 / (p.ρ * p.ε)) ^ (1 / 9 : ℝ) + 2⌉₊

theorem result : Convergence LongTails.Setups.HessianLipschitzGradientStationarity.spec budget := by
  refine ⟨fun p => chebyshevGd p.L p.ρ p.ε p.x0, ?_, ?_⟩
  · intro p hp f O ho
    obtain ⟨hL, hρ, hΔ0, hε⟩ := hp
    obtain ⟨hf, hlip, hH, hΔ, hO⟩ := ho
    dsimp only
    intro ω
    change ‖gradient f (execute O (chebyshevGd p.L p.ρ p.ε p.x0) (budget p) ω.1 ω.2)‖ ≤ p.ε
    erw [execute_eq_of_answer_eq O (gradient f) hO, execute_iterate]
    exact chebyshev_output hL hρ hΔ0 hε hf hlip hH hΔ _ (Nat.le_ceil _)
  · intro p hp
    refine ⟨chebyshevThreshold p.L p.ρ p.ε, chebyshevRadius p.L p.ρ p.ε,
      chebyshevSteps p.L p.ρ p.ε, ?_, rfl⟩
    intro h hh
    unfold chebyshevSteps at hh
    split_ifs at hh with hk
    · exact schedule_pos hp.1 hk h hh
    · simp at hh

end OracleTemplate.RestartedScheduleGD.FractalChebyshevGdStationarity
