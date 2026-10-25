import LongTails.Setups.RelativeGeneralizedSmoothConvex
import LongTails.Proofs.RelativeGeneralizedConvergence

namespace LongTails.Theorems.RelativeErrorGeneralizedAcceleration

open OracleTemplate
open OracleTemplate.RelativeGeneralized
open LongTails.Setups.RelativeGeneralizedSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ 60 * (Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + p.α ^ 2 * (p.L0 * p.R ^ 2 / p.ε) + (1 + p.L1 * p.R) * (1 + Real.log (2 + p.L0 * p.R ^ 2 / p.ε + p.L1 * p.R + p.Δ / (p.L0 * p.R ^ 2))) + p.α ^ 2 * (p.L1 * p.R) ^ 2 * (1 + Real.log (2 + p.L0 * p.R ^ 2 / p.ε + p.L1 * p.R + p.Δ / (p.L0 * p.R ^ 2))) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.RelativeGeneralizedSmoothConvex.spec budget := by
  refine ⟨fun p => acceleration p (budget p 0), ?_, ?_⟩
  · intro p hp I oracle hadm
    obtain ⟨u, hu, hout⟩ := execution_accuracy p hp I oracle hadm
    refine ⟨u, hu, Filter.Eventually.of_forall ?_⟩
    intro ω
    rcases ω with ⟨seed, oracleSeed⟩
    cases seed
    exact hout oracleSeed
  · intro p _hp
    trivial

end LongTails.Theorems.RelativeErrorGeneralizedAcceleration
