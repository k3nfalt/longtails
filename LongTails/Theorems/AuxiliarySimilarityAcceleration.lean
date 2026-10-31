import LongTails.Setups.AuxiliarySimilarityNonconvex
import LongTails.Proofs.AuxiliaryConvergence

namespace OracleTemplate.AuxiliarySimilarityAcceleration

open LongTails.Setups.AuxiliarySimilarityNonconvex
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Proofs.AuxiliaryConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p => ![(⌈2 ^ 19 * p.Δ * Real.sqrt (p.ρ * p.ε) / p.ε ^ 2⌉₊ + 1) * ((⌈6 * Real.sqrt (1 + p.δ / Real.sqrt (p.ρ * p.ε)) * Real.log (8 + 8 * p.δ / Real.sqrt (p.ρ * p.ε))⌉₊ + 1) * (⌈15 * Real.log (400 * (1 + (p.L + p.δ) / Real.sqrt (p.ρ * p.ε)))⌉₊ + 2) + 6), (⌈2 ^ 19 * p.Δ * Real.sqrt (p.ρ * p.ε) / p.ε ^ 2⌉₊ + 1) * ((⌈6 * Real.sqrt (1 + p.δ / Real.sqrt (p.ρ * p.ε)) * Real.log (8 + 8 * p.δ / Real.sqrt (p.ρ * p.ε))⌉₊ + 1) * ((⌈15 * Real.log (400 * (1 + (p.L + p.δ) / Real.sqrt (p.ρ * p.ε)))⌉₊ + 1) * (⌈(p.L / p.δ + 6) * Real.log (2 ^ 110 * (1 + (p.L + p.δ) / Real.sqrt (p.ρ * p.ε)) ^ 10 * (1 + p.Δ * Real.sqrt (p.ρ * p.ε) / p.ε ^ 2))⌉₊ + 3) + 1))]

theorem result : Convergence LongTails.Setups.AuxiliarySimilarityNonconvex.spec budget := by
  refine ⟨fun p => TwoPlan.algorithm p.x0 p.x0 (method (tuning p.L p.δ p.ρ p.Δ p.ε) p.x0), ?_,
    fun _ _ => trivial⟩
  intro p hp I O hO
  exact Filter.Eventually.of_forall fun ω => run_result p hp I O hO (budget p)
    (fun j => (calls_bound p.L p.δ p.ρ p.Δ p.ε p.x0 _ j).trans le_rfl) ω.1 ω.2

end OracleTemplate.AuxiliarySimilarityAcceleration
