import LongTails.Proofs.NcConcaveLower
import LongTails.Setups.StochasticNonconvexConcaveMinimax
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.StochasticNonconvexConcaveMinimaxLowerBound

open LongTails.Setups.StochasticNonconvexConcaveMinimax
open LongTails.Proofs.NcConcaveParams LongTails.Proofs.NcConcaveAssembly
open LongTails.Proofs.NcConcaveLower

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  ⌊p.L ^ 2 * p.D * p.Δ / (2 ^ 100 * p.ε ^ 3) +
    p.L ^ 3 * p.D ^ 2 * p.Δ * p.σ ^ 2 / (2 ^ 165 * p.ε ^ 6)⌋₊

theorem result : NonConvergence spec budget := by
  intro q hv A _ b hb
  have hpos : 0 ≤ B1 q + B2 q := by
    have := hL hv; have := hΔ hv; have := hD hv; have := hε hv
    unfold B1 B2; positivity
  have hN : (b 0 : ℝ) ≤ B1 q + B2 q := by
    have h := hb 0
    have h' : b 0 ≤ ⌊B1 q + B2 q⌋₊ := h
    exact (Nat.le_floor_iff hpos).mp h'
  obtain ⟨W, hW⟩ := exists_failure hv A (b 0) hN
  refine ⟨hardF q W, hardOracle q W, hard_admissible hv W, ?_⟩
  have hbeq : b = fun _ => b 0 := funext fun i => by rw [Fin.fin_one_eq_zero i]
  rw [hbeq]
  exact hW

end LongTails.Theorems.StochasticNonconvexConcaveMinimaxLowerBound
