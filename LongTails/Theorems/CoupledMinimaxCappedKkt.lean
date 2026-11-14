import LongTails.Setups.CoupledStronglyConcaveMinimax
import LongTails.Proofs.CoupledMinimaxKkt
import LongTails.Proofs.CoupledMinimaxBudget

namespace OracleTemplate.CoupledMinimaxCappedKkt

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxKkt
open LongTails.Proofs.CoupledMinimaxBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (2 + ⌈4 * Real.sqrt ((1 + p.μ + p.Lf + (1 + 2 * p.Z * (p.Gy + 1) / p.δ) * p.LJ + 2 * p.J) / p.μ)⌉₊ * ⌈Real.log (2 + 24 * (1 + p.μ + p.Lf + (1 + 2 * p.Z * (p.Gy + 1) / p.δ) * p.LJ + 2 * p.J) * p.DY * (1 + p.ε) * (2 + Real.sqrt p.constraints + 2 * p.Z * (p.Gy + 1) / p.δ) / p.ε) / Real.log 2⌉₊) * (1 + ⌈576 * (1 + p.μ + p.Lf + (1 + 2 * p.Z * (p.Gy + 1) / p.δ) * p.LJ + 2 * p.J) ^ 2 * (p.Gx * p.DX + p.Gy * p.DY + (1 + 2 * p.Z * (p.Gy + 1) / p.δ) * p.C) * (1 + p.ε) ^ 2 * (2 + Real.sqrt p.constraints + 2 * p.Z * (p.Gy + 1) / p.δ) ^ 2 / (p.μ * p.ε ^ 2)⌉₊)

theorem result : Convergence LongTails.Setups.CoupledStronglyConcaveMinimax.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hv K hK I O hO
  obtain ⟨H, hans⟩ := hO
  have hb : calls p ≤ budget p 0 := by
    have hh := calls_bound hv
    rw [conversion_factor] at hh
    simpa only [budget, smoothness, gapBound, cap] using hh
  have hcalls := hb.trans hK
  apply Filter.Eventually.of_forall
  rintro ⟨⟨⟩, ξ⟩
  exact execute_kkt hv H O hans hcalls ξ

end OracleTemplate.CoupledMinimaxCappedKkt
