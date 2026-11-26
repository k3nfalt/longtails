import LongTails.Setups.TerminalClippingConvex
import LongTails.Proofs.TerminalClippingSingleLogConvergence

open LongTails.Setups.TerminalClippingConvex

namespace OracleTemplate.TerminalClippingSingleLog

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let q := Real.log (8 / p.δ)
  let W := p.G ^ 2 + 16 * p.B ^ 2 * p.R ^ 2
  if p.G * p.R ≤ p.ε then 0 else 2 * ⌈576 * p.R ^ 2 * W * q / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.TerminalClippingConvex.spec budget := by
  have he : budget = fun p _ => 2 * horizon p.toPublic := by
    funext p i
    by_cases h : p.G * p.R ≤ p.ε <;> simp [budget,horizon,h]
  rw [he]
  exact convergence

end OracleTemplate.TerminalClippingSingleLog
