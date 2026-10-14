import LongTails.Setups.TerminalClippingConvex
import LongTails.Proofs.TerminalClippingConvergence

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * max 1 ⌈2 ^ 40 * (p.B * p.R ^ 2 + p.G ^ 2 / p.B) ^ 2 * Real.log (8 / p.δ) ^ 2 / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.TerminalClippingConvex.spec budget := convergence

end OracleTemplate.TerminalClipping
