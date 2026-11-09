import LongTails.Setups.ChiSquareConstrainedDro
import LongTails.Proofs.ChiSquareConvergence

namespace OracleTemplate.ChiSquareBracketedDro

open LongTails.Setups.ChiSquareConstrainedDro
open OracleTemplate.ChiSquareDro

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => (Nat.clog 2 ⌈8 * Real.sqrt (1 + 2 * q.ρ) * (q.B + q.B / Real.sqrt q.ρ) / q.ε⌉₊ + 2) ^ 2 * (⌈2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2⌉₊ + 144)

theorem result : Convergence LongTails.Setups.ChiSquareConstrainedDro.spec budget :=
  ⟨bracketAlgorithm, fun q hq I O hadm => bracket_successful q hq I O hadm (bracket_budget q),
    fun _ _ => trivial⟩

end OracleTemplate.ChiSquareBracketedDro
