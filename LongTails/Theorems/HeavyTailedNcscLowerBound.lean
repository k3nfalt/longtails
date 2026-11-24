import LongTails.Setups.HighDimensionalHeavyTailedNcsc
import LongTails.Proofs.HeavyTailNcscLowerAssembly
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.HeavyTailedNcscLowerBound

open OracleTemplate

noncomputable def budget :
    (let S := LongTails.Setups.HighDimensionalHeavyTailedNcsc.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ =>
    let κ := q.L / q.μ
    let A := q.L * q.Δ / q.ε ^ 2
    let u := q.σ / q.ε
    let r := q.p / (q.p - 1)
    ⌊(A * (1 + (Real.sqrt κ * u / 2 ^ 14) ^ r) + (κ * u / 2 ^ 5) ^ r) / 2 ^ 61⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalHeavyTailedNcsc.spec budget :=
  LongTails.Proofs.HeavyTailNcscLowerAssembly.nonConvergence

end LongTails.Theorems.HeavyTailedNcscLowerBound
