import LongTails.Setups.HighDimensionalHeavyTailedNcsc
import LongTails.Theorems.HeavyTailedNcscAccelerated

namespace LongTails.Theorems.HighDimensionalHeavyTailedNcscUpperBound

open OracleTemplate

noncomputable def budget :
    (let S := LongTails.Setups.HighDimensionalHeavyTailedNcsc.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ =>
    let κ := q.L / q.μ
    let r := q.p / (q.p - 1)
    let A := q.L * q.Δ / q.ε ^ 2
    let u := q.σ / q.ε
    let Q := Real.log (2 + κ ^ 3 * q.L * (q.Δ + q.G ^ 2 / q.μ) / q.ε ^ 2)
    let Λ := 1 + Real.log (2 + κ + 1 / q.δ + A + (κ * u) ^ r + Q)
    ⌈((2 : ℝ) ^ 80 * r) ^ (r + 2) * Λ ^ (2 * r + 3) *
      (Real.sqrt κ * (1 + A + Q) + (A * κ ^ (r / 2) + κ ^ r) * u ^ r)⌉₊

theorem result : Convergence LongTails.Setups.HighDimensionalHeavyTailedNcsc.spec budget := by
  obtain ⟨mk, hmk, -⟩ := OracleTemplate.HeavyTailedNcscAccelerated.result
  refine ⟨fun q => mk (LongTails.Setups.HighDimensionalHeavyTailedNcsc.toGeneral q), ?_,
    fun _ _ => trivial⟩
  intro q hv f O hadm
  exact hmk _ hv.1 f O hadm

end LongTails.Theorems.HighDimensionalHeavyTailedNcscUpperBound
