import LongTails.Setups.RiverValleyHillNoise
import LongTails.Proofs.RiverValleyConvergence

namespace OracleTemplate.RiverValley

open LongTails.Setups.RiverValleyHillNoise

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈256 * q.Δ * (8 * q.Lv + 64 * (2 * q.Lh * q.σu ^ 2 + (q.Γ * q.Lh + 2 * q.LJ * q.G) * ((1792 * (q.Γ * q.Lh + 2 * q.LJ * q.G) / q.μ + 224 * q.Γ) * (q.σu ^ 2 + q.σv ^ 2) + q.σu * q.σv) + (2 * q.G * q.ρJ + 2 * q.LJ * q.Lh + q.Γ * q.ρh + q.G * q.LJ ^ 2) * q.σu * (14 * (q.σu ^ 2 + q.σv ^ 2) / q.Lv + q.σu ^ 2 / q.μ + q.Γ * q.G * q.σu / q.Lv) + 2 * q.LJ ^ 2 * q.σu ^ 4 / q.Lv) / q.ε ^ 2) / q.ε ^ 2 + Real.log (3 + q.Lv ^ 2 / q.μ ^ 2 + 4 * q.Lv ^ 2 * (2 * q.G * q.ρh * q.σu ^ 2 + q.μ ^ 2 * q.σu ^ 2 + 4 * q.Lv ^ 2 * q.σv ^ 2 + 8 * q.Lv * q.LJ ^ 2 * q.σu ^ 4 / q.μ) / (q.μ ^ 3 * (q.Lv * q.ε ^ 2 + 8 * (2 * q.Lh * q.σu ^ 2 + (q.Γ * q.Lh + 2 * q.LJ * q.G) * ((1792 * (q.Γ * q.Lh + 2 * q.LJ * q.G) / q.μ + 224 * q.Γ) * (q.σu ^ 2 + q.σv ^ 2) + q.σu * q.σv) + (2 * q.G * q.ρJ + 2 * q.LJ * q.Lh + q.Γ * q.ρh + q.G * q.LJ ^ 2) * q.σu * (14 * (q.σu ^ 2 + q.σv ^ 2) / q.Lv + q.σu ^ 2 / q.μ + q.Γ * q.G * q.σu / q.Lv) + 2 * q.LJ ^ 2 * q.σu ^ 4 / q.Lv)))) ^ 2 * (16 * q.Lv / q.μ + 512 * (2 * q.G * q.ρh * q.σu ^ 2 + q.μ ^ 2 * q.σu ^ 2 + 4 * q.Lv ^ 2 * q.σv ^ 2 + 8 * q.Lv * q.LJ ^ 2 * q.σu ^ 4 / q.μ) / (q.μ ^ 2 * q.ε ^ 2)) + 1⌉₊

theorem result : Convergence LongTails.Setups.RiverValleyHillNoise.spec budget :=
  convergence_of_le (fun q => budget q 0) budget_ge

end OracleTemplate.RiverValley
