import LongTails.Setups.EllSmoothNonconvex

open OracleTemplate

namespace LongTails.Setups.HighDimensionalEllSmoothNonconvex

open LongTails.Setups.EllSmoothNonconvex

abbrev spec : Setup := { EllSmoothNonconvex.spec with
  valid := fun (p : EllSmoothNonconvex.Params) => EllSmoothNonconvex.spec.valid p ∧ p.ρ < 2 ∧ 0 < p.ℓ 0 ∧
    2 ^ 27 * p.ε ^ 2 ≤ (2 - p.ρ) * p.Δ * p.ℓ p.ε ∧
    2 ^ 56 * ((⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊ : ℝ) + 1) ^ 6 *
      (p.ℓ p.ε / p.ℓ 0) ^ 4 ≤ p.d }

end LongTails.Setups.HighDimensionalEllSmoothNonconvex
