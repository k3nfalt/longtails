import LongTails.Setups.AffineVarianceMeanSquaredSmooth
import LongTails.Proofs.RecursiveMomentumGapBatch

namespace OracleTemplate.RecursiveMomentumGapBatch

open LongTails.Setups.AffineVarianceMeanSquaredSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let S := q.L + q.Lbar
  let D := S * q.Δ / q.ε ^ 2
  let z := q.Λ / q.ε
  let r := 1 + 3 * q.Γ + 6 * z
  ⌈8 * z ^ 2 + 64 * q.Γ * D⌉₊ + 1 + ⌈20 * r * D⌉₊

theorem result : Convergence LongTails.Setups.AffineVarianceMeanSquaredSmooth.spec budget :=
  convergence

end OracleTemplate.RecursiveMomentumGapBatch
