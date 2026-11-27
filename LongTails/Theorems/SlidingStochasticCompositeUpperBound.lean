import LongTails.Setups.SlidingStochasticComposite
import LongTails.Proofs.SlidingCompositeAssembly

namespace LongTails.Theorems.SlidingStochasticCompositeUpperBound

open OracleTemplate OracleTemplate.SlidingStochasticComposite

noncomputable def budget : (let S := LongTails.Setups.SlidingStochasticComposite.spec;
    S.Params → Fin S.numOracles → ℕ) := fun p i =>
  let M := ⌈32 * p.ℓ * p.Δ / p.ε ^ 2⌉₊ + 1
  let N := ⌈4 * Real.sqrt (1 + p.L / p.ℓ) + 256 * p.σ ^ 2 / p.ε ^ 2⌉₊
  if i = 0 then M else M * N

theorem result : Convergence LongTails.Setups.SlidingStochasticComposite.spec budget := by
  refine ⟨fun p =>
    let K := ⌈32 * p.ℓ * p.Δ / p.ε ^ 2⌉₊
    let N := ⌈4 * Real.sqrt (1 + p.L / p.ℓ) + 256 * p.σ ^ 2 / p.ε ^ 2⌉₊
    method p.ℓ (p.ℓ * N * (N + 1) / 8) N K p.x0, ?_, fun _ _ => trivial⟩
  intro p hp I O hadm
  exact LongTails.Proofs.SlidingCompositeAssembly.successful_execution p hp I O hadm

end LongTails.Theorems.SlidingStochasticCompositeUpperBound
