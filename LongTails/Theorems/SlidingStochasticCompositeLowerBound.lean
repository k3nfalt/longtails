import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalSlidingStochasticComposite
import LongTails.Proofs.SlidingLowerBoundMain

namespace LongTails.Theorems.SlidingStochasticCompositeLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalSlidingStochasticComposite.spec;
    S.Params → Fin S.numOracles → ℕ) := fun q i =>
  let X := q.ℓ * q.Δ / q.ε ^ 2
  let H := X * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ))
  if i = q.c then (if i = 0 then ⌊X / 2 ^ 60⌋₊ else ⌊H / 2 ^ 60⌋₊) else q.K

theorem result :
    NonConvergence LongTails.Setups.HighDimensionalSlidingStochasticComposite.spec budget := by
  intro q hq A _ b hb
  have h0 := hb 0
  have h1 := hb 1
  rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) q.c with hc | hc
  · simp only [budget, hc, ite_true, ite_false,
      show (1 : Fin 2) ≠ 0 by decide] at h0 h1
    exact LongTails.Proofs.SlidingLowerBoundMain.failure_f q hq A b h0 h1
  · simp only [budget, hc, ite_true, ite_false,
      show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide] at h0 h1
    by_cases hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)
    · exact LongTails.Proofs.SlidingLowerBoundMain.failure_hB q hq A b hB h0 h1
    · push Not at hB
      exact LongTails.Proofs.SlidingLowerBoundMain.failure_hA q hq A b hB h0 h1

end LongTails.Theorems.SlidingStochasticCompositeLowerBound
