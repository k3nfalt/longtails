import LongTails.Setups.RelativeGradientStrongQuasar
import LongTails.Proofs.RelativeQuasarConvergence

open MeasureTheory

namespace OracleTemplate.RelativeQuasar

open LongTails.Setups.RelativeGradientStrongQuasar

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈32 * Real.sqrt (p.L / (p.μ * (1 - p.δ))) / p.γ + 128 * p.δ ^ 2 * p.L / (p.γ ^ 2 * p.μ * (1 - p.δ))⌉₊ * max 1 (Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊)

theorem result : Convergence LongTails.Setups.RelativeGradientStrongQuasar.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨accelerated, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  obtain ⟨hg, hlip, ⟨g, hm, hans, herr⟩, u, hmin, hgap, hquasar⟩ := ho
  obtain ⟨hi, ha⟩ := run_accuracy p f g hp hm hg hlip herr u hmin hgap hquasar
  have hK : budget p 0 = calls p := rfl
  have he (seed : (accelerated p).Seed) (ξ : (k : ℕ) → O.Seed k) :
      output p O (seed, ξ) = (run p g (calls p) (p.x0, p.x0) seed).1 := by
    unfold output
    rw [execute_eq_of_answer_eq O g hans, execute_accelerated]
  change spec.successful p f (output p O) _
  refine ⟨u, hmin, ?_, ?_⟩
  · simp only [he]
    exact hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k))
  · simp only [he]
    change (∫ ω : (Fin (calls p) → ℝ) × ((k : ℕ) → O.Seed k),
      f (run p g (calls p) (p.x0, p.x0) ω.1).1 - f u
      ∂(samplesLaw (calls p) : Measure _).prod (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_prod _ (hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k)))]
    simpa using ha

end OracleTemplate.RelativeQuasar
