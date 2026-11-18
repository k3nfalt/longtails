import LongTails.Setups.HighDimensionalStrongQuasar
import LongTails.Proofs.StrongQuasarChainUpper

open MeasureTheory

namespace LongTails.Theorems.HighDimensionalStrongQuasarUpperBound

open OracleTemplate OracleTemplate.RelativeQuasar LongTails.Proofs.StrongQuasarChainUpper

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStrongQuasar.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈32 * Real.sqrt (p.L / p.μ) / p.γ⌉₊ * Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊

theorem result : Convergence LongTails.Setups.HighDimensionalStrongQuasar.spec budget := by
  apply convergence_of_public_budget (S := LongTails.Setups.HighDimensionalStrongQuasar.spec)
    (fun p => budget p 0)
  refine ⟨fun p => accelerated p.toRelative, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  have hv := valid_relative hp
  obtain ⟨hg, hlip, ⟨g, hm, hans, herr⟩, u, hmin, hgap, hquasar⟩ := ho
  obtain ⟨hi, ha⟩ := run_accuracy p.toRelative f g hv hm hg hlip herr u hmin hgap hquasar
  have hK : budget p 0 = calls p.toRelative := (calls_eq hp).symm
  have he (seed : (accelerated p.toRelative).Seed) (ξ : (k : ℕ) → O.Seed k) :
      execute O (accelerated p.toRelative) (fun _ => budget p 0) seed ξ =
        (run p.toRelative g (calls p.toRelative) (p.x0, p.x0) seed).1 := by
    rw [hK, execute_eq_of_answer_eq O g hans]
    exact execute_accelerated p.toRelative g seed
  change LongTails.Setups.HighDimensionalStrongQuasar.spec.successful p f
    (fun seed : (accelerated p.toRelative).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (accelerated p.toRelative) (fun _ => budget p 0) seed.1 seed.2) _
  refine ⟨u, hmin, ?_, ?_⟩
  · simp only [he]
    exact hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k))
  · simp only [he]
    change (∫ ω : (Fin (calls p.toRelative) → ℝ) × ((k : ℕ) → O.Seed k),
      f (run p.toRelative g (calls p.toRelative) (p.x0, p.x0) ω.1).1 - f u
      ∂(samplesLaw (calls p.toRelative) : Measure _).prod
        (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_prod _ (hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k)))]
    simpa using ha

end LongTails.Theorems.HighDimensionalStrongQuasarUpperBound
