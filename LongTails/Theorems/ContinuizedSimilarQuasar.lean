import LongTails.Setups.ContinuizedSimilarQuasar
import LongTails.Proofs.Execution
import LongTails.Proofs.ContinuizedQuasarConvergence
import LongTails.Proofs.ContinuizedQuasarExecution

open MeasureTheory

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (p.n + max 1 ⌈8 * Real.sqrt (p.L / p.μ) / p.γ + 4096 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)⌉₊) * max 1 (Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊)

theorem result : Convergence LongTails.Setups.ContinuizedSimilarQuasar.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨accelerated, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  obtain ⟨u, hmin, hi, ha⟩ := run_accuracy p f O hp ho
  have hK : budget p 0 = (epochLength p + p.n) * epochs p := by
    unfold budget epochLength epochs
    rw [Nat.add_comm p.n]
  let g : Fin p.n × p.E → p.E := fun ix => gradient (f ix.1) ix.2
  have he (seed : (accelerated p).Seed) (ξ : (k : ℕ) → O.Seed k) :
      execute O (accelerated p) (fun _ => (budget p 0)) seed ξ =
        (run p g (epochs p) (p.x0, p.x0) seed).1 := by
    rw [hK, execute_eq_of_answer_eq O g (fun k ix ξ => ho.2.1 k ix.1 ix.2 ξ),
      execute_accelerated (g := g)]
  refine ⟨u, hmin, ?_, ?_⟩
  · simp only [he]
    exact hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k))
  · simp only [he]
    change (∫ ω : (Fin (epochs p) → Fin (epochLength p) → ℝ × Fin p.n) × ((k : ℕ) → O.Seed k),
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f (run p g (epochs p) (p.x0, p.x0) ω.1).1 - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u
      ∂(samplesLaw p.n (epochLength p) (epochs p) : Measure _).prod
        (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_prod _ (hi.comp_fst (O.law : Measure ((k : ℕ) → O.Seed k)))]
    simpa using ha

end OracleTemplate.ContinuizedSimilarQuasar
