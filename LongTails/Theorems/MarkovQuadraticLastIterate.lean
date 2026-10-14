import LongTails.Setups.MarkovQuadraticInterpolation
import LongTails.Proofs.Execution
import LongTails.Proofs.MarkovQuadraticRisk

open MeasureTheory

namespace OracleTemplate.MarkovQuadratic

open LongTails.Setups.MarkovQuadraticInterpolation

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈10000000000000000 * q.L * q.R ^ 2 / (q.α * q.ε)⌉₊ + 1

theorem result : Convergence LongTails.Setups.MarkovQuadraticInterpolation.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => lastSgd (q.α / (10000 * q.L)) q.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hR, hα, hα1, hε⟩
  intro K hK
  rintro f O ⟨m, π, μ, κ, hκ, H, u, model, rfl⟩
  have := hκ
  let η := q.α / (10000 * q.L)
  let P := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ
  let output := fun ξ : ℕ → Fin m => iterate (fun x i => H i (x - u)) η q.x0 ξ K
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηL : η * q.L ≤ 2 := by
    have he : η * q.L = q.α / 10000 := by dsimp [η]; field_simp
    rw [he]
    linarith
  have hm : Measurable output := measurable_iterate _ (sample_gradient_measurable H u) η q.x0 K
  have hi : Integrable (fun ξ => f (output ξ) - f u) (P : Measure (ℕ → Fin m)) :=
    model.integrable_iterate_gap hL hη hηL _ K
  have ha : (∫ ξ, f (output ξ) - f u ∂(P : Measure (ℕ → Fin m))) ≤ q.ε :=
    model.iterate_accuracy μ hL hα hα1 hε K hK
  let result := fun seed : Unit × (ℕ → Fin m) =>
    (execute { Seed := fun _ => Fin m, law := P, answer := fun _ (_, x) i => H i (x - u) }
      (lastSgd η q.x0) (fun _ => K) seed.1 seed.2)
  change Measurable result ∧ ∃ u, IsMinOn f Set.univ u ∧
    Integrable (fun seed => f (result seed) - f u) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed, f (result seed) - f u ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε
  have he : result = fun seed => output seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_lastSgd P (fun x i => H i (x - u)) η q.x0 K ξ)
  rw [he]
  refine ⟨hm.comp measurable_snd, u, model.minimizer, ?_, ?_⟩
  · change Integrable (fun seed : Unit × (ℕ → Fin m) => f (output seed.2) - f u)
      ((Measure.dirac ()).prod (P : Measure (ℕ → Fin m)))
    exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → Fin m)))).integrable_comp_of_integrable hi
  · change (∫ seed : Unit × (ℕ → Fin m), f (output seed.2) - f u
      ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε
    rw [integral_fun_snd (fun ξ : ℕ → Fin m => f (output ξ) - f u)]
    simpa using ha

end OracleTemplate.MarkovQuadratic
