import LongTails.Setups.CoordinateSmoothStronglyConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedCoordinateAccuracy
import LongTails.Proofs.SvrgConvex
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * (∑ i : Fin p.d, max 1 ⌈Real.sqrt (p.L i / p.μ)⌉₊) * Nat.clog 2 ⌈2 * p.Δ / p.ε⌉₊

theorem result : Convergence LongTails.Setups.CoordinateSmoothStronglyConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => acceleratedCoordinate p (budget p 0), ?_, fun _ _ => trivial⟩
  rintro p ⟨hμ, hL, hΔ, hε⟩

  rintro f oracle ⟨hg, ho, hmodel, hs, u, hmin, hgap⟩
  let K := 2 * totalWeight p * Nat.clog 2 ⌈2 * p.Δ / p.ε⌉₊
  let g : Fin p.d × EuclideanSpace ℝ (Fin p.d) → ℝ := fun q => gradient f q.2 q.1
  let out := fun seed : Seeds p K => (run p g (p.x0, p.x0) (List.ofFn seed)).1
  have hanswer : ∀ k q seed, oracle.answer k (0, q) seed = g q :=
    fun k q seed => ho k seed q.1 q.2
  have hgood : (𝔼 seed : Seeds p K, (f (out seed) - f u)) ≤ p.ε :=
    (run_rate p hμ hL hg hmodel hs u hmin hgap K).trans
      (coordinate_budget_accuracy p hμ hΔ hε)
  have hexec (seed : Seeds p K) (ξ : (k : ℕ) → oracle.Seed k) :
      execute oracle (acceleratedCoordinate p K) (fun _ => K) seed ξ = out seed := by
    erw [execute_eq_of_answer_eq oracle g hanswer, execute_acceleratedCoordinate (g := g)]
  change spec.successful p f
      (fun seed => (execute oracle (acceleratedCoordinate p K) (fun _ => K) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (Seeds p K)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : Seeds p K × ((k : ℕ) → oracle.Seed k) => out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, u, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Seeds p K => f (out seed) - f u)
        (μ := (PMF.uniformOfFintype (Seeds p K)).toMeasure))
  · change (∫ seed : Seeds p K × ((k : ℕ) → oracle.Seed k), f (out seed.1) - f u
        ∂(PMF.uniformOfFintype (Seeds p K)).toMeasure.prod
          (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => f (out seed) - f u)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact hgood

end OracleTemplate.AcceleratedCoordinate
