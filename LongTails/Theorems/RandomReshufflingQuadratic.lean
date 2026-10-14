import LongTails.Setups.QuadraticFiniteSum
import LongTails.Proofs.ReshufflingAccuracy
import LongTails.Proofs.ReshufflingExecution
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace OracleTemplate.QuadraticFiniteSum

open LongTails.Setups.QuadraticFiniteSum

open QuadraticReshuffling

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * ⌈(64 * p.L / p.μ + 128 * p.L * Real.sqrt p.L * p.G / ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε) + 8 * (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ)) * Real.log (1 + p.L * p.R ^ 2 / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.QuadraticFiniteSum.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p hp

  rintro f oracle ⟨hs, hA, hcoercive, hanswer, u, hu, hR, hG⟩
  let η := stepSize p
  let K := epochCount p
  let out := fun seed : RandomReshuffling.Seeds p.n K =>
    RandomReshuffling.epochs (fun i y => f.A i y + f.b i) η
      (List.ofFn (fun k => List.ofFn (seed k))) p.x0
  have hbudget : budget p 0 = p.n * epochCount p := by rw [epochCount_formula]; rfl
  have hexec (seed : RandomReshuffling.Seeds p.n K) (ξ : (k : ℕ) → oracle.Seed k) :
      execute oracle (algorithm p) (fun _ => (budget p 0)) seed ξ = out seed := by
    erw [execute_eq_of_answer_eq oracle (fun q => f.A q.1 q.2 + f.b q.1)
      (fun k q ξ => hanswer k ξ q.1 q.2)]
    unfold algorithm
    rw [hbudget]
    exact RandomReshuffling.execute_algorithm (fun i y => f.A i y + f.b i)
      (stepSize p) (epochCount p) p.x0 seed
  change spec.successful p f
      (fun seed => (execute oracle (algorithm p) (fun _ => (budget p 0)) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (RandomReshuffling.Seeds p.n K)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : RandomReshuffling.Seeds p.n K × ((k : ℕ) → oracle.Seed k) => out seed.1) ∧ _
  have hμ : 0 < p.μ := hp.2.1
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, u,
    stationary_minimizer f hμ.le hs hcoercive hu, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : RandomReshuffling.Seeds p.n K => objective f (out seed) - objective f u)
        (μ := (PMF.uniformOfFintype (RandomReshuffling.Seeds p.n K)).toMeasure))
  · change (∫ seed : RandomReshuffling.Seeds p.n K × ((k : ℕ) → oracle.Seed k),
        objective f (out seed.1) - objective f u
        ∂(PMF.uniformOfFintype (RandomReshuffling.Seeds p.n K)).toMeasure.prod
          (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => objective f (out seed) - objective f u)]
    simp only [probReal_univ, one_smul]
    exact tuned_objective_accuracy p hp f hs hA hcoercive u hu hR hG

end OracleTemplate.QuadraticFiniteSum
