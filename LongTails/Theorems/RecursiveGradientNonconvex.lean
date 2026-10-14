import LongTails.Setups.FiniteSumSmoothNonconvex
import LongTails.Proofs.Execution
import LongTails.Proofs.RecursiveGradientAccuracy
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.NonconvexFiniteSum

open LongTails.Setups.FiniteSumSmoothNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 5 * p.n + ⌈20 * Real.sqrt (p.n : ℝ) * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.FiniteSumSmoothNonconvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨tunedRecursiveGradient, ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hΔ, hε⟩

  rintro f oracle ⟨hg, ho, hmean, lower, hlower, hgap⟩
  let b := Nat.sqrt p.n + 1
  let S := max 1 ⌈4 * p.L * p.Δ / ((b : ℝ) * p.ε ^ 2)⌉₊
  let η := 1 / (2 * p.L)
  let K := 5 * p.n + ⌈20 * Real.sqrt (p.n : ℝ) * p.L * p.Δ / p.ε ^ 2⌉₊
  have hK : (2 * b * (b - 1) + 1 * p.n) * S ≤ K := by
    simpa only [one_mul, Nat.add_comm] using recursive_budget_bound (n := p.n) hL hΔ hε
  have hb : 0 < b := Nat.succ_pos _
  have : NeZero S := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))⟩
  let g : Fin p.n × p.E → p.E := fun z => gradient (f z.1) z.2
  let out := fun seed : RecursiveSeeds p.n b (b - 1) S =>
    (recursiveEpochs g η b p.x0
      (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed.1 s j))))).2.getD seed.2.val p.x0
  have hanswer : ∀ k z seed, oracle.answer k (0, z) seed = g z :=
    fun k z seed => (ho k seed z.1 z.2).unique (hg z.1 z.2)
  have hgrad : ∀ x, gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) x = FiniteSum.fullGradient g x :=
    fun x => (FiniteSum.objective_gradient hg x).gradient
  have hrate := recursiveGradient_rate (g := g) hL hb (FiniteSum.objective_gradient hg)
    hmean (b - 1) (Nat.sub_le _ _) S p.x0 lower hlower hgap
  simp only [execute_recursiveGradient] at hrate
  have hlen : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have heps : 4 * p.L * p.Δ / (((b - 1 + 1) * S : ℕ) : ℝ) ≤ p.ε ^ 2 := by
    simpa only [hlen, Nat.cast_mul] using recursive_budget_accuracy hε b hb
  have hgood : (𝔼 seed : RecursiveSeeds p.n b (b - 1) S,
      ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (out seed)‖ ^ 2) ≤ p.ε ^ 2 := by
    simp only [hgrad]
    exact hrate.trans heps
  have hexec (seed : RecursiveSeeds p.n b (b - 1) S)
      (ξ : (k : ℕ) → oracle.Seed k) :
      execute oracle (recursiveGradient η b (b - 1) S p.x0) (fun _ => K) seed ξ = out seed := by
    erw [execute_eq_of_answer_eq oracle g hanswer]
    unfold recursiveGradient
    erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ g _ hK,
      QueryPlan.eval_map, eval_allEpochsPlan]
  change spec.successful p f
      (fun seed => (execute oracle (recursiveGradient η b (b - 1) S p.x0) (fun _ => K) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (RecursiveSeeds p.n b (b - 1) S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : RecursiveSeeds p.n b (b - 1) S × ((k : ℕ) → oracle.Seed k) =>
    out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : RecursiveSeeds p.n b (b - 1) S =>
        ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (out seed)‖ ^ 2)
        (μ := (PMF.uniformOfFintype (RecursiveSeeds p.n b (b - 1) S)).toMeasure))
  · change (∫ seed : RecursiveSeeds p.n b (b - 1) S × ((k : ℕ) → oracle.Seed k),
        ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (out seed.1)‖ ^ 2
        ∂(PMF.uniformOfFintype (RecursiveSeeds p.n b (b - 1) S)).toMeasure.prod
          (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ p.ε ^ 2
    rw [integral_fun_fst (fun seed => ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (out seed)‖ ^ 2)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact hgood

end OracleTemplate.NonconvexFiniteSum
