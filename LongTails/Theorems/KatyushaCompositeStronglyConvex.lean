import LongTails.Setups.CompositeFiniteSumStronglyConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.KatyushaConvergence
import LongTails.Proofs.KatyushaAccuracy
import LongTails.Proofs.KatyushaExecution
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 108 * (p.n + ⌈Real.sqrt ((p.n : ℝ) * p.L / p.μ)⌉₊) * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊

theorem result : Convergence LongTails.Setups.CompositeFiniteSumStronglyConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => katyusha p (12 * tuning p * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊), ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hμ, hΔ, hε⟩

  rintro inst oracle ⟨hc, hg, hlip, hψ, hp, ho, hprox, u, hu, hgap⟩
  let S := 12 * tuning p * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊
  let K := 108 * (p.n + ⌈Real.sqrt ((p.n : ℝ) * p.L / p.μ)⌉₊) * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊
  have hK : (4 * (2 * p.n) + 1 * p.n) * S ≤ K := by
    calc
      _ = 108 * (p.n * tuning p) * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊ := by dsimp [S]; ring
      _ ≤ K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (tuning_cost_bound p hL hμ))
  let g : Fin p.n × p.E → p.E := fun q => gradient (inst.components q.1) q.2
  let out := fun seed : Seeds p S =>
    (run (tau p) (alpha p) p.L (theta p) (2 * p.n) g inst.prox S
      ⟨p.x0, p.x0, p.x0⟩ seed).snapshot
  have hanswer : ∀ k q seed, oracle.answer k (0, q) seed = answer p g inst.prox q := by
    intro k q seed
    cases q with
    | gradient i x => exact ho k seed i x
    | prox a z v => exact hprox k seed a z v
  have hgood : (𝔼 seed : Seeds p S, (objective p inst (out seed) - objective p inst u)) ≤ p.ε := by
    have hr := run_rate p hL hμ hΔ inst.components inst.regularizer g inst.prox
      hc hg hlip hψ hp u hu hgap S
    have hb := katyusha_budget_accuracy p hL hμ hε
    have hθ : 0 < theta p := by
      have hα := (tuning_bounds p hL hμ).2.2.1
      unfold theta
      positivity
    apply (mul_le_mul_iff_right₀ (pow_pos hθ (2 * p.n * S))).mp
    exact hr.trans hb
  have hexec (seed : Seeds p S) (ξ : (k : ℕ) → oracle.Seed k) :
      execute oracle (katyusha p S) (fun _ => K) seed ξ = out seed := by
    erw [execute_eq_of_answer_eq oracle (answer p g inst.prox) hanswer]
    unfold katyusha
    erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hK,
      QueryPlan.eval_map, eval_allPlan]
  change spec.successful p inst
      (fun seed => (execute oracle (katyusha p S) (fun _ => K) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (Seeds p S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : Seeds p S × ((k : ℕ) → oracle.Seed k) => out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, u, hu, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Seeds p S => objective p inst (out seed) - objective p inst u)
        (μ := (PMF.uniformOfFintype (Seeds p S)).toMeasure))
  · change (∫ seed : Seeds p S × ((k : ℕ) → oracle.Seed k),
        objective p inst (out seed.1) - objective p inst u
        ∂(PMF.uniformOfFintype (Seeds p S)).toMeasure.prod
          (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => objective p inst (out seed) - objective p inst u)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact hgood

end OracleTemplate.Katyusha
