import LongTails.Setups.FiniteSumThirdSmoothConvex
import LongTails.Proofs.HessianOnlyFiniteSumConvergence

namespace LongTails.Theorems.HessianOnlyFiniteSumThirdSmooth

open LongTails.Setups.FiniteSumThirdSmoothConvex
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)
open LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth
open LongTails.Proofs.HessianOnlyFiniteSumTuning LongTails.Proofs.HessianOnlyFiniteSumConvergence
open OracleTemplate MeasureTheory

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 ^ 38 * (p.n + ⌈((p.n : ℝ) ^ 4 * p.L * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ)⌉₊) * (1 + ⌈Real.log (2 + p.n + p.G * p.R / p.ε + p.H * p.R ^ 2 / p.ε + p.L * p.R ^ 4 / p.ε)⌉₊) ^ 2

theorem result : Convergence LongTails.Setups.FiniteSumThirdSmoothConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp F oracle h
  rcases h with ⟨hf, hc, hT, hmin, hx0, hG, hH, horacle⟩
  let g := fun q : Fin p.n × p.E => (gradient (F.component q.1) q.2, fderiv ℝ (gradient (F.component q.1)) q.2)
  have hanswer : ∀ history q seed, oracle.answer history (0, q) seed = g q :=
    fun history q seed => horacle history seed q.1 q.2
  have hcost : calls p ≤ budget p 0 := calls_bound p hp
  have hexec (seed : Seeds p) (oracleSeed : (k : ℕ) → oracle.Seed k) :
      execute oracle (algorithm p) (fun _ => budget p 0) seed oracleSeed = QueryPlan.eval g (plan p seed) := by
    erw [execute_eq_of_answer_eq oracle g hanswer]
    exact QueryPlan.execute_plan_of_le ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩
      (0, p.x0) p.x0 (calls p) (budget p 0) (plan p) g seed hcost
  change spec.successful p F
    (fun seed => execute oracle (algorithm p) (fun _ => budget p 0) seed.1 seed.2)
    ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure.prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : Seeds p × ((k : ℕ) → oracle.Seed k) => QueryPlan.eval g (plan p seed.1)) ∧ _
  refine ⟨(measurable_from_top : Measurable (fun seed : Seeds p => QueryPlan.eval g (plan p seed))).comp measurable_fst, ?_⟩
  have hfailure := plan_failure p hp F hf hc hT (fun x => hmin (Set.mem_univ x)) hx0 hG hH
  have hprob := LongTails.Proofs.AcceleratedQuarticProbability.uniform_success
    (fun seed : Seeds p => objective F.component (QueryPlan.eval g (plan p seed)) - objective F.component F.xstar ≤ p.ε) hfailure
  have he : {seed : Seeds p × ((k : ℕ) → oracle.Seed k) |
      objective F.component (QueryPlan.eval g (plan p seed.1)) - objective F.component F.xstar ≤ p.ε} =
      {seed : Seeds p | objective F.component (QueryPlan.eval g (plan p seed)) - objective F.component F.xstar ≤ p.ε} ×ˢ Set.univ := by
    ext seed
    simp
  change (2 / 3 : ENNReal) ≤ ((PMF.uniformOfFintype (Seeds p)).toMeasure.prod
    (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) _
  rw [he, Measure.prod_prod, measure_univ, mul_one]
  exact hprob

end LongTails.Theorems.HessianOnlyFiniteSumThirdSmooth
