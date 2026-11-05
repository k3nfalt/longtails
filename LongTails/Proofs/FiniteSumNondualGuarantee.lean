import LongTails.Proofs.FiniteSumNondualPlan
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualGuarantee

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open OracleTemplate
open OracleTemplate.ComponentEnvelope (Program)
open FiniteSumNondualPlan FiniteSumNondualDomain FiniteSumNondualExecution

lemma successful_execution (p : Params) (hp : spec.valid p) (f : Fin p.n → Point p → ℝ)
    (O : Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O)
    (K : ℕ) (hK : 1099511627776 * p.n * rootSize p * logSize p ^ 4 ≤ K) :
    spec.successful p f (fun seed : Seeds p × ((k : ℕ) → O.Seed k) => runOutput p O K seed.1 seed.2)
      ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure.prod (O.law : Measure _), inferInstance⟩ := by
  let g : Fin p.n × Point p → Point p := fun q => gradient (f q.1) q.2
  let out : Seeds p → Feasible p := fun seed => feasiblePoint p (Program.eval g (plan p seed))
  have hout (seed : Seeds p) : (out seed).val = Program.eval g (plan p seed) :=
    feasiblePoint_val p _ (FiniteSumNondualProxFeasibility.checked_eval (plan_checked p seed) g)
  have hexec (seed : Seeds p) (oracleSeed : (k : ℕ) → O.Seed k) :
      runOutput p O K seed oracleSeed = out seed := by
    apply Subtype.ext
    rw [hout]
    exact execute_program p ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩ (plan p) O g
      (fun history query sample => ha.2.2.2 history sample query.1 query.2) K seed oracleSeed
      (plan_checked p seed) ((plan_cost p g seed).trans hK)
  obtain ⟨xstar, hmin⟩ := exists_minimizer p f O ha
  change Measurable _ ∧ ∃ xstar : Feasible p, IsMinOn (objective f) (domain p) xstar.val ∧ _
  simp only [hexec]
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, xstar, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Seeds p => objective f (out seed).val - objective f xstar.val)
        (μ := (PMF.uniformOfFintype (Seeds p)).toMeasure))
  · change (∫ seed : Seeds p × ((k : ℕ) → O.Seed k),
      objective f (out seed.1).val - objective f xstar.val
      ∂(PMF.uniformOfFintype (Seeds p)).toMeasure.prod (O.law : Measure _)) ≤ p.ε
    rw [integral_fun_fst (fun seed : Seeds p => objective f (out seed).val - objective f xstar.val)]
    simp only [probReal_univ, one_smul]
    rw [OracleTemplate.FiniteSum.uniform_integral]
    simp only [hout]
    simpa only [Finset.expect_sub_distrib, Fintype.expect_const] using
      (plan_expected_gap p hp f O ha xstar hmin)

lemma rootSize_explicit (p : Params) :
    rootSize p = 1 + ⌈(p.L * p.R ^ 2 / (p.n * p.ε)) ^ (1 / 3 : ℝ)⌉₊ := by
  unfold rootSize scale
  rw [div_div, mul_comm p.ε (p.n : ℝ)]

end LongTails.Proofs.FiniteSumNondualGuarantee
