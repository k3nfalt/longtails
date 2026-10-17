import LongTails.Proofs.LazyQuarticConvergence
import LongTails.Proofs.LazyQuarticHessianBudget

namespace LongTails.Proofs.LazyQuarticBudget

open OracleTemplate.QueryPlan
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.EnergyHessianExecution (counts counts_map)
open LongTails.Proofs.LazyQuarticConvergence

lemma plan_counts (p : Params) (f : p.E → ℝ) (i : Fin 2) :
    counts (replies p f) (plan p) i =
      counts (replies p f) (loop p (stages p) (initial p f)) i + 1 := by
  simp only [plan, counts, replies_gradient, replies_hessian,
    LongTails.Algorithms.QuarticMetricStage.readPoint, readHessian, counts_map]
  change (if i = (0 : Fin 2) then 1 else 0) +
    ((if i = (1 : Fin 2) then 1 else 0) + counts (replies p f) (loop p (stages p) (initial p f)) i) = _
  fin_cases i <;> simp <;> omega

lemma ordinary_calls (p : Params) (f : p.E → ℝ) (hp : spec.valid p) :
    counts (replies p f) (plan p) 0 ≤
      ⌈2 ^ 90 * (1 + p.Δ ^ (5 / 4 : ℝ) * p.L₃ ^ (5 / 12 : ℝ) / p.ε ^ (5 / 3 : ℝ)) *
        Real.log (logarithmArgument p)⌉₊ := by
  rw [plan_counts]
  have hh := LazyQuarticExecution.loop_ordinary_calls p (replies p f) (initial p f) (stages p)
  have hb := LazyQuarticRates.ordinary_bound p hp
  omega

lemma hessian_calls (p : Params) (f : p.E → ℝ) (h : LazyQuarticTransition.Data p f) :
    counts (replies p f) (plan p) 1 ≤
      ⌈2 ^ 62 * (1 + p.Δ ^ (3 / 4 : ℝ) * p.L₃ ^ (1 / 4 : ℝ) / p.ε)⌉₊ := by
  rw [plan_counts]
  apply LazyQuarticHessianBudget.hessian_bound p h.valid
  exact LazyQuarticLedger.loop_hessian_bound p f h (replies p f) (replies_gradient p f)
    (replies_hessian p f) (initial p f) (initial_faithful p f) (initial_snapshot p f h.valid) rfl rfl

end LongTails.Proofs.LazyQuarticBudget
