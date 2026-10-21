import LongTailsOnline.Proofs.TaskAllocationInvariants
import LongTailsOnline.Proofs.TaskAllocationOracle

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma expected_regret_of_confidence {p : Params}
    {P : ProbabilityMeasure (Sample p.config.k)}
    (hP : Sampling p P) (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Ioc (0 : ℝ) 1) {r : ℝ} (hr : 0 ≤ r)
    (hgood : ∀ w, w ∉ confidenceFailure p → regret p (history p.config w p.config.T) ≤ r) :
    (∫ h, regret p h ∂(OnlineTemplate.execute (algorithm p.config)
      (environment P) p.config.T).toMeasure) ≤ r + 1 := by
  classical
  let c : ℝ := p.config.T * p.config.B
  have hi : Integrable (fun w => regret p (history p.config w p.config.T)) P.toMeasure :=
    Integrable.of_mem_Icc 0 c
      ((measurable_regret p).comp (measurable_history p.config p.config.T)).aemeasurable
      (Filter.Eventually.of_forall (fun w => regret_bounds p hμ _))
  have hb : Integrable ((confidenceFailure p).indicator (fun _ : Sample p.config.k => c))
      P.toMeasure := (integrable_const c).indicator (measurableSet_confidenceFailure p)
  have hpoint (w : Sample p.config.k) : regret p (history p.config w p.config.T) ≤
      r + (confidenceFailure p).indicator (fun _ => c) w := by
    by_cases hw : w ∈ confidenceFailure p
    · rw [Set.indicator_of_mem hw]
      exact (regret_bounds p hμ _).2.trans (by linarith)
    · rw [Set.indicator_of_notMem hw, add_zero]
      exact hgood w hw
  rw [execute_history, integral_map (measurable_history p.config p.config.T).aemeasurable
    (measurable_regret p).aestronglyMeasurable]
  calc
    _ ≤ ∫ w, r + (confidenceFailure p).indicator (fun _ => c) w ∂P.toMeasure :=
      integral_mono hi ((integrable_const r).add hb) hpoint
    _ = r + c * P.toMeasure.real (confidenceFailure p) := by
      rw [integral_add (integrable_const r) hb,
        integral_indicator_const c (measurableSet_confidenceFailure p)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    _ ≤ r + 1 := by
      have hc := confidenceFailure_cost hP hB hT (fun i => (hμ i).1.le) (fun i => (hμ i).2)
      dsimp only [c]
      nlinarith

end LongTailsOnline.Proofs.TaskAllocation
