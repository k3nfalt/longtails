import LongTails.Algorithms.JointHessianStationarity
import LongTails.Proofs.EnergyHessianConvergence
import LongTails.Proofs.RelativeHessianTuning

namespace LongTails.Proofs.JointHessianStationarity

open OracleTemplate MeasureTheory LongTails.Setups.PointwiseHessianStationarity
open LongTails.Algorithms.JointHessianStationarity

lemma parameters_valid {p : Params} (hp : broadSpec.valid p) :
    LongTails.Setups.GradientDependentHessian.spec.valid (parameters p) := by
  exact ⟨RelativeHessianTuning.curvature_pos hp, hp.2.1, hp.2.2.2.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2, le_rfl⟩

lemma eval_joint (p : Params) (f : Point p → ℝ) {U : Type} {k : ℕ}
    (q : QueryPlan (Fin 2 × Point p) (LongTails.Algorithms.EnergyHessianReuse.Reply (parameters p)) U k) :
    QueryPlan.eval (fun x => (f x, gradient f x, fderiv ℝ (gradient f) x)) (jointPlan p q) =
      QueryPlan.eval (EnergyHessianExecution.replies (parameters p) f) q := by
  induction q with
  | done value => rfl
  | ask q next ih => exact ih _

lemma output_accuracy {p : Params} (hp : broadSpec.valid p) (f : Point p → ℝ)
    (O : Oracle (Point p) (Reply p)) (hf : broadSpec.admissible p f O) :
    ‖gradient f (output p f)‖ ≤ p.ε := by
  unfold output plan
  erw [eval_joint]
  apply EnergyHessianConvergence.plan_accuracy (parameters p) f (parameters_valid hp) hf.1
  · intro x
    exact (hf.2.1 x).trans (show p.L₀ + p.L₁ * ‖gradient f x‖ ≤
      p.L₀ + p.L₁ * p.ε + p.L₁ * ‖gradient f x‖ from by
        linarith [mul_nonneg hp.2.1 hp.2.2.2.2.2.le])
  · exact hf.2.2.1
  · exact hf.2.2.2.1

lemma execution {p : Params} (f : Point p → ℝ) (O : Oracle (Point p) (Reply p))
    (hf : broadSpec.admissible p f O) (K : ℕ) (hK : count p ≤ K)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) seed ξ = output p f := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun _ q => (f q.2, gradient f q.2, fderiv ℝ (gradient f) q.2)) (fun history q => by
      have hq : q.1 = 0 := Subsingleton.elim _ _
      simpa only [← hq] using hf.2.2.2.2 history (ξ history.length) q.2)]
  change QueryPlan.output 0 (StochasticGradient.advance
    (fun _ s => QueryPlan.update s ((fun x => (f x, gradient f x, fderiv ℝ (gradient f) x))
      (QueryPlan.query 0 s))) K 0 ⟨count p, plan p⟩) = _
  erw [QueryPlan.advance_plan_of_le (fun x => (f x, gradient f x, fderiv ℝ (gradient f) x)) 0 (plan p) hK 0]
  rfl

lemma success {p : Params} (hp : broadSpec.valid p) (f : Point p → ℝ)
    (O : Oracle (Point p) (Reply p)) (hf : broadSpec.admissible p f O)
    (K : ℕ) (hK : count p ≤ K) :
    broadSpec.successful p f (fun ω : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => K) ω.1 ω.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let P : ProbabilityMeasure ((algorithm p).Seed × ((k : ℕ) → O.Seed k)) :=
    ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩
  change broadSpec.successful p f _ P
  let : IsProbabilityMeasure (P : Measure ((algorithm p).Seed × ((k : ℕ) → O.Seed k))) := P.prop
  simp only [execution f O hf K hK]
  refine ⟨measurable_const, integrable_const _, ?_⟩
  simpa using output_accuracy hp f O hf

end LongTails.Proofs.JointHessianStationarity
