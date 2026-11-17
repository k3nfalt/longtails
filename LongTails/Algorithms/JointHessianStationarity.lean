import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Setups.PointwiseHessianStationarity

namespace LongTails.Algorithms.JointHessianStationarity

open OracleTemplate LongTails.Setups.PointwiseHessianStationarity

noncomputable def parameters (p : Params) : LongTails.Setups.GradientDependentHessian.Params where
  E := Point p
  x0 := 0
  L₀ := p.L₀ + p.L₁ * p.ε
  L₁ := p.L₁
  Δ := p.Δ
  G₀ := p.G
  ε := p.ε
  m := 1

noncomputable def jointPlan (p : Params) {U : Type} : {k : ℕ} →
    QueryPlan (Fin 2 × Point p) (EnergyHessianReuse.Reply (parameters p)) U k →
    QueryPlan (Point p) (Reply p) U k
  | _, .done value => .done value
  | _, .ask q next => .ask q.2 (fun reply => jointPlan p
      (next (if q.1 = 0 then Sum.inl reply.2.1 else Sum.inr reply.2.2)))

noncomputable def count (p : Params) : ℕ :=
  4 * EnergyHessianReuse.blockCount (parameters p) + 2 * EnergyHessianReuse.burnCount (parameters p) + 1

noncomputable def plan (p : Params) : QueryPlan (Point p) (Reply p) (Point p) (count p) :=
  jointPlan p (EnergyHessianReuse.plan (parameters p))

noncomputable def algorithm (p : Params) : Algorithm (Point p) (Reply p) (Point p) :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ 0 0 (count p) (fun _ => plan p)

noncomputable def output (p : Params) (f : Point p → ℝ) : Point p :=
  QueryPlan.eval (fun x => (f x, gradient f x, fderiv ℝ (gradient f) x)) (plan p)

end LongTails.Algorithms.JointHessianStationarity
