import LongTails.Algorithms.QuarticMetricStage
import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Setups.ThirdDerivativeSmoothNonconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.LazyQuarticMetric

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open QuarticMetricStage

noncomputable section

def beta (p : Params) : ℝ := Real.sqrt (p.L₃ * p.Δ)
def alpha (p : Params) : ℝ := min (beta p / 2 ^ 24) ((p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ))
def condition (p : Params) : ℝ := beta p / alpha p
def radius (p : Params) : ℝ := Real.sqrt p.Δ / 256
def decrease (p : Params) : ℝ := alpha p ^ 2 / (3072 * p.L₃)
def logarithmArgument (p : Params) : ℝ := 2 + p.H₀ * p.Δ / p.ε ^ 2 + p.L₃ * p.Δ ^ 3 / p.ε ^ 4
def innerSteps (p : Params) : ℕ := ⌈2 ^ 11 * Real.sqrt (condition p) * Real.log (logarithmArgument p)⌉₊
def stages (p : Params) : ℕ := ⌈3072 * condition p ^ 2⌉₊ + 1

structure State (p : Params) where
  point : Point p.E
  snapshot : p.E
  coordinates : p.E ≃L[ℝ] p.E

def readHessian (p : Params) : Reply p.E → (p.E →L[ℝ] p.E)
  | .inr H => H
  | .inl _ => 0

def coordinates (p : Params) (H : p.E →L[ℝ] p.E) : p.E ≃L[ℝ] p.E :=
  HessianSnapshot.coordinates (H + (8 * beta p) • ContinuousLinearMap.id ℝ p.E)

def parameters (p : Params) (st : State p) : Parameters p.E where
  S := st.coordinates
  center := st.point
  α := alpha p
  μ := alpha p / (64 * beta p)
  L := 4
  a := Real.sqrt (alpha p / (256 * beta p))
  r := radius p
  q := decrease p
  η := Real.sqrt (alpha p / (16 * p.L₃))
  ε := p.ε

def refresh (p : Params) (st : State p) : Plan p.E (State p) 1 := by
  classical
  exact if p.ε < ‖st.point.gradient‖ ∧
      radius p / 4 < ‖st.coordinates (st.point.x - st.snapshot)‖ then
    .ask (1, st.point.x) fun reply => .done ⟨st.point, st.point.x, coordinates p (readHessian p reply)⟩
  else .ask (0, st.point.x) fun _ => .done st

def step (p : Params) (st : State p) : Plan p.E (State p) (2 * innerSteps p + 8) := by
  classical
  exact (show (2 * innerSteps p + 7) + 1 = 2 * innerSteps p + 8 by omega) ▸
    (refresh p st).bind (fun fresh =>
      if p.ε < ‖fresh.point.gradient‖ then
        (QuarticMetricStage.plan (parameters p fresh) (innerSteps p)).map
          (fun point => { fresh with point := point })
      else
        (Nat.one_mul (2 * innerSteps p + 7)) ▸
          (QueryPlan.traverse (2 * innerSteps p + 7) (fun _ =>
            QueryPlan.ask ((0 : Fin 2), fresh.point.x) fun (_ : Reply p.E) => .done ())).map (fun _ => fresh))

def loop (p : Params) : (t : ℕ) → State p → Plan p.E (State p) ((2 * innerSteps p + 8) * t)
  | 0, st => .done st
  | t + 1, st => by
    simpa only [Nat.mul_succ] using (step p st).bind (loop p t)

def plan (p : Params) : Plan p.E p.E ((2 * innerSteps p + 8) * stages p + 2) :=
  .ask (0, p.x0) fun reply =>
    let point := readPoint p.x0 reply
    .ask (1, p.x0) fun reply =>
      (loop p (stages p) ⟨point, p.x0, coordinates p (readHessian p reply)⟩).map (fun st => st.point.x)

def algorithm (p : Params) : Algorithm p.E (Reply p.E) p.E 2 :=
  EnergyHessianReuse.channelAlgorithm (0, p.x0) p.x0 (plan p)

end

end LongTails.Algorithms.LazyQuarticMetric
