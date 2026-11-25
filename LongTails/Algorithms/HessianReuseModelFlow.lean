import LongTails.Setups.GradientDependentHessian
import LongTails.Algorithms.EnergyHessianReuse
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace LongTails.Algorithms.HessianReuseModelFlow

open OracleTemplate LongTails.Setups.GradientDependentHessian

noncomputable section

def curvature (p : Params) := p.L₀ + p.L₁ * p.ε
def allowance (p : Params) := 2 * p.ε / 9
def threshold (p : Params) := 7 * p.ε / 9
def radius (p : Params) := Real.sqrt (allowance p / (p.m * curvature p))
def energyCap (p : Params) := threshold p * radius p
def decrease (p : Params) := (threshold p - allowance p / 2) * radius p

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def velocity (g : E) (H : E →L[ℝ] E) (t : ℝ) : E :=
  NormedSpace.exp (t • (-H)) g

def displacement (g : E) (H : E →L[ℝ] E) (t : ℝ) : E :=
  -(∫ u in (0 : ℝ)..t, velocity g H u)

def energy (g : E) (H : E →L[ℝ] E) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ‖velocity g H u‖ ^ 2

def margin (p : Params) (g : E) (H : E →L[ℝ] E) (t : ℝ) : ℝ :=
  min (‖velocity g H t‖ - threshold p) (energyCap p - energy g H t)

def stopTime (p : Params) (g : E) (H : E →L[ℝ] E) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ margin p g H t = 0}

inductive State (p : Params) where
  | active (x : p.E) (stored : p.E →L[ℝ] p.E)
  | done (x : p.E)

def point {p : Params} : State p → p.E
  | .active x _ | .done x => x

def stored {p : Params} : State p → (p.E →L[ℝ] p.E)
  | .active _ B => B
  | .done _ => 0

def advance (p : Params) (s : State p) (g : p.E) (B : p.E →L[ℝ] p.E) : State p :=
  match s with
  | .done y => .done y
  | .active x _ =>
    if ‖g‖ ≤ p.ε then .done x else
      let t := stopTime p g B
      let y := x + displacement g B t
      if ‖velocity g B t‖ ≤ threshold p then .done y else .active y B

open LongTails.Algorithms.EnergyHessianReuse (Plan Reply readGradient readHessian channelAlgorithm)

def fresh (p : Params) (s : State p) : Plan p (State p) 2 :=
  .ask (0, point s) fun rg => .ask (1, point s) fun rh =>
    .done (advance p s (readGradient p rg) (readHessian p rh))

def reuse (p : Params) (s : State p) : Plan p (State p) 1 :=
  .ask (0, point s) fun rg => .done (advance p s (readGradient p rg) (stored s))

def steps (p : Params) : ℕ → Σ k, Plan p (State p) k
  | 0 => ⟨0, .done (.active p.x0 0)⟩
  | j+1 =>
    let prev := steps p j
    if j % p.m = 0 then ⟨_, QueryPlan.bind prev.2 (fresh p)⟩
    else ⟨_, QueryPlan.bind prev.2 (reuse p)⟩

def horizon (p : Params) := ⌊p.Δ / decrease p⌋₊ + 1

def algorithm (p : Params) : Algorithm p.E (Reply p) p.E 2 :=
  channelAlgorithm (0, p.x0) p.x0 (QueryPlan.map point (steps p (horizon p)).2)

end
end LongTails.Algorithms.HessianReuseModelFlow
