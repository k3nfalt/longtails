import LongTails.Setups.PointwiseHessianStationarity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace LongTails.Algorithms.PointwiseHessianModelFlow

open OracleTemplate LongTails.Setups.PointwiseHessianStationarity

noncomputable section

def radius (p : Params) : ℝ :=
  Real.sqrt p.ε / (4 * Real.sqrt (p.L₀ + p.L₁ * p.ε))

def energyCap (p : Params) : ℝ := p.ε * radius p / 2

def velocity {p : Params} (g : Point p) (H : Point p →L[ℝ] Point p) (t : ℝ) : Point p :=
  NormedSpace.exp (t • (-H)) g

def displacement {p : Params} (g : Point p) (H : Point p →L[ℝ] Point p) (t : ℝ) : Point p :=
  -(∫ u in (0 : ℝ)..t, velocity g H u)

def energy {p : Params} (g : Point p) (H : Point p →L[ℝ] Point p) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ‖velocity g H u‖ ^ 2

def margin (p : Params) (g : Point p) (H : Point p →L[ℝ] Point p) (t : ℝ) : ℝ :=
  min (‖velocity g H t‖ - p.ε / 2) (energyCap p - energy g H t)

def stopTime (p : Params) (g : Point p) (H : Point p →L[ℝ] Point p) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ margin p g H t = 0}

inductive State (p : Params) where
  | active (x : Point p)
  | done (x : Point p)

def output {p : Params} : State p → Point p
  | .active x | .done x => x

def queryPoint {p : Params} : State p → Point p
  | .active x => x
  | .done _ => 0

def step (p : Params) (x g : Point p) (H : Point p →L[ℝ] Point p) : State p :=
  if ‖g‖ ≤ p.ε then .done x else
    let t := stopTime p g H
    let y := x + displacement g H t
    if ‖velocity g H t‖ ≤ p.ε / 2 then .done y else .active y

def update (p : Params) : State p → Reply p → State p
  | .active x, reply => step p x reply.2.1 reply.2.2
  | .done x, _ => .done x

def algorithm (p : Params) : Algorithm (Point p) (Reply p) (Point p) where
  State := State p
  initial _ := .active 0
  query s := (0, queryPoint s)
  update := update p
  output := output

end
end LongTails.Algorithms.PointwiseHessianModelFlow
