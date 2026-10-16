import LongTails.Algorithms.QueryPlan
import LongTails.Setups.GradientDependentHessian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.EnergyHessianReuse

open OracleTemplate LongTails.Setups.GradientDependentHessian

noncomputable section

abbrev Reply (p : Params) := p.E ⊕ (p.E →L[ℝ] p.E)
abbrev Plan (p : Params) (U : Type) (n : ℕ) := QueryPlan (Fin 2 × p.E) (Reply p) U n

def radius (p : Params) : ℝ := if p.L₁ = 0 then p.Δ / p.ε else 1 / (100 * Real.sqrt p.L₁)

def burnCount (p : Params) : ℕ :=
  ⌈Real.log (1 + p.L₁ * p.G₀ / (p.m * p.L₀)) / Real.log (4 / 3)⌉₊

def blockCount (p : Params) : ℕ :=
  ⌈(27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) +
    15000 * p.Δ * Real.sqrt (p.m * p.L₁) / p.ε + 72) / (p.m + 1)⌉₊

structure Point (p : Params) where
  x : p.E
  g : p.E
  best : p.E
  bestNorm : ℝ
  σ : ℝ

def coefficient (p : Params) (a : Point p) : ℝ :=
  max (a.σ / 2) (100 * (p.m * p.L₀ + p.L₁ * ‖a.g‖))

def certificate (p : Params) (g : p.E) (B : p.E →L[ℝ] p.E) (δ σ : ℝ)
    (s : p.E) (μ : ℝ) : Prop :=
  ‖s‖ ≤ radius p ∧ 0 ≤ μ ∧
  g + B s + (2 * δ + σ * ‖s‖ + μ) • s = 0 ∧
  μ * (‖s‖ - radius p) = 0 ∧
  ∀ v, 0 ≤ ⟪v, B v + (2 * δ + σ * ‖s‖ + μ) • v⟫

def selectedStep (p : Params) (g : p.E) (B : p.E →L[ℝ] p.E) (δ σ : ℝ) : p.E × ℝ := by
  classical
  exact if h : ∃ z : p.E × ℝ, certificate p g B δ σ z.1 z.2 then Classical.choose h else (0, 0)

def readGradient (p : Params) : Reply p → p.E
  | .inl g => g
  | .inr _ => 0

def readHessian (p : Params) : Reply p → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr H => H

def move (p : Params) (a : Point p) (s : p.E) (g : p.E) : Point p where
  x := a.x + s
  g := g
  best := if ‖g‖ < a.bestNorm then a.x + s else a.best
  bestNorm := min ‖g‖ a.bestNorm
  σ := coefficient p a

def stepEnergy {p : Params} (σ δ : ℝ) (z : p.E × ℝ) : ℝ :=
  σ * ‖z.1‖ ^ 3 + δ * ‖z.1‖ ^ 2 + z.2 * ‖z.1‖ ^ 2

def fresh (p : Params) (a : Point p) : Plan p (Point p) 2 :=
  .ask (1, a.x) fun reply =>
    let z := selectedStep p a.g (readHessian p reply) 0 (coefficient p a)
    .ask (0, a.x + z.1) fun reply => .done (move p a z.1 (readGradient p reply))

def lazySteps (p : Params) (B : p.E →L[ℝ] p.E) :
    (n : ℕ) → Point p → ℝ → ℝ → Plan p (Point p) n
  | 0, a, _, _ => .done a
  | n + 1, a, energy, path =>
    let δ := 4 * p.L₀ * path + 100 * p.L₁ * energy
    let z := selectedStep p a.g B δ (coefficient p a)
    .ask (0, a.x + z.1) fun reply =>
      lazySteps p B n (move p a z.1 (readGradient p reply))
        (energy + stepEnergy (coefficient p a) δ z) (path + ‖z.1‖)

def block (p : Params) (a : Point p) : Plan p (Point p) (p.m + 3) :=
  .ask (1, a.x) fun reply =>
    let z := selectedStep p a.g (readHessian p reply) 0 (coefficient p a)
    .ask (0, a.x + z.1) fun reply =>
      let next := move p a z.1 (readGradient p reply)
      .ask (1, next.x) fun reply =>
        lazySteps p (readHessian p reply) p.m next
          (stepEnergy (coefficient p a) 0 z) 0

def iteratePlans {p : Params} {c : ℕ} (step : Point p → Plan p (Point p) c) :
    (n : ℕ) → Point p → Plan p (Point p) (c * n)
  | 0, a => .done a
  | n + 1, a => QueryPlan.bind (step a) (iteratePlans step n)

def initial (p : Params) (g : p.E) : Point p where
  x := p.x0
  g := g
  best := p.x0
  bestNorm := ‖g‖
  σ := 100 * (p.m * p.L₀ + p.L₁ * ‖g‖)

def plan (p : Params) : Plan p p.E ((p.m + 3) * blockCount p + 2 * burnCount p + 1) :=
  .ask (0, p.x0) fun reply =>
    QueryPlan.bind (iteratePlans (fresh p) (burnCount p) (initial p (readGradient p reply)))
      (fun a => QueryPlan.map Point.best (iteratePlans (block p) (blockCount p) a))

def channelAlgorithm {Q R U : Type} {n K : ℕ} (q0 : Fin n × Q) (u0 : U)
    (queries : QueryPlan (Fin n × Q) R U K) : Algorithm Q R U n where
  State := Σ k, QueryPlan (Fin n × Q) R U k
  initial _ := ⟨_, queries⟩
  query := QueryPlan.query q0
  update := QueryPlan.update
  output := QueryPlan.output u0

def algorithm (p : Params) : Algorithm p.E (Reply p) p.E 2 :=
  channelAlgorithm (0, p.x0) p.x0 (plan p)

end
end LongTails.Algorithms.EnergyHessianReuse
