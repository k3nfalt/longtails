import LongTails.Setups.HessianAdaptiveStochasticConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Algorithms.HessianAdaptiveCubic

open LongTails.Setups.HessianAdaptiveStochasticConvex

def minimize {E : Type*} (C : Set E) (fallback : E) (φ : E → ℝ) : E := by
  classical
  exact if h : ∃ x ∈ C, IsMinOn φ C x then h.choose else fallback

def model {d : ℕ} (z g : Point d) (H : Point d →L[ℝ] Point d)
    (q c : ℝ) (x : Point d) : ℝ :=
  ⟪g, x - z⟫ + 1 / 2 * ⟪x - z, H (x - z)⟫ + q * ‖x - z‖ ^ 2 + c * ‖x - z‖ ^ 3

structure State (d : ℕ) where
  iteration : ℕ
  phase : Fin 3
  weight : ℝ
  point : Point d
  dual : Point d
  scale : ℝ
  modelGradient : Point d
  modelHessian : Point d →L[ℝ] Point d
  trial : Point d

def mixing (t : ℕ) : ℝ := 4 / (t + 3)

def center {d : ℕ} (s : State d) : Point d :=
  (1 - mixing s.iteration) • s.point + mixing s.iteration • s.dual

def quadraticDamping (p : Public) (s : State p.d) : ℝ :=
  s.scale * p.D / ((s.iteration : ℝ) * Real.sqrt s.iteration)

def displacement {d : ℕ} (s : State d) : Point d :=
  mixing s.iteration • (s.trial - s.dual)

def queryPoint {d : ℕ} (s : State d) : Point d := center s + displacement s

def damping (p : Public) (s : State p.d) : ℝ :=
  quadraticDamping p s + s.scale * ‖displacement s‖

def increment (p : Public) (s : State p.d) : ℝ :=
  if s.iteration = 1 then s.scale / (mixing s.iteration * damping p s)
  else min (mixing s.iteration * s.weight / (1 - mixing s.iteration))
    (s.scale / (mixing s.iteration * damping p s))

def residualWeight (p : Public) (s : State p.d) : ℝ :=
  s.scale * increment p s / (mixing s.iteration * damping p s)

def primal (p : Public) (s : State p.d) (H : Point p.d →L[ℝ] Point p.d) : Point p.d :=
  minimize p.C p.x0 (model s.dual s.modelGradient (mixing s.iteration • H)
    (mixing s.iteration * quadraticDamping p s / 2)
    (s.scale * mixing s.iteration ^ 2 / 3))

def advance (p : Public) (s : State p.d) (g : Point p.d) : State p.d :=
  let a := increment p s
  let A := s.weight + a
  let r := g - s.modelGradient - s.modelHessian (displacement s)
  { iteration := s.iteration + 1
    phase := 0
    weight := A
    point := A⁻¹ • (s.weight • s.point + a • s.trial)
    dual := minimize p.C p.x0 (model s.dual g 0 (s.scale / (2 * a)) 0)
    scale := max (Real.sqrt (s.scale ^ 2 + residualWeight p s * ‖r‖ ^ 2 / p.D ^ 2))
      (p.σg * ((s.iteration + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2)
    modelGradient := 0
    modelHessian := 0
    trial := p.x0 }

def initial (p : Public) : State p.d :=
  { iteration := 1
    phase := 0
    weight := 0
    point := p.x0
    dual := p.x0
    scale := 2 * p.ρ + p.σg / p.D ^ 2
    modelGradient := 0
    modelHessian := 0
    trial := p.x0 }

def update (p : Public) (s : State p.d)
    (reply : Point p.d × (Point p.d →L[ℝ] Point p.d)) : State p.d :=
  if s.phase = 0 then { s with phase := 1, modelGradient := reply.1 }
  else if s.phase = 1 then
    { s with phase := 2, modelHessian := reply.2, trial := primal p s reply.2 }
  else advance p s reply.1

def output {d : ℕ} (s : State d) : Point d := s.point

def algorithm (p : Public) : OracleTemplate.Algorithm
    (Bool × Point p.d) (Point p.d × (Point p.d →L[ℝ] Point p.d)) (Point p.d) where
  State := State p.d
  initial _ := initial p
  query s := (0, s.phase = 1, if s.phase = 2 then queryPoint s else center s)
  update := update p
  output := output

def modelState (p : Public) (s : State p.d) (g : Point p.d)
    (H : Point p.d →L[ℝ] Point p.d) : State p.d :=
  let s1 := { s with phase := 1, modelGradient := g }
  { s1 with phase := 2, modelHessian := H, trial := primal p s1 H }

def round {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (n : ℕ) (s : State p.d) : State p.d :=
  let m := modelState p s (g (center s) (ξ (3 * n))) (H (center s) (ξ (3 * n + 1)))
  advance p m (g (queryPoint m) (ξ (3 * n + 2)))

def roundState {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) : ℕ → State p.d
  | 0 => initial p
  | n + 1 => round p g H ξ n (roundState p g H ξ n)

def sampleStep {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (sc : State p.d × ℕ) : State p.d × ℕ :=
  let query := (algorithm p).query sc.1
  let reply := if query.2.1 then (0, H query.2.2 (ξ sc.2)) else (g query.2.2 (ξ sc.2), 0)
  (update p sc.1 reply, sc.2 + 1)

def modelAt {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) : State p.d :=
  let s := roundState p g H ξ n
  modelState p s (g (center s) (ξ (3 * n))) (H (center s) (ξ (3 * n + 1)))

end LongTails.Algorithms.HessianAdaptiveCubic
