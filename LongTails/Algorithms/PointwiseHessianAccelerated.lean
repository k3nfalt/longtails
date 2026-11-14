import LongTails.Setups.PointwiseHessianConvex
import LongTails.Algorithms.CompositeCubicAcceleration

namespace LongTails.Algorithms.PointwiseHessianAccelerated

open OracleTemplate LongTails.Setups.PointwiseHessianConvex

noncomputable section

variable (p : Public)

def initialWeight : ℝ := p.R ^ 2 / (2 * p.Δ)

def targetWeight : ℝ := p.R ^ 2 / p.ε

def gradientThreshold : ℝ := p.ε / (1000 * p.R)

def weight (A η : ℝ) : ℝ := CompositeCubicAcceleration.trialWeight η A

def radiusCap (τ : ℝ) : ℝ :=
  if p.M₀ = 0 then 16 * p.R else min (16 * p.R) (τ / (64 * p.M₀))

def initialRadius (τ : ℝ) : ℝ := min (gradientThreshold p / τ) (radiusCap p τ)

def continuationRatio (τ r : ℝ) : ℝ :=
  1 / (64 * (1 + p.M₁ * r ^ 2 + p.M₀ * r / τ))

def initialRegularization (τ r : ℝ) (g : p.E) : ℝ :=
  min (1 / τ) (continuationRatio p τ r * r / (4 * ‖g‖))

def newtonPoint (b : ℝ) (c x g : p.E) (H : p.E →L[ℝ] p.E) : p.E :=
  x - Function.invFun (ContinuousLinearMap.id ℝ p.E + b • H) (b • g + x - c)

inductive Phase where
  | centerGradient
  | newtonHessian
  | newtonGradient
  | finished

structure State where
  phase : Phase
  A : ℝ
  η : ℝ
  w : p.E
  z : p.E
  τ : ℝ
  r : ℝ
  b : ℝ
  x : p.E
  g : p.E
  centerG : p.E
  out : p.E

variable {p}

def State.a (s : State p) : ℝ := weight s.A s.η

def State.center (s : State p) : p.E :=
  (s.A / (s.A + s.a)) • s.w + (s.a / (s.A + s.a)) • s.z

def startTrial (s : State p) (τ r : ℝ) : State p :=
  { s with
    phase := .newtonHessian
    τ := τ
    r := r
    b := initialRegularization p τ r s.centerG
    x := s.center
    g := s.centerG }

def failedTrial (s : State p) : State p :=
  if s.r < radiusCap p s.τ then
    startTrial s s.τ (min (2 * s.r) (radiusCap p s.τ))
  else startTrial s (2 * s.τ) (initialRadius p (2 * s.τ))

def finish (s : State p) (x : p.E) : State p := { s with phase := .finished, out := x }

def accept (s : State p) : State p :=
  let γ := s.η / s.τ
  let Anew := s.A + γ * s.a
  let wnew := ((1 - γ) * s.A / Anew) • s.w + (γ * (s.A + s.a) / Anew) • s.x
  let next := { s with
    A := Anew
    w := wnew
    z := s.z - (γ * s.a) • s.g
    η := if s.τ = s.η then s.η / 2 else 2 * s.η
    out := wnew
    phase := .centerGradient }
  if targetWeight p ≤ Anew then finish next wnew else next

def readGradient : p.E ⊕ (p.E →L[ℝ] p.E) → p.E
  | .inl g => g
  | .inr _ => 0

def readHessian : p.E ⊕ (p.E →L[ℝ] p.E) → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr H => H

def update (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : State p :=
  match s.phase with
  | .finished => s
  | .centerGradient =>
      let g := readGradient reply
      if ‖g‖ ≤ gradientThreshold p then finish s s.center
      else startTrial { s with centerG := g } s.η (initialRadius p s.η)
  | .newtonHessian =>
      let xnew := newtonPoint p s.b s.center s.x s.g (readHessian reply)
      if ‖xnew - s.center‖ ≤ 2 * s.r then
        { s with phase := .newtonGradient, x := xnew }
      else failedTrial s
  | .newtonGradient =>
      let next := { s with g := readGradient reply }
      if ‖next.g‖ ≤ gradientThreshold p then finish next next.x
      else if s.b < 1 / s.τ then
        { next with
          phase := .newtonHessian
          b := min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8)) }
      else if ‖s.b • next.g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2 then
        accept next
      else { next with phase := .newtonHessian }

def initial (p : Public) : State p :=
  { phase := if p.Δ ≤ p.ε then .finished else .centerGradient,
    A := initialWeight p, η := 1 / initialWeight p, w := p.x0, z := p.x0,
    τ := 0, r := 0, b := 0, x := p.x0, g := 0, centerG := 0, out := p.x0 }

def query (s : State p) : Fin 2 × p.E :=
  match s.phase with
  | .centerGradient => (0, s.center)
  | .newtonHessian => (1, s.x)
  | .newtonGradient => (0, s.x)
  | .finished => (0, s.out)

def algorithm (p : Public) : Algorithm p.E (p.E ⊕ (p.E →L[ℝ] p.E)) p.E 2 where
  State := State p
  initial _ := initial p
  query := query
  update := update
  output := State.out

end

end LongTails.Algorithms.PointwiseHessianAccelerated
