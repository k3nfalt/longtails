import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.CompositeLipschitzHessian

open OracleTemplate MeasureTheory Set
open scoped RealInnerProductSpace

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  H : ℝ
  R : ℝ
  ε : ℝ
  m : ℕ

attribute [instance] Params.normedE Params.innerE Params.finiteE

structure Problem (p : Params) where
  f : p.E → ℝ
  ψ : p.E → ℝ
  domain : Set p.E
  xstar : p.E

structure Model (p : Params) where
  center : p.E
  linear : p.E
  quadratic : p.E →L[ℝ] p.E
  cubic : ℝ
  scale : ℝ

def Model.valid {p : Params} (q : Model p) : Prop :=
  0 < q.scale ∧ 0 ≤ q.cubic ∧
    (∀ x y, ⟪x, q.quadratic y⟫ = ⟪q.quadratic x, y⟫) ∧
    (∀ x, 0 ≤ ⟪x, q.quadratic x⟫) ∧
    (0 < q.cubic ∨ ∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪x, q.quadratic x⟫)

noncomputable def Model.derivative {p : Params} (q : Model p) (z : p.E) : p.E :=
  q.linear + q.quadratic (z - q.center) +
    (q.cubic * ‖z - q.center‖) • (z - q.center)

def Model.solution {p : Params} (q : Model p) (F : Problem p) (z : p.E) : Prop :=
  z ∈ F.domain ∧ ∀ u ∈ F.domain,
    0 ≤ ⟪q.derivative z, u - z⟫ + q.scale * (F.ψ u - F.ψ z)

abbrev spec : Setup where
  numOracles := 3
  Params := Params
  Public := Params
  Instance p := Problem p
  Query p := p.E ⊕ Model p
  Reply p := p.E ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.H ∧ 0 < p.R ∧ 0 < p.ε ∧ 1 ≤ p.m
  admissible p F O :=
    ContDiff ℝ 2 F.f ∧ ConvexOn ℝ univ F.f ∧
    (∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤
      p.H * ‖x - y‖) ∧
    ConvexOn ℝ F.domain F.ψ ∧
    IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2} ∧
    p.x0 ∈ F.domain ∧ F.xstar ∈ F.domain ∧ ‖p.x0 - F.xstar‖ ≤ p.R ∧
    (∀ x ∈ F.domain, F.f F.xstar + F.ψ F.xstar ≤ F.f x + F.ψ x) ∧
    (∀ k x seed, O.answer k (0, Sum.inl x) seed = Sum.inl (gradient F.f x)) ∧
    (∀ k x seed, O.answer k (1, Sum.inl x) seed =
      Sum.inr (fderiv ℝ (gradient F.f) x)) ∧
    (∀ k q seed, q.valid → ∃ z,
      O.answer k (2, Sum.inr q) seed = Sum.inl z ∧ q.solution F z)
  successful p F output P := ∀ᵐ ω ∂(P : Measure _),
    output ω ∈ F.domain ∧ F.f (output ω) + F.ψ (output ω) -
      (F.f F.xstar + F.ψ F.xstar) ≤ p.ε

end LongTails.Setups.CompositeLipschitzHessian
