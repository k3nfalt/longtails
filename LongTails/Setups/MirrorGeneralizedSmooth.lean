import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set

namespace LongTails.Setups.MirrorGeneralizedSmooth

open OracleTemplate

def SegmentSmooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] (g : E → F) (L0 L1 : ℝ) : Prop :=
  ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖g (x + θ • (y - x))‖ ≤ M) →
    ‖g x - g y‖ ≤ (L0 + L1 * M) * ‖x - y‖

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L0 : ℝ
  L1 : ℝ
  D : ℝ
  Δ : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

structure Params extends Public where
  ε : ℝ

inductive Query (p : Public) where
  | gradient (x : p.E)
  | prox (z : p.E) (v : p.E →L[ℝ] ℝ)

inductive Reply (p : Public) where
  | gradient (v : p.E →L[ℝ] ℝ)
  | prox (x : p.E)

structure Instance (p : Public) where
  f : p.E → ℝ
  grad : p.E → p.E →L[ℝ] ℝ
  ψ : p.E → ℝ
  mirrorGrad : p.E → p.E →L[ℝ] ℝ
  prox : p.E → (p.E →L[ℝ] ℝ) → p.E

def bregman {p : Public} (I : Instance p) (u z : p.E) : ℝ :=
  I.ψ u - I.ψ z - I.mirrorGrad z (u - z)

def proxObjective {p : Public} (I : Instance p) (z : p.E) (v : p.E →L[ℝ] ℝ)
    (u : p.E) : ℝ := v u + bregman I u z

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query := Query
  Reply := Reply
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.D ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ history seed x, oracle.answer history (0, .gradient x) seed = .gradient (I.grad x)) ∧
    (∀ history seed z v, oracle.answer history (0, .prox z v) seed = .prox (I.prox z v)) ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasFDerivAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    SegmentSmooth I.grad p.L0 p.L1 ∧
    (∀ x, HasFDerivAt I.ψ (I.mirrorGrad x) x) ∧
    (∀ x y, ‖y - x‖ ^ 2 / 2 ≤ bregman I y x) ∧
    (∀ z v, IsMinOn (proxObjective I z v) univ (I.prox z v)) ∧
    (∃ xstar, IsMinOn I.f univ xstar ∧ bregman I xstar p.x0 ≤ p.D ∧
      I.f p.x0 - I.f xstar ≤ p.Δ)
  successful p I output P :=
    ∃ xstar, IsMinOn I.f univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), I.f (output ω) - I.f xstar ≤ p.ε

end LongTails.Setups.MirrorGeneralizedSmooth
