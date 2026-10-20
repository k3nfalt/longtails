import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.NonEuclideanWeakMinty

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L : ℝ
  ρ : ℝ
  μ : ℝ
  h : E → ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

noncomputable def Public.bregman (p : Public) (u x : p.E) : ℝ :=
  p.h u - p.h x - fderiv ℝ p.h x (u - x)

def Public.Valid (p : Public) : Prop :=
  0 < p.L ∧ 0 ≤ p.ρ ∧ p.ρ ≤ 1 / (20 * p.L) ∧ 0 < p.μ ∧
  (∀ x, DifferentiableAt ℝ p.h x) ∧
  (∀ x u, p.μ / 2 * ‖u - x‖ ^ 2 ≤ p.bregman u x)

structure Params where
  data : Public
  D : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.E →L[ℝ] ℝ
  Query p := p.E
  Reply p := p.E →L[ℝ] ℝ
  Output p := p.E
  publicInput p := p.data
  valid p := p.data.Valid ∧ 0 ≤ p.D ∧ 0 < p.ε
  admissible p F oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = F x) ∧
    (∀ x y, ‖F x - F y‖ ≤ p.data.L * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ p.data.bregman xstar p.data.x0 ≤ p.D ∧
      ∀ x, -p.data.ρ * ‖F x‖ ^ 2 ≤ F x (x - xstar))
  successful p F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ p.ε

end LongTails.Setups.NonEuclideanWeakMinty
