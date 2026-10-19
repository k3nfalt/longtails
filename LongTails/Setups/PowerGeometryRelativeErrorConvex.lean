import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.PowerGeometryRelativeErrorConvex

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L : ℝ
  α : ℝ
  p : ℝ
  c : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

noncomputable def Public.ψ (d : Public) (x : d.E) : ℝ := ‖x - d.x0‖ ^ 2 / 2

def Public.Valid (d : Public) : Prop :=
  0 < d.L ∧ 2 < d.p ∧ 0 < d.c ∧ 0 ≤ d.α ∧ d.α ≤ 1 / 4 ∧
  (∀ x, DifferentiableAt ℝ d.ψ x) ∧
  (∀ x y, d.c * ‖y - x‖ ^ d.p /
    (‖y - d.x0‖ + ‖x - d.x0‖) ^ (d.p - 2) ≤
      d.ψ y - d.ψ x - fderiv ℝ d.ψ x (y - x))

structure Params where
  data : Public
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance d := d.E → ℝ
  Query d := d.E
  Reply d := d.E →L[ℝ] ℝ
  Output d := d.E
  publicInput q := q.data
  valid q := q.data.Valid ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ q.data.L * ‖x - y‖) ∧
    (∀ k seed x, ‖oracle.answer k (0, x) seed - fderiv ℝ f x‖ ≤
      q.data.α * ‖fderiv ℝ f x‖) ∧
    (∃ xstar, (∀ x, f xstar ≤ f x) ∧ ‖xstar - q.data.x0‖ ≤ q.R)
  successful q f output P :=
    ∃ xstar, (∀ x, f xstar ≤ f x) ∧
      ∀ᵐ ω ∂(P : Measure _), f (output ω) - f xstar ≤ q.ε

end LongTails.Setups.PowerGeometryRelativeErrorConvex
