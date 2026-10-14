import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

namespace LongTails.Setups.QuadraticTemporalDiscrepancy

open OracleTemplate

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  μ : ℝ

structure Params extends Public where
  D : ℝ
  Δ : ℝ
  ε : ℝ

structure Instance (p : Public) where
  A : p.E →L[ℝ] p.E
  xstar : p.E

def objective {p : Public} (I : Instance p) (x : p.E) : ℝ :=
  ‖I.A (x - I.xstar)‖ ^ 2 / 2

def exactGradient {p : Public} (I : Instance p) (x : p.E) : p.E :=
  I.A.adjoint (I.A (x - I.xstar))

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.D ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p I O :=
    (∀ x, p.μ * ‖x‖ ^ 2 ≤ ‖I.A x‖ ^ 2 ∧ ‖I.A x‖ ^ 2 ≤ p.L * ‖x‖ ^ 2) ∧
    objective I p.x0 ≤ p.Δ ∧
    (∃ e : ℕ → p.E,
      (∀ k x seed, O.answer k (0, x) seed = exactGradient I x + e k) ∧
      ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ p.D)
  successful p I output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
      objective I (output ω) - objective I I.xstar ≤ p.ε

end LongTails.Setups.QuadraticTemporalDiscrepancy
