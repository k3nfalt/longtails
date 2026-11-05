import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace LongTails.Setups.FiniteSumThirdSmoothConvex

open OracleTemplate MeasureTheory
open FiniteSumSmoothAndConvex (objective)

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  R : ℝ
  ε : ℝ
  G : ℝ
  H : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.nonzero

structure Problem (p : Params) where
  component : Fin p.n → p.E → ℝ
  xstar : p.E

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Problem
  Query p := Fin p.n × p.E
  Reply p := p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 ≤ p.L ∧ 0 < p.R ∧ 0 < p.ε ∧ 0 ≤ p.G ∧ 0 ≤ p.H
  admissible p F oracle :=
    (∀ i, ContDiff ℝ 3 (F.component i)) ∧
    (∀ i, ConvexOn ℝ Set.univ (F.component i)) ∧
    (∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (F.component i))) x -
      fderiv ℝ (fderiv ℝ (gradient (F.component i))) y‖ ≤ p.L * ‖x - y‖) ∧
    IsMinOn (objective F.component) Set.univ F.xstar ∧
    ‖p.x0 - F.xstar‖ ≤ p.R ∧
    ‖gradient (objective F.component) p.x0‖ ≤ p.G ∧
    ‖fderiv ℝ (gradient (objective F.component)) p.x0‖ ≤ p.H ∧
    (∀ history seed i x, oracle.answer history (0, (i, x)) seed =
      (gradient (F.component i) x, fderiv ℝ (gradient (F.component i)) x))
  successful p F output P :=
    Measurable output ∧
    (2 / 3 : ENNReal) ≤ (P : Measure _) {ω |
      objective F.component (output ω) - objective F.component F.xstar ≤ p.ε}

end LongTails.Setups.FiniteSumThirdSmoothConvex
