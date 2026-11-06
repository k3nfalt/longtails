import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set MeasureTheory

namespace LongTails.Setups.SmoothFiniteMaximum

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  m : ℕ
  hm : 2 ≤ m
  G : ℝ
  L : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.finiteE
  Public.measurableE Public.borelE

def domain (p : Public) : Set p.E := Metric.closedBall p.x0 p.R

structure Instance (p : Public) where
  loss : Fin p.m → p.E → ℝ
  xstar : p.E

noncomputable def objective {p : Public} (I : Instance p) (x : p.E) : ℝ :=
  sSup (Set.range fun i => I.loss i x)

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Instance
  Query p := Fin p.m × p.E
  Reply p := ℝ × p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.G ∧ 0 ≤ p.L ∧ 0 < p.R ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ i, ConvexOn ℝ (domain p) (I.loss i)) ∧
    (∀ i x, x ∈ domain p → HasGradientAt (I.loss i) (gradient (I.loss i) x) x) ∧
    (∀ i x, x ∈ domain p → ‖gradient (I.loss i) x‖ ≤ p.G) ∧
    (∀ i x y, x ∈ domain p → y ∈ domain p →
      ‖gradient (I.loss i) x - gradient (I.loss i) y‖ ≤ p.L * ‖x - y‖) ∧
    I.xstar ∈ domain p ∧ IsMinOn (objective I) (domain p) I.xstar ∧
    (∀ history seed i x, x ∈ domain p →
      oracle.answer history (0, (i, x)) seed = (I.loss i x, gradient (I.loss i) x))
  successful p I output P :=
    Measurable output ∧
    (∀ᵐ ω ∂(P : Measure _), output ω ∈ domain p) ∧
    (9 : ENNReal) / 10 ≤
      (P : Measure _) {ω | objective I (output ω) - objective I I.xstar ≤ p.ε}

end LongTails.Setups.SmoothFiniteMaximum
