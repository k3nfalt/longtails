import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set

namespace LongTails.Setups.InterpolatedGeneralizedFiniteSum

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  n : ℕ
  [nonzero : NeZero n]
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.nonzero

structure Instance (p : Params) where
  loss : Fin p.n → p.E → ℝ
  grad : Fin p.n → p.E → p.E

noncomputable def objective {p : Params} (I : Instance p) (x : p.E) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ i, I.loss i x

def ComponentSmooth {p : Params} (I : Instance p) : Prop :=
  ∀ i x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad i (x + θ • (y - x))‖ ≤ M) →
    ‖I.grad i x - I.grad i y‖ ≤ (p.L0 + p.L1 * M) * ‖x - y‖

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.R ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ k seed i x, oracle.answer k (0, (i, x)) seed = I.grad i x) ∧
    (∀ i, ConvexOn ℝ univ (I.loss i)) ∧
    (∀ i x, HasGradientAt (I.loss i) (I.grad i x) x) ∧
    (∀ i, Continuous (I.grad i)) ∧
    ComponentSmooth I ∧
    ∃ xstar, (∀ i, IsMinOn (I.loss i) univ xstar) ∧ ‖p.x0 - xstar‖ ≤ p.R
  successful p I output P :=
    ∃ xstar, (∀ i, IsMinOn (I.loss i) univ xstar) ∧
      (2 / 3 : ENNReal) ≤ (P : MeasureTheory.Measure _) {ω |
        objective I (output ω) - objective I xstar ≤ p.ε}

end LongTails.Setups.InterpolatedGeneralizedFiniteSum
