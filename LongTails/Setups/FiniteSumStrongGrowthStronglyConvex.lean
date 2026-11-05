import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Set
open scoped BigOperators

namespace LongTails.Setups.FiniteSumStrongGrowthStronglyConvex

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  μ : ℝ
  ρ : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.nonzero

noncomputable abbrev objective {p : Params} (f : Fin p.n → p.E → ℝ) : p.E → ℝ :=
  FiniteSumSmoothAndConvex.objective f

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.μ ∧ 1 ≤ p.ρ ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p f O :=
    (∀ i, ConvexOn ℝ univ (f i)) ∧
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L * ‖x - y‖) ∧
    StrongConvexOn univ p.μ (objective f) ∧
    (∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) x‖ ^ 2 ≤
      p.ρ * ‖gradient (objective f) x‖ ^ 2) ∧
    (∀ k seed i x, O.answer k (0, (i, x)) seed = gradient (f i) x) ∧
    (∃ xstar, IsMinOn (objective f) univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R)
  successful p f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn (objective f) univ xstar ∧
        Integrable (fun ω => objective f (output ω) - objective f xstar)
          (P : Measure _) ∧
        (∫ ω, objective f (output ω) - objective f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
