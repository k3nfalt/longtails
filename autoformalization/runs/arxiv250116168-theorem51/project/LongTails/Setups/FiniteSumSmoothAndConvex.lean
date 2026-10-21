import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.FiniteSumSmoothAndConvex

open OracleTemplate

noncomputable def objective {n : ℕ} {E : Type*} (f : Fin n → E → ℝ) (x : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f i x

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.n ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ k seed i x, HasGradientAt (f i) (oracle.answer k (0, (i, x)) seed) x) ∧
    (∀ k seed i x y, ‖oracle.answer k (0, (i, x)) seed - oracle.answer k (0, (i, y)) seed‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn (objective f) Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (objective f) Set.univ xstar ∧
      Integrable (fun ω => objective f (output ω) - objective f xstar) (P : Measure _) ∧
      (∫ ω, objective f (output ω) - objective f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.FiniteSumSmoothAndConvex
