import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Convex.Strong

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.CompositeFiniteSumStronglyConvex

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  μ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.nonzero

inductive Query (p : Params) where
  | gradient (i : Fin p.n) (x : p.E)
  | prox (a : ℝ) (z g : p.E)

structure Instance (p : Params) where
  components : Fin p.n → p.E → ℝ
  regularizer : p.E → ℝ
  prox : ℝ → p.E → p.E → p.E

noncomputable def objective (p : Params) (inst : Instance p) (x : p.E) : ℝ :=
  LongTails.Setups.FiniteSumSmoothAndConvex.objective inst.components x + inst.regularizer x

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.μ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p inst oracle :=
    (∀ i, ConvexOn ℝ univ (inst.components i)) ∧
    (∀ i x, HasGradientAt (inst.components i) (gradient (inst.components i) x) x) ∧
    (∀ i x y, ‖gradient (inst.components i) x - gradient (inst.components i) y‖ ≤
      p.L * ‖x - y‖) ∧
    StrongConvexOn univ p.μ inst.regularizer ∧
    (∀ a, 0 < a → ∀ z g, IsMinOn
      (fun v => ‖v - z‖ ^ 2 / (2 * a) + ⟪g, v - z⟫ + inst.regularizer v)
      univ (inst.prox a z g)) ∧
    (∀ k seed i x, oracle.answer k (0, (.gradient i x)) seed = gradient (inst.components i) x) ∧
    (∀ k seed a z g, oracle.answer k (0, (.prox a z g)) seed = inst.prox a z g) ∧
    (∃ xstar, IsMinOn (objective p inst) univ xstar ∧
      objective p inst p.x0 - objective p inst xstar ≤ p.Δ)
  successful p inst output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (objective p inst) univ xstar ∧
      Integrable (fun ω => objective p inst (output ω) - objective p inst xstar)
        (P : Measure _) ∧
      (∫ ω, objective p inst (output ω) - objective p inst xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.CompositeFiniteSumStronglyConvex
