import LongTails.Setups.StochasticGeneralizedMonotone
import Mathlib.Analysis.Convex.Basic

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticConstrainedGeneralizedMonotone

open OracleTemplate

structure Params extends StochasticGeneralizedMonotone.Params.{0} where
  G : ℝ

structure Instance (q : Params) where
  F : q.E → q.E
  X : Set q.E

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance := Instance
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 ≤ q.G ∧ 0 ≤ q.σ ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)) (proj : q.E → q.E),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (i, x) seed => if i = 0 then g x seed else proj x } ∧
    (∀ z, proj z ∈ I.X ∧ ∀ w ∈ I.X, ⟪z - proj z, w - proj z⟫ ≤ 0) ∧
    Convex ℝ I.X ∧ q.x0 ∈ I.X ∧ Continuous I.F ∧
    (∀ x y, 0 ≤ ⟪I.F x - I.F y, x - y⟫) ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.F (x + θ • (y - x))‖ ≤ M) →
      ‖I.F x - I.F y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    (∃ xstar ∈ I.X, (∀ w ∈ I.X, 0 ≤ ⟪I.F xstar, w - xstar⟫) ∧
      ‖q.x0 - xstar‖ ≤ q.R ∧ ‖I.F xstar‖ ≤ q.G) ∧
    StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure _) I.F g q.σ
  successful q I output P :=
    Measurable output ∧ (P : Measure _) {ω | ¬(output ω ∈ I.X ∧
      ∃ ξ : q.E, (∀ w ∈ I.X, ⟪ξ, w - output ω⟫ ≤ 0) ∧ ‖I.F (output ω) + ξ‖ ≤ q.ε)} ≤
        ENNReal.ofReal q.δ

end LongTails.Setups.StochasticConstrainedGeneralizedMonotone
