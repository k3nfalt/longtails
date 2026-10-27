import LongTails.Setups.FiniteSumSmoothAndConvex

open MeasureTheory Set

namespace LongTails.Setups.GeneralizedSmoothFiniteSum

open OracleTemplate
open scoped RealInnerProductSpace

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L0 : ℝ
  L1 : ℝ
  G : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := ℝ × p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 ≤ q.G ∧ 0 < q.R ∧ 0 < q.Δ ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ i, ConvexOn ℝ univ (f i)) ∧
    (∀ k seed i x, (oracle.answer k (0, (i, x)) seed).1 = f i x) ∧
    (∀ k seed i x, HasGradientAt (f i) (oracle.answer k (0, (i, x)) seed).2 x) ∧
    (∀ i, Continuous (gradient (f i))) ∧
    (∀ i x y M, (∀ θ ∈ Icc (0 : ℝ) 1,
      ‖gradient (f i) (x + θ • (y - x))‖ ≤ M) →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    (∃ xstar, IsMinOn (FiniteSumSmoothAndConvex.objective f) univ xstar ∧
      ‖q.x0 - xstar‖ ≤ q.R ∧
      FiniteSumSmoothAndConvex.objective f q.x0 -
        FiniteSumSmoothAndConvex.objective f xstar ≤ q.Δ ∧
      (q.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) xstar‖ ≤ q.G)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (FiniteSumSmoothAndConvex.objective f) univ xstar ∧
      Integrable (fun ω => FiniteSumSmoothAndConvex.objective f (output ω) -
        FiniteSumSmoothAndConvex.objective f xstar) (P : Measure _) ∧
      (∫ ω, FiniteSumSmoothAndConvex.objective f (output ω) -
        FiniteSumSmoothAndConvex.objective f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.GeneralizedSmoothFiniteSum
