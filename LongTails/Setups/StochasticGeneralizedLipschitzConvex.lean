import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticGeneralizedLipschitzConvex

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  x0 : E
  R : ℝ
  G0 : ℝ
  G1 : ℝ
  ε : ℝ

attribute [instance] Public.normedE Public.linearE Public.completeE
  Public.measurableE Public.borelE Public.countableE

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]

attribute [instance] Params.measurableΩ

structure IsOracle {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Ω] (p : Measure Ω)
    (f : E → ℝ) (xstar : E) (oracle : E → Ω → E) (G0 G1 : ℝ) : Prop where
  measurable : Measurable (Function.uncurry oracle)
  integrable : ∀ x, Integrable (oracle x) p
  subgradient : ∀ x y,
    f x - f y ≤ ⟪∫ ω, oracle x ω ∂p, x - y⟫
  decomposition : ∀ x, ∃ u v : Ω → E,
    Measurable u ∧ Measurable v ∧
    (∀ᵐ ω ∂p, oracle x ω = u ω + v ω) ∧
    Integrable (fun ω => ‖u ω‖ ^ 2) p ∧
    (∫ ω, ‖u ω‖ ^ 2 ∂p) ≤ G0 ^ 2 ∧
    (∀ᵐ ω ∂p, ‖v ω‖ ≤ G1 * (f x - f xstar))

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q.toPublic
  valid q := 0 < q.R ∧ 0 < q.G0 ∧ 0 ≤ q.G1 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧ Continuous f ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      IsOracle (p : Measure _) f xstar g q.G0 q.G1
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal (1 / 10 : ℝ)

end LongTails.Setups.StochasticGeneralizedLipschitzConvex
