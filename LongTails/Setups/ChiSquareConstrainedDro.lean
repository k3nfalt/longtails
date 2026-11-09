import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.ChiSquareConstrainedDro

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ξ : Type
  [measurableΞ : MeasurableSpace Ξ]
  ρ : ℝ
  G : ℝ
  B : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΞ

structure Instance (q : Params) where
  loss : q.E → q.Ξ → ℝ
  sub : q.E → q.Ξ → q.E
  law : ProbabilityMeasure q.Ξ
  domain : Set q.E

def IsFeasibleDensity {q : Params} (I : Instance q) (w : q.Ξ → ℝ) : Prop :=
  Measurable w ∧ (∀ ξ, 0 ≤ w ξ) ∧ MemLp w 2 (I.law : Measure q.Ξ) ∧
    (∫ ξ, w ξ ∂(I.law : Measure q.Ξ)) = 1 ∧
    (∫ ξ, (w ξ - 1) ^ 2 ∂(I.law : Measure q.Ξ)) / 2 ≤ q.ρ

noncomputable def objective {q : Params} (I : Instance q) (x : q.E) : ℝ :=
  sSup {v | ∃ w, IsFeasibleDensity I w ∧ v = ∫ ξ, w ξ * I.loss x ξ ∂(I.law : Measure q.Ξ)}

noncomputable def sampleOracle {q : Params} (I : Instance q) (projection : q.E → q.E)
    (P : ProbabilityMeasure (ℕ → q.Ξ)) : Oracle q.E (q.E × ℝ × q.E) where
  Seed := fun _ => q.Ξ
  law := P
  answer := fun _ (_, y) seed =>
    (projection y, I.loss (projection y) seed, I.sub (projection y) seed)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query q := q.E
  Reply q := q.E × ℝ × q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.ρ ∧ 0 < q.G ∧ 0 < q.B ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q I O :=
    ∃ (projection : q.E → q.E) (P : ProbabilityMeasure (ℕ → q.Ξ)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ξ) => ξ k)
      (I.law : Measure q.Ξ) (P : Measure _) ∧
    O = sampleOracle I projection P ∧
    Convex ℝ I.domain ∧ IsClosed I.domain ∧ q.x0 ∈ I.domain ∧
    Measurable projection ∧
    (∀ x, projection x ∈ I.domain) ∧
    (∀ x, ∀ u ∈ I.domain, ⟪x - projection x, u - projection x⟫ ≤ 0) ∧
    Measurable (Function.uncurry I.loss) ∧
    Measurable (Function.uncurry I.sub) ∧
    (∀ ξ, ∀ x ∈ I.domain, ∀ y ∈ I.domain, I.loss x ξ + ⟪I.sub x ξ, y - x⟫ ≤ I.loss y ξ) ∧
    (∀ ξ, ∀ x ∈ I.domain, 0 ≤ I.loss x ξ ∧ I.loss x ξ ≤ q.B) ∧
    (∀ ξ, ∀ x ∈ I.domain, ‖I.sub x ξ‖ ≤ q.G) ∧
    (∃ xstar ∈ I.domain, IsMinOn (objective I) I.domain xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q I output P :=
    Measurable output ∧ (∀ ω, output ω ∈ I.domain) ∧
    ∃ xstar ∈ I.domain, IsMinOn (objective I) I.domain xstar ∧
      Integrable (fun ω => objective I (output ω) - objective I xstar) (P : Measure _) ∧
      (∫ ω, objective I (output ω) - objective I xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.ChiSquareConstrainedDro
