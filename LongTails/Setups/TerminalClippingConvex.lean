import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.TerminalClippingConvex

open OracleTemplate

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

instance (d : ℕ) : MeasurableSpace (Vector d) := borel _
instance (d : ℕ) : BorelSpace (Vector d) := ⟨rfl⟩

structure Public where
  d : ℕ
  x0 : Vector d
  B : ℝ
  G : ℝ
  δ : ℝ
  R : ℝ
  ε : ℝ

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]

attribute [instance] Params.measurableΩ

structure Instance (q : Public) where
  f : Vector q.d → ℝ
  domain : Set (Vector q.d)

inductive Query (q : Public) where
  | subgradient : Vector q.d → Query q
  | projection : Vector q.d → Query q

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query := Query
  Reply q := Vector q.d
  Output q := Vector q.d
  publicInput q := q.toPublic
  valid q := 0 < q.B ∧ 0 < q.G ∧ 0 < q.δ ∧ q.δ < 1 ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q I O :=
    ∃ (g : Vector q.d → q.Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
      (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (ν : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, query) seed => match query with
            | .subgradient x => g x seed
            | .projection x => projection x } ∧
    Convex ℝ I.domain ∧ IsClosed I.domain ∧ q.x0 ∈ I.domain ∧
    ConvexOn ℝ I.domain I.f ∧ Measurable I.f ∧
    (∃ xstar ∈ I.domain, IsMinOn I.f I.domain xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    Measurable projection ∧
    (∀ x, projection x ∈ I.domain) ∧
    (∀ x, ∀ u ∈ I.domain, ⟪x - projection x, u - projection x⟫ ≤ 0) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x ∈ I.domain, Integrable (g x) (ν : Measure _)) ∧
    (∀ x ∈ I.domain, ∀ y ∈ I.domain,
      I.f x - I.f y ≤ ⟪∫ ω, g x ω ∂(ν : Measure _), x - y⟫) ∧
    (∀ x ∈ I.domain, Integrable (fun ω => ‖g x ω‖ ^ 2) (ν : Measure _)) ∧
    (∀ x ∈ I.domain, (∫ ω, ‖g x ω‖ ^ 2 ∂(ν : Measure _)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
  successful q I output P :=
    Measurable output ∧ (∀ ω, output ω ∈ I.domain) ∧
    ∃ xstar ∈ I.domain, IsMinOn I.f I.domain xstar ∧
      (P : Measure _) {ω | q.ε < I.f (output ω) - I.f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.TerminalClippingConvex
