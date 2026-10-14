import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

namespace LongTails.Setups.AdaptiveHeavyTailSimplex

open OracleTemplate

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

instance (d : ℕ) : MeasurableSpace (Vector d) := borel _

instance (d : ℕ) : BorelSpace (Vector d) := ⟨rfl⟩

def oneNorm {d : ℕ} (x : Vector d) : ℝ := ∑ i, |x i|

noncomputable def dualNorm {d : ℕ} (x : Vector d) : ℝ := ‖fun i => x i‖

def simplex (d : ℕ) : Set (Vector d) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

structure Public where
  d : ℕ
  hd : 2 ≤ d
  L : ℝ
  δ : ℝ

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  p : ℝ
  σ : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := Vector q.d → ℝ
  Query q := simplex q.d
  Reply q := Vector q.d
  Output q := simplex q.d
  publicInput q := q.toPublic
  valid q := 0 < q.L ∧ 0 < q.δ ∧ q.δ < 1 ∧
    1 < q.p ∧ q.p ≤ 2 ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : simplex q.d → q.Ω → Vector q.d) (ν : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (ν : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ (simplex q.d) f ∧
    (∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x) ∧
    (∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y)) ∧
    (∃ xstar ∈ simplex q.d, IsMinOn f (simplex q.d) xstar) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (ν : Measure _)) ∧
    (∀ x, (∫ ω, g x ω ∂(ν : Measure _)) = gradient f x) ∧
    (∀ x, Integrable (fun ω => dualNorm (g x ω - gradient f x) ^ q.p)
      (ν : Measure _)) ∧
    (∀ x, (∫ ω, dualNorm (g x ω - gradient f x) ^ q.p ∂(ν : Measure _)) ≤
      q.σ ^ q.p)
  successful q f output P :=
    Measurable output ∧ ∃ xstar ∈ simplex q.d, IsMinOn f (simplex q.d) xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.AdaptiveHeavyTailSimplex
