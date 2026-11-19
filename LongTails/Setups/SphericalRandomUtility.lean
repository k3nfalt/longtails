import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory Set Metric
open scoped RealInnerProductSpace NNReal ENNReal

namespace LongTails.Setups.SphericalRandomUtility

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  R : ℝ≥0
  B : ℝ
  ε : ℝ

abbrev Feasible (p : Params) := closedBall (0 : Point p.d) p.R

noncomputable def sampleUtility {d : ℕ} (f : Point d → ℝ) (z x : Point d) : ℝ := f x + ⟪z, x⟫

def good (p : Params) (f : Point p.d → ℝ) : Set (Point p.d) :=
  {z | ∀ x y : Feasible p,
    |sampleUtility f z x - sampleUtility f z y| ≤ p.B * ‖(x : Point p.d) - y‖}

noncomputable def comparePair {p : Params} (f : Point p.d → ℝ)
    (q : Feasible p × Feasible p) (z : Point p.d) : Bool :=
  decide (sampleUtility f z q.2 ≤ sampleUtility f z q.1)

def Spherical {d : ℕ} (μ : Measure (Point d)) : Prop :=
  ∀ U : Point d ≃ₗᵢ[ℝ] Point d, μ.map U = μ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  Query p := Feasible p × Feasible p
  Reply _ := Bool
  Output p := Feasible p
  Instance p := Point p.d → ℝ
  valid p := 2 ≤ p.d ∧ 0 < p.R ∧ 0 < p.B ∧ 0 < p.ε ∧ p.ε ≤ p.B * p.R / 16
  admissible p f O :=
    ConvexOn ℝ (closedBall (0 : Point p.d) p.R) f ∧
    Measurable (Function.uncurry (comparePair (p := p) f)) ∧
    ∃ (μ : ProbabilityMeasure (Point p.d)) (P : ProbabilityMeasure (ℕ → Point p.d)),
      Spherical (d := p.d) (μ : Measure (Point p.d)) ∧ (1 / 2 : ℝ≥0∞) ≤ (μ : Measure _) (good p f) ∧
      StochasticGeneralizedSmoothAndConvex.IID (fun k (z : ℕ → Point p.d) => z k)
        (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => Point p.d
            law := P
            answer := fun _ (_, q) z => comparePair f q z }
  successful p f output P :=
    ∃ xstar : Feasible p, IsMinOn f (closedBall (0 : Point p.d) p.R) xstar.val ∧
      Integrable (fun z => f (output z).val - f xstar.val) (P : Measure _) ∧
      (∫ z, f (output z).val - f xstar.val ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.SphericalRandomUtility
