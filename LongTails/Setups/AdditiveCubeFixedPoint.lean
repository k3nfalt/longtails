import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.AdditiveCubeFixedPoint

open OracleTemplate

structure Params where
  d : ℕ
  R : NNReal
  σ : ℝ
  ε : ℝ

abbrev Point (p : Params) := Fin p.d → ℝ

abbrev Cube (p : Params) := {x : Point p // ‖x‖ ≤ p.R}

def measurablePolicy {p : Params} (A : Algorithm (Cube p) (Point p) (Cube p)) : Prop :=
  ∃ space : MeasurableSpace A.State,
    letI := space
    Measurable A.initial ∧ Measurable A.query ∧ Measurable A.update.uncurry ∧ Measurable A.output

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Cube p → Cube p
  Query := Cube
  Reply := Point
  Output := Cube
  publicInput := fun p => p
  valid p := 0 < p.d ∧ 0 < p.R ∧ 0 ≤ p.σ ∧ 0 < p.ε
  allowedAlgorithm _ A := measurablePolicy A
  admissible p T O :=
    LipschitzWith 1 T ∧
    ∃ (μ : ProbabilityMeasure (Point p)) (P : ProbabilityMeasure (ℕ → Point p)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → Point p) => ξ k) (μ : Measure _) (P : Measure _) ∧
      Integrable (fun z : Point p => z) (μ : Measure (Point p)) ∧
      (∫ z : Point p, z ∂(μ : Measure (Point p))) = (0 : Point p) ∧
      Integrable (fun z : Point p => ‖z‖ ^ 2) (μ : Measure _) ∧
      (∫ z : Point p, ‖z‖ ^ 2 ∂(μ : Measure _)) ≤ p.σ ^ 2 ∧
      O = { Seed := fun _ => Point p, law := P,
            answer := fun _ (_, x) z => (T x).val + z }
  successful p T output P :=
    Measurable output ∧ Integrable (fun ω => dist (T (output ω)) (output ω)) (P : Measure _) ∧
      (∫ ω, dist (T (output ω)) (output ω) ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.AdditiveCubeFixedPoint
