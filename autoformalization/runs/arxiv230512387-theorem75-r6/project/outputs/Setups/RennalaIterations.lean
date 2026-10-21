import outputs.Algorithms.BatchIterations

open MeasureTheory

namespace OracleTemplate.RennalaIterations

abbrev Params := BatchIterations.Params

noncomputable def publicInput (p : Params) : BatchIterations.Public where
  d := p.d
  gamma := Rennala.stepSize p.L p.v p.eps
  S := Rennala.batchSize p.v p.eps
  x0 := p.x0
  N := (max 1 ⌈24 * p.Delta * p.L / p.eps⌉₊ + p.extra) - 1

end OracleTemplate.RennalaIterations

namespace outputs.Setups.RennalaIterations

open OracleTemplate OracleTemplate.RennalaIterations

noncomputable abbrev spec : Setup where
  Params := Params
  Public := BatchIterations.Public
  Instance p := Rennala.Instance p.d
  Query p := Rennala.Point p.d
  Reply p := Rennala.Point p.d
  Output p := Rennala.Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧ 0 ≤ p.Delta
  admissible p I O := BatchIterations.SmoothLower p I ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Rennala.Point p.d → Ω → Rennala.Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        Rennala.StochasticOracle Ω μ I.f g p.v ∧
        O = BatchIterations.oracle (publicInput p) P g
  successful p I output P := Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps
  allowedAlgorithm p A := A = BatchIterations.algorithm p

end outputs.Setups.RennalaIterations
