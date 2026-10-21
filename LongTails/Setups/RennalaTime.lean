import LongTails.Proofs.RennalaAllocation

open MeasureTheory

namespace OracleTemplate.Rennala

end OracleTemplate.Rennala

namespace LongTails.Setups.RennalaTime

open OracleTemplate OracleTemplate.Rennala

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p :=
    0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧ 0 ≤ p.Delta ∧
      (∀ i, 0 < p.tau i) ∧ Monotone p.tau
  admissible p I O :=
    SmoothLower p I ∧
      ∃ (Ω : Type) (m : MeasurableSpace Ω),
        letI := m
        ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
          (g : Point p.d → Ω → Point p.d),
          LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
            (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
          StochasticOracle Ω μ I.f g p.v ∧
          O = eventOracle (publicInput p) p.tau P g
  successful p I output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient I.f (output ω).1‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient I.f (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.eps ∧
      ∀ᵐ ω ∂(P : Measure _), (output ω).2 ≤ deadline p
  allowedAlgorithm p A := A = algorithm p

end LongTails.Setups.RennalaTime
