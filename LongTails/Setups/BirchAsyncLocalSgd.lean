import LongTails.Template
import LongTails.Setups.BirchSgd
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Setups.BirchLocalSgd

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.BirchAsyncLocalSgd

open OracleTemplate OracleTemplate.BirchSgd OracleTemplate.BirchMethods
open OracleTemplate.Rennala (Instance Point)

structure Params where
  d : ℕ
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  B : ℕ
  M : ℕ
  δ : ℕ → ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  gamma := asyncStep p.L p.σ p.ε p.B p.M
  x0 := p.x0
  tree := asyncTree p.M p.δ
  branch := chainBranch
  K := asyncHorizon p.L p.σ p.ε p.Δ p.B p.M

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 < p.B ∧ 0 < p.M ∧ ∀ b, p.δ b ≤ b ∧ p.M * p.δ b < p.B
  admissible p I O :=
    LongTails.Setups.BirchSgd.SmoothObjective I.f p.L ∧
    LongTails.Setups.BirchSgd.LowerBounded I.f I.lower ∧ I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (η : ℕ → Ω) => η k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        O = gradientOracle P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = birch q

end LongTails.Setups.BirchAsyncLocalSgd
