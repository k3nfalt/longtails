import LongTails.Template
import LongTails.Algorithms.RingmasterAsgd
import LongTails.Algorithms.BatchIterations

open MeasureTheory
namespace LongTails.Setups.RingmasterIterations
open OracleTemplate OracleTemplate.RingmasterAsgd
open OracleTemplate.Rennala (Instance Point)

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  R : ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := stepSize p.L p.σ p.ε p.R
  R := p.R
  x0 := p.x0
  K := iterationHorizon p.L p.σ p.ε p.Δ p.R

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 1 ≤ p.R
  admissible p I O :=
    (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
    (∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x, I.lower ≤ I.f x) ∧
    I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d) (arrive : ℕ → Fin p.n),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        O = arrivalOracle (publicInput p) arrive P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = ringmasterPoint q

end LongTails.Setups.RingmasterIterations
