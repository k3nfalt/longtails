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
  sigma : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  R : ℕ
  K : ℕ

noncomputable def stepSize (L sigma eps : ℝ) (R : ℕ) : ℝ :=
  if sigma = 0 then 1 / (2 * R * L) else min (1 / (2 * R * L)) (eps / (4 * L * sigma ^ 2))

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := stepSize p.L p.sigma p.eps p.R
  R := p.R
  x0 := p.x0
  K := p.K

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.sigma ∧ 0 < p.eps ∧ 1 ≤ p.R ∧
    8 * p.R * p.L * p.Delta / p.eps + 16 * p.sigma ^ 2 * p.L * p.Delta / p.eps ^ 2 ≤ p.K
  admissible p I O :=
    BatchIterations.SmoothLower ⟨p.d, p.L, p.sigma ^ 2, p.eps, p.Delta, p.x0, 0⟩ I ∧
      ∃ (Ω : Type) (m : MeasurableSpace Ω),
        letI := m
        ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
          (g : Point p.d → Ω → Point p.d) (arrive : ℕ → Fin p.n),
          LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
            (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
          LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
            (μ : Measure Ω) I.f g p.sigma ∧
          O = arrivalOracle (publicInput p) arrive P g
  successful p I output P :=
    Measurable output ∧ EpsStationary I.f (fun ω => (output ω).1) (P : Measure _) p.eps
  allowedAlgorithm q A := A = ringmaster q

end LongTails.Setups.RingmasterIterations
