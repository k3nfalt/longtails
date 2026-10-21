import outputs.Setups.RingmasterIterations
import LongTails.Setups.RennalaUniformTime

open MeasureTheory

namespace outputs.Setups.RingmasterUniversalTime

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
  power : Fin n → ℝ → ℝ

noncomputable def threshold (sigma eps : ℝ) : ℕ := max 1 ⌈sigma ^ 2 / eps⌉₊

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := outputs.Setups.RingmasterIterations.stepSize p.L p.sigma p.eps (threshold p.sigma p.eps)
  R := threshold p.sigma p.eps
  x0 := p.x0
  K := threshold p.sigma p.eps * ⌈48 * p.L * p.Delta / p.eps⌉₊

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.sigma ∧ 0 < p.eps ∧ ∀ i, RennalaUniform.PowerAssumption (p.power i)
  admissible p I O :=
    BatchIterations.SmoothLower ⟨p.d, p.L, p.sigma ^ 2, p.eps, p.Delta, p.x0, 0⟩ I ∧
      ∃ (Ω : Type) (m : MeasurableSpace Ω),
        letI := m
        ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
          (g : Point p.d → Ω → Point p.d),
          LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
            (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
          LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
            (μ : Measure Ω) I.f g p.sigma ∧
          O = eventOracle (publicInput p) (fun i => RennalaUniform.work (p.power i)) P g
  successful p I output P :=
    RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
        (threshold p.sigma p.eps) ⌈48 * p.L * p.Delta / p.eps⌉₊ < ⊤ →
      Measurable output ∧ EpsStationary I.f (fun ω => (output ω).1) (P : Measure _) p.eps ∧
        ∀ᵐ ω ∂(P : Measure _), ENNReal.ofReal (output ω).2 ≤
          RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
            (threshold p.sigma p.eps) ⌈48 * p.L * p.Delta / p.eps⌉₊
  allowedAlgorithm q A := A = ringmaster q

end outputs.Setups.RingmasterUniversalTime
