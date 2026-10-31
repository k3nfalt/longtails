import LongTails.Template
import LongTails.Setups.RingmasterIterations
import LongTails.Setups.RennalaIterations
import LongTails.Setups.RennalaUniformTime

open MeasureTheory
namespace LongTails.Setups.RingmasterUniversalTime
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
  power : Fin n → ℝ → ℝ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := stepSize p.L p.σ p.ε (threshold p.σ p.ε)
  R := threshold p.σ p.ε
  x0 := p.x0
  K := timeHorizon p.L p.σ p.ε p.Δ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p := (0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧
      ∀ i, RennalaUniform.PowerAssumption (p.power i)) ∧
    RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
      (max 1 ⌈p.σ ^ 2 / p.ε⌉₊) ⌈48 * p.L * p.Δ / p.ε⌉₊ < ⊤
  admissible p I O :=
    (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
    (∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x, I.lower ≤ I.f x) ∧
    I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        O = eventOracle (publicInput p) (fun i => RennalaUniform.work (p.power i)) P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω).1‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ∧
    (∀ᵐ ω ∂(P : Measure _), ENNReal.ofReal (output ω).2 ≤
      RennalaUniform.deadline (fun i t => RennalaUniform.work (p.power i) t / 4)
        (max 1 ⌈p.σ ^ 2 / p.ε⌉₊) ⌈48 * p.L * p.Δ / p.ε⌉₊)
  allowedAlgorithm q A := A = ringmaster q

end LongTails.Setups.RingmasterUniversalTime
