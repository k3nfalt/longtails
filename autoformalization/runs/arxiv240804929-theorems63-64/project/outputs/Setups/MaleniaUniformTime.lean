import outputs.Setups.RennalaUniformTime
import outputs.Setups.MaleniaIterations

open MeasureTheory

namespace OracleTemplate.MaleniaUniform

open Rennala

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  power : Fin n → ℝ → ℝ
  calls : ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := MaleniaIterations.stepSize p.L p.v p.eps (MaleniaIterations.batchSize p.n p.v p.eps)
  S := MaleniaIterations.batchSize p.n p.v p.eps
  x0 := p.x0
  K := ⌈24 * p.L * p.Delta / p.eps⌉₊

noncomputable def threshold (n : ℕ) (v eps : ℝ) : ℝ := max (2 * v / (n * eps)) 1

end OracleTemplate.MaleniaUniform

namespace outputs.Setups.MaleniaUniformTime

open OracleTemplate OracleTemplate.MaleniaUniform
open OracleTemplate.Rennala (Instance Point StochasticOracle batchSize)

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Rennala.Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p := 0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧
    ∀ i, RennalaUniform.PowerAssumption (p.power i)
  admissible p I O :=
    BatchIterations.SmoothLower ⟨p.d, p.L, p.v, p.eps, p.Delta, p.x0, 0⟩ I ∧
      ∃ fs : Fin p.n → Point p.d → ℝ,
        (∀ x, I.f x = (1 / (p.n : ℝ)) * ∑ i, fs i x) ∧
        (∀ i x, HasGradientAt (fs i) (gradient (fs i) x) x) ∧
        ∃ (Ω : Type) (m : MeasurableSpace Ω),
          letI := m
          ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
            (g : Fin p.n → Point p.d → Ω → Point p.d),
            LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
            (∀ i, StochasticOracle Ω μ (fs i) (g i) p.v) ∧
            O = eventOracle (publicInput p) (fun i => RennalaUniform.work (p.power i)) P g
  successful p I output P :=
    deadline (fun i => RennalaUniform.work (p.power i)) (threshold p.n p.v p.eps)
        ⌈24 * p.L * p.Delta / p.eps⌉₊ < ⊤ →
      (∑ i, ⌊RennalaUniform.work (p.power i)
          (deadline (fun i => RennalaUniform.work (p.power i)) (threshold p.n p.v p.eps)
            ⌈24 * p.L * p.Delta / p.eps⌉₊).toReal⌋₊) ≤ p.calls →
      Measurable output ∧
        Integrable (fun ω => ‖gradient I.f (output ω).1‖ ^ 2) (P : Measure _) ∧
        (∫ ω, ‖gradient I.f (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.eps ∧
        ∀ᵐ ω ∂(P : Measure _), ENNReal.ofReal (output ω).2 ≤
          deadline (fun i => RennalaUniform.work (p.power i)) (threshold p.n p.v p.eps)
            ⌈24 * p.L * p.Delta / p.eps⌉₊
  allowedAlgorithm q A := A = malenia q

end outputs.Setups.MaleniaUniformTime
