import outputs.Algorithms.RennalaUniform
import outputs.Algorithms.BatchIterations
import outputs.Setups.RennalaHalfIterations

open MeasureTheory

namespace OracleTemplate.RennalaUniform

open Rennala

def PowerAssumption (v : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → 0 ≤ v t) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), ContinuousAt v t) ∧
    ∀ T, 0 ≤ T → IntervalIntegrable v volume 0 T

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  power : Fin n → ℝ → ℝ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  gamma := 1 / (2 * p.L)
  S := batchSize p.v p.eps
  x0 := p.x0
  K := ⌈24 * p.L * p.Delta / p.eps⌉₊

end OracleTemplate.RennalaUniform

namespace outputs.Setups.RennalaUniformTime

open OracleTemplate OracleTemplate.RennalaUniform
open OracleTemplate.Rennala (Instance Point StochasticOracle batchSize)

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧ ∀ i, PowerAssumption (p.power i)
  admissible p I O :=
    BatchIterations.SmoothLower ⟨p.d, p.L, p.v, p.eps, p.Delta, p.x0, 0⟩ I ∧
      ∃ (Ω : Type) (m : MeasurableSpace Ω),
        letI := m
        ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
          (g : Point p.d → Ω → Point p.d),
          LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
            (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
          StochasticOracle Ω μ I.f g p.v ∧
          O = eventOracle (publicInput p) (fun i => work (p.power i)) P g
  successful p I output P :=
    deadline (fun i => work (p.power i)) (batchSize p.v p.eps) ⌈24 * p.L * p.Delta / p.eps⌉₊ < ⊤ →
      Measurable output ∧
        Integrable (fun ω => ‖gradient I.f (output ω).1‖ ^ 2) (P : Measure _) ∧
        (∫ ω, ‖gradient I.f (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.eps ∧
        ∀ᵐ ω ∂(P : Measure _), ENNReal.ofReal (output ω).2 ≤
          deadline (fun i => work (p.power i)) (batchSize p.v p.eps) ⌈24 * p.L * p.Delta / p.eps⌉₊
  allowedAlgorithm p A := A = rennala p

end outputs.Setups.RennalaUniformTime
