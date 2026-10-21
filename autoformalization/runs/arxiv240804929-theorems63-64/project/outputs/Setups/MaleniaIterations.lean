import outputs.Algorithms.MaleniaUniform

open MeasureTheory

namespace OracleTemplate.MaleniaIterations

noncomputable def batchSize (n : ℕ) (v eps : ℝ) : ℕ := max ⌈v / eps⌉₊ n

noncomputable def stepSize (L v eps : ℝ) (S : ℕ) : ℝ :=
  if v = 0 then 1 / L else min (1 / L) (eps * S / (2 * L * v))

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Rennala.Point d
  extra : ℕ

noncomputable def publicInput (p : Params) : BatchIterations.Public where
  d := p.d
  gamma := stepSize p.L p.v p.eps (batchSize p.n p.v p.eps)
  S := batchSize p.n p.v p.eps
  x0 := p.x0
  N := (max 1 ⌈24 * p.L * p.Delta / p.eps⌉₊ + p.extra) - 1

end OracleTemplate.MaleniaIterations

namespace outputs.Setups.MaleniaIterations

open OracleTemplate OracleTemplate.MaleniaIterations

noncomputable abbrev spec : Setup where
  Params := Params
  Public := BatchIterations.Public
  Instance p := Rennala.Instance p.d
  Query p := Rennala.Point p.d
  Reply p := Rennala.Point p.d
  Output p := Rennala.Point p.d
  publicInput := publicInput
  valid p := 0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps
  admissible p I O :=
    BatchIterations.SmoothLower ⟨p.d, p.L, p.v, p.eps, p.Delta, p.x0, p.extra⟩ I ∧
      ∃ fs : Fin p.n → Rennala.Point p.d → ℝ,
        (∀ x, I.f x = (1 / (p.n : ℝ)) * ∑ i, fs i x) ∧
        (∀ i x, HasGradientAt (fs i) (gradient (fs i) x) x) ∧
        ∃ (Ω : Type) (m : MeasurableSpace Ω),
          letI := m
          ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
            (g : Fin p.n → Rennala.Point p.d → Ω → Rennala.Point p.d) (B : ℕ → Fin p.n → ℕ),
            LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
            (∀ i, Rennala.StochasticOracle Ω μ (fs i) (g i) p.v) ∧
            (∀ r, MaleniaUniform.harmonicReady p.n (batchSize p.n p.v p.eps) (B r)) ∧
            O = MaleniaUniform.iterOracle (publicInput p) p.n B P g
  successful p I output P := Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps
  allowedAlgorithm q A := A = BatchIterations.algorithm q

end outputs.Setups.MaleniaIterations
