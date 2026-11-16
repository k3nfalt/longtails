import LongTails.Setups.StochasticConstrainedQuasar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace LongTails.Setups.HighDimensionalConstrainedQuasar

open OracleTemplate

structure Params where
  d : ℕ
  x0 : EuclideanSpace ℝ (Fin d)
  L : ℝ
  D : ℝ
  γ : ℝ
  σ : ℝ
  ε : ℝ
  δ : ℝ

noncomputable def Params.toStochastic (p : Params) : StochasticConstrainedQuasar.Params where
  E := EuclideanSpace ℝ (Fin p.d)
  L := p.L
  x0 := p.x0
  Ω := Bool
  D := p.D
  γ := p.γ
  σ := p.σ
  ε := p.ε
  δ := p.δ

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := StochasticConstrainedQuasar.Instance p.toStochastic
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.D ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 < p.δ ∧
    p.δ ≤ 1 / 4 ∧ 100000000 * p.ε ≤ p.L * p.D ^ 2 ∧ (p.σ = 0 ∨ 64 * p.γ * p.ε ≤ p.σ * p.D) ∧
    2 ^ 34 * (⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊ + 1) ^ 5 ≤ p.d
  admissible p I O := StochasticConstrainedQuasar.spec.admissible p.toStochastic I O
  successful p I output P := StochasticConstrainedQuasar.spec.successful p.toStochastic I output P

end LongTails.Setups.HighDimensionalConstrainedQuasar
