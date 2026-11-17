import LongTails.Setups.RelativeGradientStrongQuasar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalStrongQuasar

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  μ : ℝ
  γ : ℝ
  Δ : ℝ
  ε : ℝ

noncomputable abbrev Params.toRelative (p : Params) :
    LongTails.Setups.RelativeGradientStrongQuasar.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L := p.L, x0 := p.x0, μ := p.μ, γ := p.γ, δ := 0,
    Δ := p.Δ, ε := p.ε }

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid p := 0 < p.L ∧ 0 < p.μ ∧ 0 < p.γ ∧ p.γ ≤ 1 / 256 ∧ 0 < p.ε ∧
    870400 * p.μ ≤ p.L ∧ 4 * p.μ ≤ p.γ ^ 2 * p.L ∧
    1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε ≤ p.Δ ∧
    (Real.sqrt (p.L / p.μ) / p.γ) ^ 5 * (p.Δ / (1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε)) ^ 3 ≤ p.d
  admissible p f O := LongTails.Setups.RelativeGradientStrongQuasar.spec.admissible p.toRelative f O
  successful p f output P :=
    LongTails.Setups.RelativeGradientStrongQuasar.spec.successful p.toRelative f output P

end LongTails.Setups.HighDimensionalStrongQuasar
