import LongTails.Setups.GeneralizedSmoothAndConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.GapGeneralizedSmoothConvex

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  Δ : ℝ
  ε : ℝ

noncomputable abbrev Params.toGeneralized (p : Params) : GeneralizedSmoothAndConvex.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L0 := p.L0, L1 := p.L1, x0 := p.x0,
    R := p.R, Δ := p.Δ, ε := p.ε }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.R ∧ 0 < p.ε ∧
    p.ε ≤ p.L0 * p.R ^ 2 / 16 ∧ 16 * p.ε ≤ p.Δ ∧
    ⌈1208925819614629174706176 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 10⌉₊ ≤ p.d
  admissible p := GeneralizedSmoothAndConvex.spec.admissible p.toGeneralized
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GapGeneralizedSmoothConvex
