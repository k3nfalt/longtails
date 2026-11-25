import LongTails.Setups.RhoSmoothRadiusConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.RhoSmoothConvexFull

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  ρ : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  ε : ℝ

noncomputable abbrev Params.toRadius (p : Params) : RhoSmoothRadiusConvex.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L0 := p.L0, L1 := p.L1, ρ := p.ρ, x0 := p.x0,
    R := p.R, ε := p.ε }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 < p.L1 ∧ 1 < p.ρ ∧ p.ρ ≤ 2 ∧ 0 < p.R ∧ 0 < p.ε ∧
    p.ε ≤ p.L0 * p.R ^ 2 / 16 ∧
    ⌈17592186044416 * (1 + (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2 +
      Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6⌉₊ ≤ p.d
  admissible p := RhoSmoothRadiusConvex.spec.admissible p.toRadius
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.RhoSmoothConvexFull
