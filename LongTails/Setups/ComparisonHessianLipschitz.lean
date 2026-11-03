import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.ComparisonHessianLipschitz

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E × p.E
  Reply _ := Bool
  Output p := List p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ history q seed, O.answer history q seed = decide (f q.2.1 ≤ f q.2.2))
  successful p f output _ := ∀ ω, ∃ x ∈ output ω, ‖gradient f x‖ ≤ p.ε
  allowedAlgorithm p A :=
    ∀ (O : Oracle (p.E × p.E) Bool) (budget : Fin 1 → ℕ) (seed : A.Seed)
      (oracleSeed : (k : ℕ) → O.Seed k),
      ∀ x ∈ (executeWithTrace O A budget seed oracleSeed).1,
        x = p.x0 ∨ ∃ e ∈ (executeWithTrace O A budget seed oracleSeed).2,
          x = e.1.2.1 ∨ x = e.1.2.2

end LongTails.Setups.ComparisonHessianLipschitz
