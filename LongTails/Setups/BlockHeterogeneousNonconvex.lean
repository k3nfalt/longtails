import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.BlockHeterogeneousNonconvex

open OracleTemplate

noncomputable def blockProj {d B : ℕ} (blk : Fin d → Fin B) (j : Fin B) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => if blk i = j then x i else 0)
      map_add' := by
        intro x y
        ext i
        by_cases h : blk i = j <;> simp [h]
      map_smul' := by
        intro a x
        ext i
        by_cases h : blk i = j <;> simp [h] }

structure Params where
  d : ℕ
  B : ℕ
  blk : Fin d → Fin B
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : Fin B → ℝ
  σ : Fin B → ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := (∀ j, 0 < q.L j) ∧ (∀ j, 0 ≤ q.σ j) ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : EuclideanSpace ℝ (Fin q.d) → q.Ω → EuclideanSpace ℝ (Fin q.d))
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, |f y - f x - ⟪gradient f x, y - x⟫| ≤
        (1 / 2) * ∑ j, q.L j * ‖blockProj q.blk j (y - x)‖ ^ 2) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x j, Integrable (fun ω => ‖blockProj q.blk j (g x ω - gradient f x)‖ ^ 2) p) ∧
      (∀ x j, ∫ ω, ‖blockProj q.blk j (g x ω - gradient f x)‖ ^ 2 ∂p ≤ q.σ j ^ 2) ∧
      ∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ∑ j, ‖blockProj q.blk j (gradient f (output ω))‖) (P : Measure _) ∧
      ∫ ω, ∑ j, ‖blockProj q.blk j (gradient f (output ω))‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.BlockHeterogeneousNonconvex
