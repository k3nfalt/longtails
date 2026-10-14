import LongTails.Template
import LongTails.Algorithms.ConstantMomentumSgd
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProductMeasure

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate OracleTemplate.MomentumConvex

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ξ : Type
  [measurableΞ : MeasurableSpace Ξ]
  G : ℝ
  R : ℝ
  β : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE
  Params.countableE Params.measurableΞ

structure Model (E Ξ : Type*) [MeasurableSpace Ξ] where
  law : ProbabilityMeasure Ξ
  f : E → ℝ
  grad : Ξ → E → E

noncomputable def scale (G R : ℝ) (N : ℕ) : ℝ :=
  R / (G * ((N : ℝ) + 2) * Real.sqrt ((N : ℝ) + 2))

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Model p.E p.Ξ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  allowedAlgorithm q algorithm :=
    ∃ (γ : ℝ) (N : ℕ), algorithm = constantMomentumSgd q.β γ N q.x0
  publicInput p := p
  valid q := 0 < q.G ∧ 0 ≤ q.R ∧ 0 ≤ q.β ∧ q.β < 1 ∧ 0 < q.ε
  admissible q M O :=
    O = { Seed := fun _ => q.Ξ
          law := ⟨Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)), inferInstance⟩
          answer := fun _ (_, x) ξ => M.grad ξ x } ∧
    Measurable (Function.uncurry M.grad) ∧
    ConvexOn ℝ Set.univ M.f ∧
    (∀ x, Integrable (fun ξ => ‖M.grad ξ x‖ ^ 2) (M.law : Measure q.Ξ)) ∧
    (∀ x, ∫ ξ, ‖M.grad ξ x‖ ^ 2 ∂(M.law : Measure q.Ξ) ≤ q.G ^ 2) ∧
    (∀ x y, M.f x + inner ℝ (∫ ξ, M.grad ξ x ∂(M.law : Measure q.Ξ)) (y - x) ≤ M.f y) ∧
    (∃ xstar, IsMinOn M.f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q M output P :=
    ∃ xstar, IsMinOn M.f Set.univ xstar ∧
      Integrable (fun ω => M.f (output ω) - M.f xstar) (P : Measure _) ∧
      ∫ ω, M.f (output ω) - M.f xstar ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.MomentumLipschitzConvex
