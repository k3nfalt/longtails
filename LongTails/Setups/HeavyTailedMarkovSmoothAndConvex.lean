import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

open OracleTemplate

noncomputable def pathLaw {Ω : Type} [MeasurableSpace Ω]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (initial : ProbabilityMeasure Ω) :
    ProbabilityMeasure (ℕ → Ω) :=
  ⟨Kernel.trajMeasure (initial : Measure Ω)
    (fun n => κ.comap (fun z : Finset.Iic n → Ω => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      (by fun_prop)), inferInstance⟩

noncomputable def mixingDistance {Ω : Type} [MeasurableSpace Ω]
    (κ : Kernel Ω Ω) (π : ProbabilityMeasure Ω) (t : ℕ) (z : Ω) : ℝ :=
  ⨆ s : {s : Set Ω // MeasurableSet s},
    |((κ ^ t) z s.val).toReal - ((π : Measure Ω) s.val).toReal|

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  R : ℝ
  σ : ℝ
  α : ℝ
  τ : ℝ
  β : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q :=
    0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 < q.τ ∧ 0 < q.β ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (κ : Kernel q.Ω q.Ω) (hκ : IsMarkovKernel κ)
        (π : ProbabilityMeasure q.Ω),
      O = { Seed := fun _ => q.Ω
            law := @pathLaw q.Ω _ κ hκ π
            answer := fun _ (_, x) z => g x z } ∧
      κ ∘ₘ (π : Measure q.Ω) = (π : Measure q.Ω) ∧
      (∀ t, Integrable (mixingDistance κ π t) (π : Measure q.Ω)) ∧
      (∀ t, (∫ z, mixingDistance κ π t z ∂(π : Measure q.Ω)) ≤
        (1 + (t : ℝ) / q.τ) ^ (-q.β)) ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (π : Measure q.Ω)) ∧
      (∀ x, ∫ z, g x z ∂(π : Measure q.Ω) = gradient f x) ∧
      (∀ x, Integrable (fun z => ‖g x z - gradient f x‖ ^ q.α) (π : Measure q.Ω)) ∧
      (∀ x, (∫ z, ‖g x z - gradient f x‖ ^ q.α ∂(π : Measure q.Ω)) ≤ q.σ ^ q.α)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
