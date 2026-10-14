import LongTails.Template
import LongTails.Algorithms.StochasticSmoothedAgda
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace LongTails.Setups.StochasticTwoSidedPL

open OracleTemplate

noncomputable def maxValue {E F : Type*} (f : E → F → ℝ) (x : E) : ℝ := ⨆ y, f x y

noncomputable def minimaxValue {E F : Type*} (f : E → F → ℝ) : ℝ := ⨅ x, maxValue f x

structure IsUnbiasedOracle {W V Ω : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace Ω] (p : Measure Ω) (grad : W → V) (oracle : W → Ω → V) (σ : ℝ)
    [MeasurableSpace W] [MeasurableSpace V] : Prop where
  measurable : Measurable (Function.uncurry oracle)
  integrable : ∀ w, Integrable (oracle w) p
  unbiased : ∀ w, ∫ ω, oracle w ω ∂p = grad w
  variance_integrable : ∀ w, Integrable (fun ω => ‖oracle w ω - grad w‖ ^ 2) p
  variance : ∀ w, ∫ ω, ‖oracle w ω - grad w‖ ^ 2 ∂p ≤ σ ^ 2

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  F : Type u
  [normedF : NormedAddCommGroup F]
  [linearF : InnerProductSpace ℝ F]
  [completeF : CompleteSpace F]
  [measurableF : MeasurableSpace F]
  [borelF : BorelSpace F]
  [countableF : SecondCountableTopology F]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  μx : ℝ
  μy : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Params.normedE Params.linearE Params.finiteE Params.measurableE Params.borelE
  Params.normedF Params.linearF Params.completeF Params.measurableF Params.borelF Params.countableF
  Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.F → ℝ
  Query p := (p.E × p.F) ⊕ (p.E × p.F)
  Reply p := p.E ⊕ p.F
  Output p := p.E × p.F
  publicInput p := p
  valid q := 0 < q.μx ∧ q.μx ≤ q.L ∧ 0 < q.μy ∧ q.μy ≤ q.L ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (gx : q.E × q.F → q.E) (gy : q.E × q.F → q.F) (Gx : q.E × q.F → q.Ω → q.E)
      (Gy : q.E × q.F → q.Ω → q.F) (p : ProbabilityMeasure q.Ω),
      O = { Seed := fun _ => q.Ω
            law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)), inferInstance⟩
            answer := fun _ (_, w) ω => Sum.elim (fun z => Sum.inl (Gx z ω)) (fun z => Sum.inr (Gy z ω)) w } ∧
      (∀ z : q.E × q.F, HasGradientAt (fun x => f x z.2) (gx z) z.1) ∧
      (∀ z : q.E × q.F, HasGradientAt (fun y => f z.1 y) (gy z) z.2) ∧
      (∀ z z' : q.E × q.F, ‖gx z - gx z'‖ ≤ q.L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖)) ∧
      (∀ z z' : q.E × q.F, ‖gy z - gy z'‖ ≤ q.L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖)) ∧
      (∀ x x' y, 2 * q.μx * (f x y - f x' y) ≤ ‖gx (x, y)‖ ^ 2) ∧
      (∀ x y y', 2 * q.μy * (f x y' - f x y) ≤ ‖gy (x, y)‖ ^ 2) ∧
      (∀ x, ∃ y, ∀ y', f x y' ≤ f x y) ∧
      IsUnbiasedOracle (p : Measure q.Ω) gx Gx q.σ ∧
      IsUnbiasedOracle (p : Measure q.Ω) gy Gy q.σ ∧
      2 * maxValue f q.x0 - minimaxValue f - f q.x0 q.y0 + ‖gx (q.x0, q.y0)‖ ^ 2 / q.L ≤ q.Δ
  successful q f output P :=
    Measurable output ∧
    Integrable (fun ω => (maxValue f (output ω).1 - minimaxValue f) +
      (maxValue f (output ω).1 - f (output ω).1 (output ω).2)) (P : Measure _) ∧
    ∫ ω, (maxValue f (output ω).1 - minimaxValue f) +
      (maxValue f (output ω).1 - f (output ω).1 (output ω).2) ∂(P : Measure _) ≤ q.ε
  allowedAlgorithm p A := ∃ (r τx τy β : ℝ) (n : ℕ), A = stochasticSmoothedAgda r τx τy β n p.x0 p.y0

end LongTails.Setups.StochasticTwoSidedPL
