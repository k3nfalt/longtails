import LongTails.Setups.StochasticTwoSidedPL
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory

namespace LongTails.Setups.StochasticNonconvexPL

open OracleTemplate
open LongTails.Setups.StochasticTwoSidedPL (maxValue minimaxValue)

structure IsJointOracle {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace Ω] (p : Measure Ω)
    (gx : E × F → E) (gy : E × F → F) (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (σ : ℝ)
    [MeasurableSpace E] [MeasurableSpace F] : Prop where
  measurable_x : Measurable (Function.uncurry Gx)
  measurable_y : Measurable (Function.uncurry Gy)
  integrable_x : ∀ w, Integrable (Gx w) p
  integrable_y : ∀ w, Integrable (Gy w) p
  unbiased_x : ∀ w, ∫ ω, Gx w ω ∂p = gx w
  unbiased_y : ∀ w, ∫ ω, Gy w ω ∂p = gy w
  variance_integrable : ∀ w,
    Integrable (fun ω => ‖Gx w ω - gx w‖ ^ 2 + ‖Gy w ω - gy w‖ ^ 2) p
  variance : ∀ w, ∫ ω, (‖Gx w ω - gx w‖ ^ 2 + ‖Gy w ω - gy w‖ ^ 2) ∂p ≤ σ ^ 2

def IsProxPoint {E F : Type*} [NormedAddCommGroup E] (f : E → F → ℝ) (L : ℝ) (z x : E) : Prop :=
  ∀ x', maxValue f x + L * ‖x - z‖ ^ 2 ≤ maxValue f x' + L * ‖x' - z‖ ^ 2

noncomputable def moreauResidual {E F : Type*} [NormedAddCommGroup E] (f : E → F → ℝ) (L : ℝ)
    (z : E) : ℝ :=
  2 * L * Metric.infDist z {x | IsProxPoint f L z x}

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
  μ : ℝ
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
  Query p := p.E × p.F
  Reply p := p.E × p.F
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (gx : q.E × q.F → q.E) (gy : q.E × q.F → q.F) (Gx : q.E × q.F → q.Ω → q.E)
      (Gy : q.E × q.F → q.Ω → q.F) (p : ProbabilityMeasure q.Ω),
      O = { Seed := fun _ => q.Ω
            law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)), inferInstance⟩
            answer := fun _ w ω => (Gx w.2 ω, Gy w.2 ω) } ∧
      (∀ z : q.E × q.F, HasGradientAt (fun x => f x z.2) (gx z) z.1) ∧
      (∀ z : q.E × q.F, HasGradientAt (fun y => f z.1 y) (gy z) z.2) ∧
      (∀ z z' : q.E × q.F, ‖gx z - gx z'‖ ≤ q.L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖)) ∧
      (∀ z z' : q.E × q.F, ‖gy z - gy z'‖ ≤ q.L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖)) ∧
      (∀ x y y', 2 * q.μ * (f x y' - f x y) ≤ ‖gy (x, y)‖ ^ 2) ∧
      (∀ x, ∃ y, ∀ y', f x y' ≤ f x y) ∧
      BddBelow (Set.range (maxValue f)) ∧
      IsJointOracle (p : Measure q.Ω) gx gy Gx Gy q.σ ∧
      2 * maxValue f q.x0 - minimaxValue f - f q.x0 q.y0 + ‖gx (q.x0, q.y0)‖ ^ 2 / q.L ≤ q.Δ
  successful q f output P :=
    Measurable output ∧
    Integrable (fun ω => moreauResidual f q.L (output ω)) (P : Measure _) ∧
    ∫ ω, moreauResidual f q.L (output ω) ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticNonconvexPL
