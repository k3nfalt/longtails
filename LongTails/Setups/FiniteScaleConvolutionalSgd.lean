import LongTails.Setups.ManySampleConvolutionalPerceptron
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.FiniteScaleConvolutionalSgd

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Space := ManySampleConvolutionalPerceptron.Space
abbrev Reply := ManySampleConvolutionalPerceptron.Reply
noncomputable abbrev axis := ManySampleConvolutionalPerceptron.axis

structure IndexSource (n : ℕ+) where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  law : @ProbabilityMeasure Ω measurableSpace
  sample : ℕ → Ω → Fin n

attribute [instance] IndexSource.measurableSpace

structure Public where
  dimension : ℕ
  count : ℕ+
  lower : ℝ
  upper : ℝ
  contrast : ℝ
  derivativeMargin : ℝ
  initialMean : ℝ
  initialDifference : ℝ
  initialReadout : Features dimension
  sampling : IndexSource count

structure Params where
  input : Public
  failure : ℝ

abbrev Data (p : Public) := Fin p.count → Features p.dimension
abbrev Query (p : Public) := Fin p.count × Space p.dimension

structure Geometry (p : Public) (data : Data p) where
  background : Fin p.count → ℝ
  defect : Fin p.count → Features p.dimension
  separator : Features p.dimension
  sample_eq : ∀ i, data i = (background i / Real.sqrt 2) • axis p.dimension +
    p.contrast • defect i
  background_lower : ∀ i, p.lower ≤ |background i|
  background_upper : ∀ i, |background i| ≤ p.upper
  centered : ∀ i, ⟪axis p.dimension, defect i⟫ = 0
  defect_norm : ∀ i, ‖defect i‖ ≤ (Real.sqrt 2)⁻¹
  separator_unit : ‖separator‖ = 1
  derivative_margin : ∀ i, p.derivativeMargin ≤ ⟪separator,
    (Real.sqrt 2)⁻¹ • (defect i - TwoSampleQuadraticPerceptron.shift (defect i))⟫

noncomputable def answer (p : Public) (data : Data p) (query : Query p) : Reply p.dimension :=
  ⟨TwoSampleQuadraticPerceptron.margin .conv p.dimension (data query.1) query.2,
    TwoSampleQuadraticPerceptron.direction .conv p.dimension (data query.1) query.2⟩

def Separates (p : Public) (data : Data p) (point : Space p.dimension) : Prop :=
  ∀ i, 0 < TwoSampleQuadraticPerceptron.margin .conv p.dimension (data i) point

noncomputable def start (p : Public) (scale : ℝ) : Space p.dimension :=
  ((scale * (p.initialMean + p.initialDifference) / Real.sqrt 2,
    scale * (p.initialMean - p.initialDifference) / Real.sqrt 2), p.initialReadout)

structure ScanState (p : Public) where
  seed : p.sampling.Ω
  point : Space p.dimension
  cursor : Fin p.count
  training : Bool
  violated : Bool
  steps : ℕ
  frozen : Bool

noncomputable def initial (p : Public) (scale : ℝ) (ω : p.sampling.Ω) : ScanState p :=
  ⟨ω, start p scale, ⟨0, p.count.pos⟩, false, false, 0, false⟩

noncomputable def scanQuery (p : Public) (s : ScanState p) : Query p :=
  (if s.training then p.sampling.sample s.steps s.seed else s.cursor, s.point)

noncomputable def scanUpdate (p : Public) (η scale : ℝ) (period : ℕ+)
    (s : ScanState p) (reply : Reply p.dimension) : ScanState p :=
  if s.frozen then s else
    if s.training then
      { s with
        point := if (s.steps + 1) % period = 0 then start p scale else
          s.point + (η / (1 + Real.exp reply.margin)) • reply.direction
        cursor := ⟨0, p.count.pos⟩
        training := false
        violated := false
        steps := s.steps + 1 }
    else
      let violated := s.violated || decide (reply.margin ≤ 0)
      if h : s.cursor.val + 1 < p.count then
        { s with cursor := ⟨_, h⟩, violated := violated }
      else if violated then { s with training := true, violated := true }
      else { s with frozen := true }

def family (p : Public)
    (A : Algorithm (Query p) (Reply p.dimension) (Space p.dimension)) : Prop :=
  ∃ (η scale : ℝ) (period : ℕ+) (seed : A.Seed → p.sampling.Ω)
    (view : A.State → ScanState p),
    0 < η ∧ 0 < scale ∧ Measurable seed ∧
    (A.law : Measure A.Seed).map seed = p.sampling.law ∧
    (∀ ω, view (A.initial ω) = initial p scale (seed ω)) ∧
    (∀ s, A.query s = (0, scanQuery p (view s))) ∧
    (∀ s reply, view (A.update s reply) = scanUpdate p η scale period (view s) reply) ∧
    (∀ s, A.output s = (view s).point)

noncomputable def spec : Setup where
  Params := Params
  Public := Public
  Instance := Data
  Query := Query
  Reply p := Reply p.dimension
  Output p := Space p.dimension
  publicInput := Params.input
  valid p :=
    let q := p.input
    let η := q.derivativeMargin / (1000 * q.upper)
    let δ := (η * q.contrast) ^ 2
    let ρ := η * q.lower
    0 < q.dimension ∧ 0 < q.lower ∧ q.lower ≤ q.upper ∧ 0 < q.contrast ∧
      0 < q.derivativeMargin ∧ q.derivativeMargin ≤ 1 / 4 ∧
      |q.initialMean| ≤ 1 ∧ 1 ≤ q.initialDifference ∧ q.initialDifference ≤ 3 / 2 ∧
      δ ≤ 1 ∧ δ * (Real.log (24 / δ)) ^ 2 ≤
        q.derivativeMargin ^ 3 * ρ ^ 4 / (10 ^ 22 * (q.count : ℝ) ^ 3) ∧
      0 < p.failure ∧ p.failure < 1 ∧
      StochasticGeneralizedSmoothAndConvex.IID q.sampling.sample
        (PMF.uniformOfFintype (Fin q.count)).toMeasure q.sampling.law
  admissible p data oracle :=
    Nonempty (Geometry p.input data) ∧
    ∀ history query seed, oracle.answer history query seed = answer p.input data query.2
  successful p data output law :=
    (law : Measure _) {ω | ¬Separates p.input data (output ω)} ≤ ENNReal.ofReal p.failure
  allowedAlgorithm := family

end LongTails.Setups.FiniteScaleConvolutionalSgd
