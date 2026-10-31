import LongTails.Setups.TwoSampleQuadraticPerceptron
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.NoisyBatchQuadraticPerceptron

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Weights (d : ℕ) := WithLp 2 (Features d × ℝ)

structure NoiseSource (d : ℕ) where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  law : @ProbabilityMeasure Ω measurableSpace
  sample : ℕ → Ω → Weights d

attribute [instance] NoiseSource.measurableSpace

structure Public where
  dimension : ℕ
  count : ℕ+
  radius : ℝ
  margin : ℝ
  noiseScale : ℝ
  start : Weights dimension
  noise : NoiseSource dimension

structure Params where
  input : Public
  failure : ℝ

abbrev Data (P : Public) := Fin P.count → Features P.dimension
abbrev Query (P : Public) := Fin P.count × Weights P.dimension

structure Reply (d : ℕ) where
  margin : ℝ
  direction : Weights d

noncomputable def answer {d : ℕ} (a : Features d) (w : Weights d) : Reply d where
  margin := w.ofLp.2 * ⟪a, w.ofLp.1⟫
  direction := WithLp.toLp 2 (w.ofLp.2 • a, ⟪a, w.ofLp.1⟫)

def Separates {P : Public} (data : Data P) (w : Weights P.dimension) : Prop :=
  ∀ i, 0 < w.ofLp.2 * ⟪data i, w.ofLp.1⟫

structure ScanState (P : Public) where
  seed : P.noise.Ω
  point : Weights P.dimension
  accumulator : Weights P.dimension
  violated : Bool
  cursor : Fin P.count
  batch : ℕ
  frozen : Bool

noncomputable def initial (P : Public) (ω : P.noise.Ω) : ScanState P :=
  ⟨ω, P.start, 0, false, ⟨0, P.count.pos⟩, 0, false⟩

noncomputable def scanUpdate (P : Public) (η : ℝ) (s : ScanState P)
    (reply : Reply P.dimension) : ScanState P :=
  if s.frozen then s else
    let wrong := decide (reply.margin ≤ 0)
    let accumulator := s.accumulator + if wrong then reply.direction else 0
    let violated := s.violated || wrong
    if h : s.cursor.val + 1 < P.count then
      { s with accumulator := accumulator, violated := violated, cursor := ⟨_, h⟩ }
    else if violated then
      { s with
        point := s.point + (η / (P.count : ℝ)) • accumulator +
          P.noiseScale • P.noise.sample s.batch s.seed
        accumulator := 0
        violated := false
        cursor := ⟨0, P.count.pos⟩
        batch := s.batch + 1 }
    else { s with frozen := true }

def family (P : Public)
    (A : Algorithm (Query P) (Reply P.dimension) (Weights P.dimension)) : Prop :=
  ∃ (η : ℝ) (seed : A.Seed → P.noise.Ω) (view : A.State → ScanState P),
    0 < η ∧ Measurable seed ∧ (A.law : Measure A.Seed).map seed = P.noise.law ∧
    (∀ ω, view (A.initial ω) = initial P (seed ω)) ∧
    (∀ s, A.query s = (0, (view s).cursor, (view s).point)) ∧
    (∀ s reply, view (A.update s reply) = scanUpdate P η (view s) reply) ∧
    (∀ s, A.output s = (view s).point)

noncomputable def spec : Setup where
  Params := Params
  Public := Public
  Instance := Data
  Query := Query
  Reply P := Reply P.dimension
  Output P := Weights P.dimension
  publicInput := Params.input
  valid p := 0 < p.input.margin ∧ p.input.margin ≤ p.input.radius ∧
    0 < p.input.noiseScale ∧ 0 < p.failure ∧ p.failure < 1 ∧
    StochasticGeneralizedSmoothAndConvex.IID p.input.noise.sample
      (ProbabilityTheory.stdGaussian (Weights p.input.dimension)) p.input.noise.law
  admissible p data oracle :=
    (∃ u : Features p.input.dimension, ‖u‖ = 1 ∧
      ∀ i, ‖data i‖ ≤ p.input.radius ∧ p.input.margin ≤ ⟪u, data i⟫) ∧
    ∀ history query seed, oracle.answer history query seed = answer (data query.2.1) query.2.2
  successful p data output law :=
    (law : Measure _) {ω | ¬Separates data (output ω)} ≤ ENNReal.ofReal p.failure
  allowedAlgorithm := family

end LongTails.Setups.NoisyBatchQuadraticPerceptron
