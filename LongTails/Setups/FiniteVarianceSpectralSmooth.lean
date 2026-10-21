import LongTails.Algorithms.ValidatedMuon
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

namespace LongTails.Setups.FiniteVarianceSpectralSmooth

open MeasureTheory OracleTemplate InnerProductSpace
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

structure Public where
  m : ℕ
  n : ℕ
  L : ℝ
  Δ : ℝ
  s : ℝ
  ε : ℝ
  δ : ℝ
  x0 : Space m n

structure GradientModel {m n : ℕ} (f : Space m n → ℝ) (s : ℝ) where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  law : ProbabilityMeasure Ω
  sample : Space m n → Ω → Space m n
  jointly_measurable : Measurable (Function.uncurry sample)
  integrable : ∀ x, Integrable (sample x) (law : Measure Ω)
  unbiased : ∀ x, (∫ ω, sample x ω ∂(law : Measure Ω)) = gradient f x
  row_profile : ∃ (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (σ : Fin m → ℝ),
    (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i) ≤ s ∧ ∀ x i,
      MemLp (fun ω => (operatorEquiv m n (sample x ω - gradient f x)).adjoint (b i)) 2
        (law : Measure Ω) ∧
      (∫ ω, ‖(operatorEquiv m n (sample x ω - gradient f x)).adjoint (b i)‖ ^ 2
        ∂(law : Measure Ω)) ≤ σ i ^ 2

attribute [instance] GradientModel.measurableΩ

def Simulates {Q R U : Type} (A B : Algorithm Q R U) : Prop :=
  ∃ (seedMap : A.Seed → B.Seed) (stateMap : A.State → B.State),
    Measurable seedMap ∧ Measure.map seedMap (A.law : Measure A.Seed) = (B.law : Measure B.Seed) ∧
    (∀ seed, stateMap (A.initial seed) = B.initial (seedMap seed)) ∧
    (∀ state, A.query state = B.query (stateMap state)) ∧
    (∀ state reply, stateMap (A.update state reply) = B.update (stateMap state) reply) ∧
    (∀ state, A.output state = B.output (stateMap state))

def MuonFamily (p : Public) (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)) : Prop :=
  (2 * p.L * p.Δ ≤ p.ε ^ 2 ∧ Simulates A (returnInitial p.x0)) ∨
    ∃ (α η ρ : ℝ) (T b k q : ℕ), 0 < α ∧ α ≤ 1 ∧ 0 < η ∧ 0 < ρ ∧ 0 < b ∧
      Simulates A (validatedMuon α η ρ T b k q p.x0)

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Space p.m p.n → ℝ
  Query p := Space p.m p.n
  Reply p := Space p.m p.n
  Output p := Space p.m p.n
  publicInput p := p
  valid p := 0 ≤ p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.s ∧ 0 < p.ε ∧ 0 < p.δ ∧ p.δ < 1
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ p.L * spectralNorm (x - y)) ∧
    (∃ fmin : ℝ, (∀ x, fmin ≤ f x) ∧ f p.x0 - fmin ≤ p.Δ) ∧
    ∃ (model : GradientModel f p.s) (P : ProbabilityMeasure (ℕ → model.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure model.Ω) (P : Measure _) ∧
      O = { Seed := fun _ => model.Ω
            law := P
            answer := fun _ (_, x) ω => model.sample x ω }
  successful p f output P :=
    Measurable output ∧ (P : Measure _) {ω | p.ε < nuclearNorm (gradient f (output ω))} ≤
      ENNReal.ofReal p.δ
  allowedAlgorithm := MuonFamily

end LongTails.Setups.FiniteVarianceSpectralSmooth
