import LongTails.Setups.MuonFrobenius
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory Matrix OracleTemplate
open OracleTemplate.Muon
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace LongTails.Setups.AsgoFixedRadius

noncomputable section

namespace Core

def matrixRoot {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := CFC.sqrt A

def gram {m n : ℕ} (X : Mat m n) : Matrix (Fin m) (Fin m) ℝ :=
  toMatrix X * (toMatrix X)ᵀ

def weightedQuadratic {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (X : Mat m n) : ℝ :=
  ((toMatrix X)ᵀ * A * toMatrix X).trace

def loewner {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (B - A).PosSemidef

structure Problem (m n : ℕ) where
  Sample : Type
  sampleSpace : MeasurableSpace Sample
  law : ProbabilityMeasure Sample
  f : Mat m n → ℝ
  H : Mat m n → Mat m n
  loss : Mat m n → Sample → ℝ
  g : Mat m n → Sample → Mat m n
  L : Matrix (Fin m) (Fin m) ℝ
  V : Matrix (Fin m) (Fin m) ℝ

attribute [instance] Problem.sampleSpace

end Core

structure Public where
  m : ℕ
  n : ℕ
  W0 : Mat m n
  R : ℝ
  k : ℝ
  M : ℕ

structure Params extends Public where
  Wstar : Mat m n
  F : ℝ
  ell : ℝ
  v : ℝ
  delta : ℝ

def publicInput (p : Params) : Public := p.toPublic

namespace Core

structure SourceAssumptions {m n : ℕ} (I : Problem m n) (Wstar : Mat m n) : Prop where
  objectiveGradient : ∀ X, HasGradientAt I.f (I.H X) X
  convex : ConvexOn ℝ Set.univ I.f
  minimizer : ∀ X, I.f Wstar ≤ I.f X
  smoothPos : I.L.PosDef
  variancePos : I.V.PosDef
  smoothUpper : ∀ X Y, I.f Y ≤ I.f X + inner ℝ (I.H X) (Y - X) +
    weightedQuadratic I.L (Y - X) / 2
  sampleGradient : ∀ X ξ, HasGradientAt (fun Y => I.loss Y ξ) (I.g X ξ) X
  lossIntegrable : ∀ X, Integrable (I.loss X) I.law.toMeasure
  objectiveIntegral : ∀ X, I.f X = ∫ ξ, I.loss X ξ ∂I.law.toMeasure
  gradientMeasurable : Measurable (Function.uncurry I.g)
  gradientIntegrable : ∀ X, Integrable (I.g X) I.law.toMeasure
  unbiased : ∀ X, (∫ ξ, I.g X ξ ∂I.law.toMeasure) = I.H X
  noiseSquareIntegrable : ∀ X,
    Integrable (fun ξ => ‖I.g X ξ - I.H X‖ ^ 2) I.law.toMeasure
  covariance : ∀ X,
    loewner (∫ ξ, gram (I.g X ξ - I.H X) ∂I.law.toMeasure) (I.V * I.V)

def batchGradient (p : Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) (t : ℕ) (X : Mat p.m p.n) : Mat p.m p.n :=
  (1 / (p.M : ℝ)) • ∑ j ∈ Finset.range p.M, g X (s (t * p.M + j))

def iterationStep (p : Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) (t : ℕ)
    (state : Mat p.m p.n × Matrix (Fin p.m) (Fin p.m) ℝ) :
    Mat p.m p.n × Matrix (Fin p.m) (Fin p.m) ℝ :=
  let G := batchGradient p g s t state.1
  let S := state.2 + gram G
  (state.1 - p.R • ofMatrix ((matrixRoot S + p.k • (1 : Matrix (Fin p.m) (Fin p.m) ℝ))⁻¹ *
    toMatrix G), S)

def trajectory (p : Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) : ℕ → Mat p.m p.n × Matrix (Fin p.m) (Fin p.m) ℝ
  | 0 => (p.W0, 0)
  | t + 1 => iterationStep p g s t (trajectory p g s t)

def point (p : Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) (t : ℕ) : Mat p.m p.n :=
  (trajectory p g s t).1

def accumulator (p : Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) (t : ℕ) : Matrix (Fin p.m) (Fin p.m) ℝ :=
  (trajectory p g s t).2

def RadiusEnvelope (p : Public) {Ξ Ω : Type*} [MeasurableSpace Ω]
    (Wstar : Mat p.m p.n) (F : ℝ) (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (ξ : ℕ → Ω → Ξ) (P : Measure Ω) (T : ℕ) : Prop :=
  0 ≤ F ∧ ∀ᵐ ω ∂P, ∀ t < T,
    spectralNorm (point p g (fun j => ξ j ω) t - Wstar) ≤ p.R ∧
    ‖point p g (fun j => ξ j ω) t - Wstar‖ ≤ F

structure MethodState (p : Public) where
  completed : ℕ
  count : ℕ
  point : Mat p.m p.n
  accumulator : Matrix (Fin p.m) (Fin p.m) ℝ
  batch : Mat p.m p.n
  total : Mat p.m p.n

def methodStep (p : Public) (state : MethodState p) (reply : Mat p.m p.n) :
    MethodState p :=
  let b := state.batch + reply
  if state.count + 1 < p.M then
    { state with count := state.count + 1, batch := b }
  else
    let G := (1 / (p.M : ℝ)) • b
    let S := state.accumulator + gram G
    let W := state.point - p.R •
      ofMatrix ((matrixRoot S + p.k • (1 : Matrix (Fin p.m) (Fin p.m) ℝ))⁻¹ * toMatrix G)
    ⟨state.completed + 1, 0, W, S, 0, state.total + state.point⟩

def method (p : Public) : Algorithm (Mat p.m p.n) (Mat p.m p.n) (Mat p.m p.n) where
  State := MethodState p
  initial _ := ⟨0, 0, p.W0, 0, 0, 0⟩
  query state := (0, state.point)
  update := methodStep p
  output state :=
    if state.completed = 0 then p.W0 else (1 / (state.completed : ℝ)) • state.total

end Core

def horizon (p : Params) : ℕ :=
  ⌈8 * p.R ^ 2 * p.ell / p.delta + 4 * p.k * p.F ^ 2 / (p.R * p.delta) +
    32 * p.R ^ 2 * p.v ^ 2 / ((p.M : ℝ) * p.delta ^ 2)⌉₊ + 1

namespace Core

def OracleExact (p : Public) (I : Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n))
    (decode : (j : ℕ) → O.Seed j → I.Sample) : Prop :=
  ∀ history query seed, O.answer history query seed =
    I.g query.2 (decode history.length seed)

def OracleSamples (p : Public) (I : Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n))
    (decode : (j : ℕ) → O.Seed j → I.Sample) : Prop :=
  (∀ j, Measurable (decode j)) ∧
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun j ω => decode j (ω j)) I.law.toMeasure O.law.toMeasure

end Core

def Valid (p : Params) : Prop :=
  0 < p.R ∧ 0 < p.k ∧ 1 ≤ p.M ∧ 0 ≤ p.F ∧ 0 ≤ p.ell ∧ 0 ≤ p.v ∧ 0 < p.delta

def Admissible (p : Params) (I : Core.Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n)) : Prop :=
  Core.SourceAssumptions I p.Wstar ∧ I.L.trace ≤ p.ell ∧ I.V.trace ≤ p.v ∧
    ∃ decode : (j : ℕ) → O.Seed j → I.Sample,
      Core.OracleExact (publicInput p) I O decode ∧
      Core.OracleSamples (publicInput p) I O decode ∧
      Core.RadiusEnvelope (publicInput p) p.Wstar p.F I.g
        (fun j ω => decode j (ω j)) O.law.toMeasure (horizon p)

def spec : Setup where
  Params := Params
  Public := Public
  Instance p := Core.Problem p.m p.n
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Mat p.m p.n
  publicInput := publicInput
  valid := Valid
  admissible := Admissible
  successful p I result P :=
    Measurable result ∧
    Integrable (fun ω => I.f (result ω) - I.f p.Wstar) P.toMeasure ∧
    (∫ ω, I.f (result ω) - I.f p.Wstar ∂P.toMeasure) ≤ p.delta
  allowedAlgorithm p A := A = Core.method p

end

end LongTails.Setups.AsgoFixedRadius
