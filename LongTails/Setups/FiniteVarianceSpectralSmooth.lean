import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

namespace LongTails.Algorithms.MatrixPolar

abbrev Space (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

instance (m n : ℕ) : MeasurableSpace (Space m n) := borel _

instance (m n : ℕ) : BorelSpace (Space m n) := ⟨rfl⟩

noncomputable def matrixEquiv (m n : ℕ) : Space m n ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun X := fun i j => X (i, j)
  invFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext p; rfl
  right_inv M := rfl

noncomputable def operatorEquiv (m n : ℕ) :
    Space m n ≃L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  ((matrixEquiv m n).trans (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)).toContinuousLinearEquiv

noncomputable def spectralNorm {m n : ℕ} (X : Space m n) : ℝ :=
  ‖operatorEquiv m n X‖

noncomputable def spectralBall (m n : ℕ) : Set (Space m n) :=
  {X | spectralNorm X ≤ 1}

noncomputable def nuclearNorm {m n : ℕ} (X : Space m n) : ℝ :=
  ‖(innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap‖

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def supportFace (K : Set E) (g : E →L[ℝ] ℝ) : Set E :=
  {x | x ∈ K ∧ ∀ y ∈ K, g y ≤ g x}

noncomputable def minimumNormSupport (K : Set E) (g : E →L[ℝ] ℝ) : E :=
  Classical.epsilon (fun x => x ∈ supportFace K g ∧
    ∀ y ∈ supportFace K g, ‖x‖ ≤ ‖y‖)

noncomputable def polar {m n : ℕ} (X : LongTails.Algorithms.MatrixPolar.Space m n) :
    LongTails.Algorithms.MatrixPolar.Space m n :=
  minimumNormSupport (LongTails.Algorithms.MatrixPolar.spectralBall m n) (innerSL ℝ X)

end LongTails.Algorithms.MatrixPolar

namespace LongTails.Setups.FiniteVarianceSpectralSmooth

open MeasureTheory OracleTemplate InnerProductSpace
open LongTails.Algorithms.MatrixPolar

noncomputable def trainingStep {m n : ℕ} (α η : ℝ)
    (state : Space m n × Space m n) (g : Space m n) : Space m n × Space m n :=
  let M := (1 - α) • state.2 + α • g
  (state.1 - η • polar M, M)

noncomputable def representativeIndex {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Fin (k + 1) := by
  classical
  let S := Finset.univ.filter fun i =>
    k + 1 < 2 * (Finset.univ.filter fun j => nuclearNorm (B i - B j) ≤ ρ).card
  exact if h : S.Nonempty then S.min' h else 0

noncomputable def representative {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Space m n := B (representativeIndex ρ B)

noncomputable def bestIndex {m n q : ℕ} (G : Fin (q + 1) → Space m n) : Fin (q + 1) := by
  classical
  let S := Finset.univ.filter fun i => ∀ j, nuclearNorm (G i) ≤ nuclearNorm (G j)
  exact if h : S.Nonempty then S.min' h else 0

noncomputable def muonIterate {m n : ℕ} (α η : ℝ) (x0 : Space m n)
    (reply : ℕ → Space m n) : ℕ → Space m n × Space m n
  | 0 => (x0, 0)
  | t + 1 => trainingStep α η (muonIterate α η x0 reply t) (reply t)

def replyState {Q R U : Type} (A : Algorithm Q R U) (seed : A.Seed) (reply : ℕ → R) : ℕ → A.State
  | 0 => A.initial seed
  | t + 1 => A.update (replyState A seed reply t) (reply t)

def FollowsMuon {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n)
    (A : Algorithm (Space m n) (Space m n) (Space m n)) : Prop :=
  ∃ draw : A.Seed → (Fin (q + 1) → Fin (T + 1)), Measurable draw ∧
    Measure.map draw (A.law : Measure _) =
      (PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure ∧
    ∀ seed reply,
      let state := replyState A seed reply
      let points := fun t : Fin (T + 1) => (muonIterate α η x0 reply t).1
      let sources := fun i => points (draw seed i)
      let offset := fun (i : Fin (q + 1)) (j : Fin (k + 1)) => T + 1 + b * (k + 1) * i + b * j
      (∀ t : Fin (T + 1), (A.query (state t)).2 = points t) ∧
      (∀ i j (u : Fin b), (A.query (state (offset i j + u))).2 = sources i) ∧
      (∀ extra, A.output (state (T + 1 + b * (k + 1) * (q + 1) + extra)) =
        sources (bestIndex (fun i => representative ρ (fun j : Fin (k + 1) =>
          (1 / (b : ℝ)) • ∑ u ∈ Finset.range b, reply (offset i j + u)))))

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

def MuonFamily (p : Public) (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)) : Prop :=
  (2 * p.L * p.Δ ≤ p.ε ^ 2 ∧ ∀ state, A.output state = p.x0) ∨
    ∃ (α η ρ : ℝ) (T b k q : ℕ), 0 < α ∧ α ≤ 1 ∧ 0 < η ∧ 0 < ρ ∧ 0 < b ∧
      FollowsMuon α η ρ T b k q p.x0 A

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
