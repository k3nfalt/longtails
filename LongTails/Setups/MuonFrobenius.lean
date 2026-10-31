import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace OracleTemplate.Muon

abbrev Mat (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

def toMatrix {m n : ℕ} (W : Mat m n) : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => W (i, j)

def ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Mat m n := WithLp.toLp 2 (fun ij => A ij.1 ij.2)

noncomputable def gramEigenvalues {m n : ℕ} (W : Mat m n) : Fin n → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvalues

noncomputable def rightSingularVectors {m n : ℕ} (W : Mat m n) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => (Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorBasis i

noncomputable def singularValues {m n : ℕ} (W : Mat m n) : Fin n → ℝ :=
  fun i => Real.sqrt (gramEigenvalues W i)

noncomputable def nuclearNorm {m n : ℕ} (W : Mat m n) : ℝ := ∑ i, singularValues W i

noncomputable def spectralNorm {m n : ℕ} (W : Mat m n) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (toMatrix W))‖

noncomputable def orthogonalize {m n : ℕ} (W : Mat m n) : Mat m n :=
  ofMatrix (∑ i, (if 0 < singularValues W i then (singularValues W i)⁻¹ else 0) •
    Matrix.vecMulVec (Matrix.mulVec (toMatrix W) (rightSingularVectors W i).ofLp) (rightSingularVectors W i).ofLp)

def NuclearStationary {m n : ℕ} (f : Mat m n → ℝ) (W : Mat m n) (ε : ℝ) : Prop :=
  nuclearNorm (gradient f W) ≤ ε

structure Public where
  m : ℕ
  n : ℕ
  η : ℝ
  β : ℝ
  B : ℕ
  T : ℕ
  W0 : Mat m n

structure State (p : Public) where
  iter : ℕ
  count : ℕ
  point : Mat p.m p.n
  momentum : Mat p.m p.n
  batch : Mat p.m p.n
  iterates : ℕ → Mat p.m p.n

noncomputable def step (p : Public) (s : State p) (g : Mat p.m p.n) : State p :=
  if s.count + 1 < p.B then ⟨s.iter, s.count + 1, s.point, s.momentum, s.batch + g, s.iterates⟩
  else
    let G := (1 / (p.B : ℝ)) • (s.batch + g)
    let M := if s.iter = 0 then G else p.β • s.momentum + (1 - p.β) • G
    let W := s.point - p.η • orthogonalize M
    ⟨s.iter + 1, 0, W, M, 0, Function.update s.iterates (s.iter + 1) W⟩

noncomputable def muon (p : Public) :
    Algorithm (Mat p.m p.n) (Mat p.m p.n) (Fin (p.T + 1) → Mat p.m p.n) where
  State := State p
  initial _ := ⟨0, 0, p.W0, 0, 0, fun _ => p.W0⟩
  query s := (0, s.point)
  update := step p
  output s := fun j => s.iterates j

noncomputable def sampleOracle {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat m n → Ω → Mat m n) : Oracle (Mat m n) (Mat m n) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q seed => g q.2 seed

noncomputable def batchGradient (p : Public) {Ω : Type} (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (s : ℕ → Ω) (t : ℕ) (W : Mat p.m p.n) : Mat p.m p.n :=
  (1 / (p.B : ℝ)) • ∑ j ∈ Finset.range p.B, g W (s (t * p.B + j))

noncomputable def iterationStep (p : Public) {Ω : Type} (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (s : ℕ → Ω) (x : ℕ × Mat p.m p.n × Mat p.m p.n) : ℕ × Mat p.m p.n × Mat p.m p.n :=
  let G := batchGradient p g s x.1 x.2.1
  let M := if x.1 = 0 then G else p.β • x.2.2 + (1 - p.β) • G
  (x.1 + 1, x.2.1 - p.η • orthogonalize M, M)

noncomputable def trajectory (p : Public) {Ω : Type} (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (s : ℕ → Ω) (t : ℕ) : ℕ × Mat p.m p.n × Mat p.m p.n :=
  (iterationStep p g s)^[t] (0, p.W0, 0)

attribute [local simp] NuclearStationary toMatrix ofMatrix gramEigenvalues rightSingularVectors singularValues nuclearNorm
  spectralNorm orthogonalize step muon sampleOracle batchGradient iterationStep trajectory

end OracleTemplate.Muon

namespace OracleTemplate.MuonTuning

open OracleTemplate OracleTemplate.Muon

structure Public where
  m : ℕ
  n : ℕ
  L : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  W0 : Mat m n

noncomputable def threshold (p : Public) (C : ℝ) : ℝ :=
  let r : ℝ := (min p.m p.n : ℕ)
  18 ^ 4 * r * C * p.Δ * p.σ ^ 2 / p.ε ^ 4 + 18 ^ 2 * C * p.Δ / p.ε ^ 2 +
    18 ^ 2 * r ^ 2 * p.σ ^ 4 / (C * p.Δ * p.ε ^ 2)

noncomputable def horizon (p : Public) (C : ℝ) : ℕ := ⌈threshold p C⌉₊ + 1

noncomputable def momentum (p : Public) (C : ℝ) : ℝ :=
  1 - (if p.σ = 0 then 1 else
    min (Real.sqrt (C * p.Δ) / (p.σ * Real.sqrt (((min p.m p.n : ℕ) : ℝ) * horizon p C))) 1)

noncomputable def stepSize (p : Public) (C : ℝ) : ℝ :=
  Real.sqrt ((1 - momentum p C) * p.Δ / ((horizon p C : ℝ) * C))

noncomputable def sourceInput (p : Public) (C : ℝ) : OracleTemplate.Muon.Public :=
  ⟨p.m, p.n, stepSize p C, momentum p C, 1, horizon p C, p.W0⟩

noncomputable def randomMuon (q : OracleTemplate.Muon.Public) (N : ℕ) :
    Algorithm (Mat q.m q.n) (Mat q.m q.n) (Mat q.m q.n) where
  Seed := Fin (N + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (N + 1))).toMeasure, inferInstance⟩
  State := OracleTemplate.Muon.State q × Fin (N + 1)
  initial j := ((muon q).initial (), j)
  query st := (muon q).query st.1
  update st G := ((muon q).update st.1 G, st.2)
  output st := st.1.iterates st.2.val

noncomputable def frobenius (p : Public) : Algorithm (Mat p.m p.n) (Mat p.m p.n) (Mat p.m p.n) :=
  randomMuon (sourceInput p (((min p.m p.n : ℕ) : ℝ) * p.L))
    ⌈threshold p (((min p.m p.n : ℕ) : ℝ) * p.L)⌉₊

noncomputable def spectral (p : Public) : Algorithm (Mat p.m p.n) (Mat p.m p.n) (Mat p.m p.n) :=
  randomMuon (sourceInput p p.L) ⌈threshold p p.L⌉₊

attribute [local simp] threshold horizon momentum stepSize sourceInput randomMuon frobenius spectral

end OracleTemplate.MuonTuning

open MeasureTheory

namespace LongTails.Setups.MuonFrobenius

open OracleTemplate OracleTemplate.Muon

structure Constants where
  m : ℕ
  n : ℕ
  L : ℝ
  σ : ℝ
  η : ℝ
  β : ℝ
  B : ℕ
  T : ℕ
  W0 : Mat m n

def publicInput (p : Constants) : Muon.Public := ⟨p.m, p.n, p.η, p.β, p.B, p.T, p.W0⟩

def FrobeniusSmooth {m n : ℕ} (L : ℝ) (f : Mat m n → ℝ) : Prop :=
  (∀ W, HasGradientAt f (gradient f W) W) ∧ ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖

def StochasticOracleModel {m n : ℕ} (f : Mat m n → ℝ) (σ : ℝ) (O : Oracle (Mat m n) (Mat m n)) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat m n → Ω → Mat m n),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
        (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
      LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ ∧
      O = sampleOracle P g

noncomputable def averageNuclear (p : Constants) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : ℝ :=
  (1 / (p.T : ℝ)) * ∑ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P

def Guarantee (p : Constants) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : Prop :=
  let r : ℝ := (min p.m p.n : ℕ)
  let T : ℝ := p.T
  let Δ : ℝ := f p.W0 - ⨅ W, f W
  let avg := averageNuclear p f W P
  (∀ t, Measurable (fun ω => W ω t)) ∧
  (∀ t, Integrable (fun ω => nuclearNorm (gradient f (W ω t))) P) ∧
  (∀ t, Integrable (fun ω => f (W ω t)) P) ∧
  avg ≤ (∫ ω, f (W ω 0) - f (W ω (Fin.last p.T)) ∂P) / (T * p.η) + p.L * r * p.η / 2 +
      2 * p.σ * Real.sqrt (r * (1 - p.β)) / Real.sqrt (p.B * (1 + p.β)) +
      2 * p.β * p.σ * Real.sqrt r / ((1 - p.β) * T * Real.sqrt p.B) +
      2 * r * p.η * p.β * p.L / (1 - p.β) ∧
  (0 < p.L → p.B = 1 → p.η = Real.sqrt ((1 - p.β) * Δ / (r * T * p.L)) →
    1 - p.β = (if p.σ = 0 then 1 else min (Real.sqrt (p.L * Δ) / (p.σ * Real.sqrt T)) 1) →
    avg ≤ 6 * ((r ^ 2 * p.L * Δ * p.σ ^ 2 / T) ^ (1 / 4 : ℝ) + Real.sqrt (r * p.L * Δ / T) +
      Real.sqrt r * p.σ ^ 2 / Real.sqrt (p.L * Δ * T)) ∧
    ∀ ε > 0, 18 ^ 4 * r ^ 2 * p.L * Δ * p.σ ^ 2 / ε ^ 4 + 18 ^ 2 * r * p.L * Δ / ε ^ 2 +
        18 ^ 2 * r * p.σ ^ 4 / (p.L * Δ * ε ^ 2) ≤ T →
      avg ≤ ε ∧ ∃ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P ≤ ε)

def Valid (p : Constants) : Prop :=
  0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.L ∧ 0 ≤ p.σ ∧ 0 < p.η ∧ 0 ≤ p.β ∧ p.β < 1 ∧
    1 ≤ p.B ∧ 1 ≤ p.T

structure Params extends OracleTemplate.MuonTuning.Public

noncomputable abbrev spec : Setup where
  Params := Params
  Public := OracleTemplate.MuonTuning.Public
  Instance p := Mat p.m p.n → ℝ
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Mat p.m p.n
  publicInput := Params.toPublic
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p f O :=
    LongTails.Setups.MuonFrobenius.FrobeniusSmooth p.L f ∧ BddBelow (Set.range f) ∧
    f p.W0 - ⨅ W, f W ≤ p.Δ ∧
    LongTails.Setups.MuonFrobenius.StochasticOracleModel f p.σ O
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => nuclearNorm (gradient f (output ω))) (P : Measure _) ∧
    (∫ ω, nuclearNorm (gradient f (output ω)) ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm p A := A = OracleTemplate.MuonTuning.frobenius p

attribute [local simp] publicInput FrobeniusSmooth StochasticOracleModel averageNuclear Guarantee

end LongTails.Setups.MuonFrobenius
