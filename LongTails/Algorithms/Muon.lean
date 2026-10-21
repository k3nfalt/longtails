import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Gradient.Basic

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
