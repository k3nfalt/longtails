import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.CyclicFullWidthPerceptron

abbrev Features (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[ext]
structure Space (d : ℕ) where
  a : ℝ
  row : Features d
  column : Features d
  matrix : Features d →L[ℝ] Features d
  b : ℝ
  head : Features d

abbrev Input (d : ℕ) := ℝ × Features d

noncomputable def linearPart {d : ℕ} (θ : Space d) (q : Input d) : Input d :=
  (θ.a * q.1 + ⟪θ.row, q.2⟫, q.1 • θ.column + θ.matrix q.2)

noncomputable def move {d : ℕ} (θ : Space d) (η : ℝ) (g : Space d) : Space d :=
  ⟨θ.a + η * g.a, θ.row + η • g.row, θ.column + η • g.column,
    θ.matrix + η • g.matrix, θ.b + η * g.b, θ.head + η • g.head⟩

structure Params where
  dimension : ℕ
  count : ℕ
  κ : ℝ
  μ : ℝ
  ν : ℝ

structure Data (d n : ℕ) where
  residual : Fin n → Features d
  offset : Fin n → ℝ

noncomputable def sample (p : Params) (D : Data p.dimension p.count) :
    Fin (p.count + 1) → Input p.dimension :=
  Fin.cases (1, 0) (fun i => (-(1 + D.offset i), -p.μ • D.residual i))

noncomputable def margin {d : ℕ} (q : Input d) (θ : Space d) : ℝ :=
  θ.b * (linearPart θ q).1 + ⟪θ.head, (linearPart θ q).2⟫

noncomputable def direction {d : ℕ} (q : Input d) (θ : Space d) : Space d :=
  ⟨θ.b * q.1, θ.b • q.2, q.1 • θ.head, InnerProductSpace.rankOne ℝ θ.head q.2,
    (linearPart θ q).1, (linearPart θ q).2⟩

structure Reply (d : ℕ) where
  value : ℝ
  direction : Space d

noncomputable def answer (p : Params) (D : Data p.dimension p.count)
    (q : Fin (p.count + 1) × Space p.dimension) : Reply p.dimension :=
  ⟨margin (sample p D q.1) q.2, direction (sample p D q.1) q.2⟩

def Geometry (p : Params) (D : Data p.dimension p.count) : Prop :=
  (∀ i, 0 ≤ D.offset i ∧ D.offset i ≤ p.ν) ∧
    (∀ i, ‖D.residual i‖ ≤ 1) ∧
    ∃ w : Features p.dimension, ‖w‖ = 1 ∧ ∀ i, p.κ ≤ ⟪w, D.residual i⟫

def Separates (p : Params) (D : Data p.dimension p.count) (θ : Space p.dimension) : Prop :=
  ∀ i, 0 < margin (sample p D i) θ

noncomputable def initial (d : ℕ) : Space d := ⟨1, 0, 0, ContinuousLinearMap.id ℝ _, 0, 0⟩

def family (p : Params)
    (A : Algorithm (Fin (p.count + 1) × Space p.dimension) (Reply p.dimension)
      (Space p.dimension)) : Prop :=
  ∃ (point : A.State → Space p.dimension) (index : A.State → Fin (p.count + 1)) (η : ℝ),
    0 < η ∧
    (∀ seed, point (A.initial seed) = initial p.dimension ∧ index (A.initial seed) = 0) ∧
    (∀ s, A.query s = (0, (index s, point s))) ∧
    (∀ s r, point (A.update s r) =
      if r.value ≤ 0 then move (point s) η r.direction else point s) ∧
    (∀ s r, index (A.update s r) = finRotate (p.count + 1) (index s)) ∧
    (∀ s, A.output s = point s)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Data p.dimension p.count
  Query p := Fin (p.count + 1) × Space p.dimension
  Reply p := Reply p.dimension
  Output p := Space p.dimension
  publicInput := id
  valid p := 0 < p.count ∧ 0 < p.κ ∧ p.κ ≤ 1 ∧ 0 < p.μ ∧
    p.μ ≤ p.κ ^ 4 / 2 ^ 20 ∧ 0 ≤ p.ν ∧ p.ν ≤ p.κ ^ 12 * p.μ ^ 2 / 2 ^ 56
  admissible p D oracle := Geometry p D ∧
    ∀ history query seed, oracle.answer history query seed = answer p D query.2
  successful p D output _ := ∀ ω, Separates p D (output ω)
  allowedAlgorithm := family

end LongTails.Setups.CyclicFullWidthPerceptron
