import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.TwoTapLogisticSeparation

open TwoSampleQuadraticPerceptron

structure Params where
  d : ℕ
  n : ℕ+
  a : ℝ
  b : ℝ
  v : Features d
  R : ℝ
  γ : ℝ
  δ : ℝ

def Params.start (p : Params) : Space .conv p.d := ((p.a,p.b),p.v)

abbrev Data (p : Params) := Fin p.n → Features p.d

noncomputable def loss (m : ℝ) : ℝ := Real.log (1 + Real.exp (-m))

noncomputable def risk (p : Params) (X : Data p) (θ : Space .conv p.d) : ℝ :=
  ∑ i, (p.n : ℝ)⁻¹ * loss (margin .conv p.d (X i) θ)

noncomputable def descent (p : Params) (X : Data p) (θ : Space .conv p.d) :
    Space .conv p.d :=
  ∑ i, ((p.n : ℝ)⁻¹ * Real.sigmoid (-margin .conv p.d (X i) θ)) • direction .conv p.d (X i) θ

noncomputable def surplus (p : Params) : ℝ := p.start.1.1^2+p.start.1.2^2-‖p.start.2‖^2

def Initial (p : Params) (X : Data p) : Prop :=
  risk p X p.start ≤ Real.log 2-p.δ ∨ (risk p X p.start ≤ 1 ∧ p.δ ≤ surplus p)

def Separates (p : Params) (X : Data p) (θ : Space .conv p.d) : Prop :=
  ∀ i, 0 < margin .conv p.d (X i) θ

def family (p : Params)
    (A : Algorithm (Space .conv p.d) (Space .conv p.d) (Space .conv p.d)) : Prop :=
  ∃ (η : ℝ) (point : A.State → Space .conv p.d), 0 < η ∧
    (∀ ω, point (A.initial ω) = p.start) ∧
    (∀ s, A.query s = (0,point s)) ∧
    (∀ s g, point (A.update s g) = point s+η • g) ∧
    (∀ s, A.output s = point s)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  Instance := Data
  Query p := Space .conv p.d
  Reply p := Space .conv p.d
  Output p := Space .conv p.d
  valid p := 0 < p.R ∧ 0 < p.γ ∧ 0 < p.δ
  admissible p X oracle :=
    (∀ i, ‖X i‖ ≤ p.R) ∧
    (∃ u v : Features p.d, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      (∀ i, p.γ ≤ ⟪X i+shift (X i),u⟫) ∧ (∀ i, p.γ ≤ ⟪X i-shift (X i),v⟫)) ∧
    Initial p X ∧
    ∀ k q ω, oracle.answer k q ω = descent p X q.2
  successful p X output _ := ∀ ω, Separates p X (output ω)
  allowedAlgorithm := family

end LongTails.Setups.TwoTapLogisticSeparation
