import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.FiniteLogisticTwoTap

abbrev Weights (d : ℕ) := EuclideanSpace ℝ (Fin 2 ⊕ Fin d)

structure Params where
  d : ℕ
  μ : ℝ
  r : ℝ
  ρ : ℝ

abbrev Features := TwoSampleQuadraticPerceptron.Features

noncomputable def signedInput {d : ℕ} (μ : ℝ) (i : Fin d) (second : Bool) : Features d :=
  if second then -(TwoSampleQuadraticPerceptron.ones d + μ • EuclideanSpace.single i 1)
  else TwoSampleQuadraticPerceptron.ones d

noncomputable def liftReadout {d : ℕ} (b : Features d) : Weights d :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => b i))

noncomputable def sampleMatrix {d : ℕ} (b : Features d) : Weights d →L[ℝ] Weights d :=
  let c₁ : Weights d := EuclideanSpace.single (.inl 0) 1
  let c₂ : Weights d := EuclideanSpace.single (.inl 1) 1
  let v₁ := liftReadout b
  let v₂ := liftReadout (TwoSampleQuadraticPerceptron.shift b)
  InnerProductSpace.rankOne ℝ c₁ v₁ + InnerProductSpace.rankOne ℝ v₁ c₁ +
    InnerProductSpace.rankOne ℝ c₂ v₂ + InnerProductSpace.rankOne ℝ v₂ c₂

structure Reply (d : ℕ) where
  margin : ℝ
  direction : Weights d

noncomputable def answer {d : ℕ} (b : Features d) (x : Weights d) : Reply d :=
  let g := sampleMatrix b x
  ⟨⟪g, x⟫ / 2, g⟩

noncomputable def loss {d : ℕ} (μ : ℝ) (i : Fin d) (x : Weights d) : ℝ :=
  (Real.log (1 + Real.exp (-(answer (signedInput μ i false) x).margin)) +
   Real.log (1 + Real.exp (-(answer (signedInput μ i true) x).margin))) / 2

def Separates {d : ℕ} (μ : ℝ) (i : Fin d) (x : Weights d) : Prop :=
  0 < (answer (signedInput μ i false) x).margin ∧
  0 < (answer (signedInput μ i true) x).margin

structure State (d : ℕ) where
  point : Weights d
  first : Option (Reply d)

noncomputable def update {d : ℕ} (η : ℝ) (s : State d) (reply : Reply d) : State d :=
  match s.first with
  | none => ⟨s.point, some reply⟩
  | some a =>
    if 0 < a.margin ∧ 0 < reply.margin then ⟨s.point, none⟩
    else ⟨s.point + (η / 2) • (Real.sigmoid (-a.margin) • a.direction +
      Real.sigmoid (-reply.margin) • reply.direction), none⟩

noncomputable def start {d : ℕ} (r : ℝ) (g : Weights d) : Weights d := (r / ‖g‖) • g

def family (p : Params) (A : Algorithm (Bool × Weights p.d) (Reply p.d) (Weights p.d)) : Prop :=
  ∃ (η : ℝ) (seed : A.Seed → Weights p.d) (view : A.State → State p.d),
    0 < η ∧ Measurable seed ∧ (A.law : Measure _).map seed = ProbabilityTheory.stdGaussian _ ∧
    (∀ ω, view (A.initial ω) = ⟨start p.r (seed ω), none⟩) ∧
    (∀ s, A.query s = (0, (view s).first.isSome, (view s).point)) ∧
    (∀ s reply, view (A.update s reply) = update η (view s) reply) ∧
    (∀ s, A.output s = (view s).point)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.d
  Query p := Bool × Weights p.d
  Reply p := Reply p.d
  Output p := Weights p.d
  publicInput := id
  valid p := 3 ≤ p.d ∧ 0 < p.μ ∧ p.μ ≤ 1 / 10 ∧ 0 < p.ρ ∧ p.ρ < 1 ∧ 0 < p.r ∧
    p.r ≤ Real.sqrt (p.μ * p.ρ) * p.ρ / (2 ^ 24 * (p.d : ℝ) ^ 2)
  admissible p i O := ∀ history query seed, O.answer history query seed =
    answer (signedInput p.μ i query.2.1) query.2.2
  successful p i out P := (P : Measure _) {ω | ¬Separates p.μ i (out ω)} ≤ ENNReal.ofReal p.ρ
  allowedAlgorithm := family

end LongTails.Setups.FiniteLogisticTwoTap
