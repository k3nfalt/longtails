import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.TwoSampleQuadraticPerceptron

inductive Model where
  | twoLayer
  | conv

abbrev Features (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Space : Model → ℕ → Type
  | .twoLayer, d => Features d × ℝ
  | .conv, d => (ℝ × ℝ) × Features d

noncomputable def shift {d : ℕ} (x : Features d) : Features d :=
  WithLp.toLp 2 fun i => x ((finRotate d).symm i)

noncomputable def ones (d : ℕ) : Features d := WithLp.toLp 2 fun _ => 1

noncomputable def margin : (m : Model) → (d : ℕ) → Features d → Space m d → ℝ
  | .twoLayer, _, b, θ => ⟪θ.1, b⟫ * θ.2
  | .conv, _, b, θ => θ.1.1 * ⟪b, θ.2⟫ + θ.1.2 * ⟪shift b, θ.2⟫

noncomputable def direction : (m : Model) → (d : ℕ) → Features d → Space m d → Space m d
  | .twoLayer, _, b, θ => (θ.2 • b, ⟪θ.1, b⟫)
  | .conv, _, b, θ => ((⟪b, θ.2⟫, ⟪shift b, θ.2⟫), θ.1.1 • b + θ.1.2 • shift b)

noncomputable def move : (m : Model) → (d : ℕ) → Space m d → ℝ → Space m d → Space m d
  | .twoLayer, _, θ, γ, g => θ + γ • g
  | .conv, _, θ, γ, g => θ + γ • g

noncomputable def negate : (m : Model) → (d : ℕ) → Space m d → Space m d
  | .twoLayer, _, g => -g
  | .conv, _, g => -g

structure Data (d : ℕ) where
  positive : Features d
  negative : Features d

structure Reply (m : Model) (d : ℕ) where
  first : ℝ
  firstDirection : Space m d
  second : ℝ
  secondDirection : Space m d

noncomputable def answer (m : Model) (d : ℕ) (D : Data d) (θ : Space m d) : Reply m d where
  first := margin m d D.positive θ
  firstDirection := direction m d D.positive θ
  second := -margin m d D.negative θ
  secondDirection := negate m d (direction m d D.negative θ)

def Separates (m : Model) (d : ℕ) (D : Data d) (θ : Space m d) : Prop :=
  0 < margin m d D.positive θ ∧ 0 < -margin m d D.negative θ

noncomputable def axisA (d : ℕ) (D : Data d) : Features d := ‖D.positive‖⁻¹ • D.positive

noncomputable def normalPart (d : ℕ) (D : Data d) : Features d :=
  D.negative - ⟪D.negative, axisA d D⟫ • axisA d D

noncomputable def axisB (d : ℕ) (D : Data d) : Features d := ‖normalPart d D‖⁻¹ • normalPart d D

noncomputable def level (d : ℕ) (x : Features d) : ℝ := ⟪x, ones d⟫ / d

noncomputable def detrended (d : ℕ) (D : Data d) : Features d :=
  D.negative - level d D.negative • ones d

noncomputable def smooth (d : ℕ) (D : Data d) : Features d := detrended d D + shift (detrended d D)

noncomputable def rough (d : ℕ) (D : Data d) : Features d := detrended d D - shift (detrended d D)

structure Coordinates where
  p : ℝ
  q : ℝ
  z : ℝ
  r : ℝ
  y : ℝ

noncomputable def coordinates : (m : Model) → (d : ℕ) → Data d → Space m d → Coordinates
  | .twoLayer, d, D, θ =>
      ⟨θ.2, ⟪θ.1, axisA d D⟫, ⟪θ.1, axisB d D⟫, 0, 0⟩
  | .conv, d, D, θ =>
      ⟨(θ.1.1 + θ.1.2) / Real.sqrt 2, ⟪θ.2, ones d⟫ / Real.sqrt d,
        ⟪θ.2, smooth d D⟫ / ‖smooth d D‖, (θ.1.1 - θ.1.2) / Real.sqrt 2,
        ⟪θ.2, rough d D⟫ / ‖rough d D‖⟩

structure Spectrum where
  first : ℝ
  second : ℝ
  coupling : ℝ
  slow : ℝ

noncomputable def eigenvalues : (m : Model) → (d : ℕ) → Data d → Spectrum
  | .twoLayer, d, D => ⟨‖D.positive‖, ⟪D.negative, axisA d D⟫, ‖normalPart d D‖, 0⟩
  | .conv, d, D => ⟨level d D.positive * Real.sqrt (2 * d), level d D.negative * Real.sqrt (2 * d),
      ‖smooth d D‖ / Real.sqrt 2, ‖rough d D‖ / Real.sqrt 2⟩

def InClass : (m : Model) → (d : ℕ) → Data d → Prop
  | .twoLayer, d, D => 0 < ⟪D.positive, D.negative⟫ ∧ normalPart d D ≠ 0
  | .conv, d, D => D.positive = level d D.positive • ones d ∧ 0 < level d D.positive ∧
      0 < level d D.negative ∧ smooth d D ≠ 0

structure Params where
  model : Model
  dimension : ℕ
  radius : ℝ
  start : Space model dimension
  gain : ℝ
  couplingLower : ℝ
  couplingUpper : ℝ
  slowLower : ℝ
  ratio : ℝ
  wedgeLower : ℝ
  depthLower : ℝ
  size : ℝ

structure Public where
  model : Model
  dimension : ℕ
  radius : ℝ
  start : Space model dimension

def publicOf (p : Params) : Public := ⟨p.model, p.dimension, p.radius, p.start⟩

def family (P : Public) (A : Algorithm (Space P.model P.dimension) (Reply P.model P.dimension)
    (Space P.model P.dimension)) : Prop :=
  ∃ (point : A.State → Space P.model P.dimension) (γ : ℝ), 0 < γ ∧
    (∀ seed, point (A.initial seed) = P.start) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) =
      if reply.first ≤ 0 then move P.model P.dimension (point state) γ reply.firstDirection
      else if reply.second ≤ 0 then move P.model P.dimension (point state) γ reply.secondDirection
      else point state) ∧
    (∀ state, A.output state = point state)

noncomputable def spec : Setup where
  Params := Params
  Public := Public
  Instance P := Data P.dimension
  Query P := Space P.model P.dimension
  Reply P := Reply P.model P.dimension
  Output P := Space P.model P.dimension
  publicInput := publicOf
  valid p := 0 < p.radius ∧ 0 < p.gain ∧ 0 < p.couplingLower ∧ p.couplingLower ≤ p.couplingUpper ∧
    0 < p.slowLower ∧ 1 ≤ p.ratio ∧ 0 < p.wedgeLower ∧ 0 < p.depthLower ∧ 0 < p.size
  admissible p D oracle :=
    let c := coordinates p.model p.dimension D p.start
    let s := eigenvalues p.model p.dimension D
    let σ := -(SignType.sign c.z : ℝ)
    InClass p.model p.dimension D ∧ ‖D.positive‖ ≤ p.radius ∧ ‖D.negative‖ ≤ p.radius ∧
    p.gain ≤ s.first ∧ p.gain ≤ s.second ∧
    p.couplingLower ≤ s.coupling ∧ s.coupling ≤ p.couplingUpper ∧
    (p.model = .conv → p.slowLower ≤ s.slow) ∧
    |c.r + c.y| ≤ p.ratio * |c.r - c.y| ∧
    p.depthLower ≤ |c.z| ∧ p.wedgeLower ≤ σ * (c.p + c.q) ∧ 0 ≤ σ * (c.p - c.q) ∧
    2 * σ * c.p + 2 * |c.z| ≤ p.size ∧
    ∀ k query seed, oracle.answer k query seed = answer p.model p.dimension D query.2
  successful p D output _ := ∀ ω, Separates p.model p.dimension D (output ω)
  allowedAlgorithm := family

end LongTails.Setups.TwoSampleQuadraticPerceptron
