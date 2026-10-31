import LongTails.Setups.TwoSampleQuadraticPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.ManySampleConvolutionalPerceptron

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Space (d : ℕ) := TwoSampleQuadraticPerceptron.Space .conv d

noncomputable def axis (d : ℕ) : Features d :=
  (Real.sqrt d)⁻¹ • TwoSampleQuadraticPerceptron.ones d

structure Data (d n : ℕ) where
  reference : Features d
  samples : Fin n → Features d

structure Geometry {d n : ℕ} (D : Data d n) (g R μ κ : ℝ) where
  referenceScale : ℝ
  background : Fin n → ℝ
  defect : Fin n → Features d
  separator : Features d
  reference_eq : D.reference = (referenceScale / Real.sqrt 2) • axis d
  sample_eq : ∀ i, D.samples i = (background i / Real.sqrt 2) • axis d + μ • defect i
  reference_lower : g ≤ referenceScale
  reference_upper : referenceScale ≤ R
  background_lower : ∀ i, g ≤ background i
  background_upper : ∀ i, background i ≤ R
  centered : ∀ i, ⟪axis d, defect i⟫ = 0
  defect_norm : ∀ i, ‖defect i‖ ≤ (Real.sqrt 2)⁻¹
  separator_unit : ‖separator‖ = 1
  derivative_margin : ∀ i, κ ≤ -⟪(Real.sqrt 2)⁻¹ •
    (defect i - TwoSampleQuadraticPerceptron.shift (defect i)), separator⟫

structure Reply (d : ℕ) where
  margin : ℝ
  direction : Space d

abbrev Query (d n : ℕ) := Fin (n + 1) × Space d

noncomputable def signedSample {d n : ℕ} (D : Data d n) : Fin (n + 1) → Features d :=
  Fin.cases D.reference (fun i => -D.samples i)

noncomputable def answer {d n : ℕ} (D : Data d n) (query : Query d n) : Reply d :=
  ⟨TwoSampleQuadraticPerceptron.margin .conv d (signedSample D query.1) query.2,
    TwoSampleQuadraticPerceptron.direction .conv d (signedSample D query.1) query.2⟩

def Separates {d n : ℕ} (D : Data d n) (θ : Space d) : Prop :=
  ∀ i, 0 < TwoSampleQuadraticPerceptron.margin .conv d (signedSample D i) θ

structure Params where
  dimension : ℕ
  samples : ℕ
  lower : ℝ
  upper : ℝ
  contrast : ℝ
  derivativeMargin : ℝ

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Data p.dimension p.samples
  Query p := Query p.dimension p.samples
  Reply p := Reply p.dimension
  Output p := Space p.dimension
  publicInput := id
  valid p :=
    let ρ := p.lower / (4 * p.upper)
    let δ := (p.contrast / (4 * p.upper)) ^ 2
    let B := ⌈8 / ρ ^ 2 * Real.log (1 / δ)⌉₊ + 2
    0 < p.dimension ∧ 0 < p.samples ∧ 0 < p.lower ∧ p.lower ≤ p.upper ∧
      0 < p.contrast ∧ 0 < p.derivativeMargin ∧ p.derivativeMargin ≤ 1 ∧
      δ ≤ Real.exp (-1) ∧
      δ * (B + 1 : ℝ) ^ 3 ≤ p.derivativeMargin ^ 3 / 16777216 ∧
      δ * (B + 1 : ℝ) ^ 2 ≤ p.derivativeMargin ^ 2 * ρ ^ 4 / 16777216
  admissible p D oracle :=
    Nonempty (Geometry D p.lower p.upper p.contrast p.derivativeMargin) ∧
    ∀ history query seed, oracle.answer history query seed = answer D query.2
  successful _ D output _ := ∀ ω, Separates D (output ω)

end LongTails.Setups.ManySampleConvolutionalPerceptron
