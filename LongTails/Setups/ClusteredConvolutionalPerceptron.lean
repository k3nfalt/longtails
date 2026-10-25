import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.ClusteredConvolutionalPerceptron

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Space := ManySampleConvolutionalPerceptron.Space
abbrev Reply := ManySampleConvolutionalPerceptron.Reply
noncomputable abbrev axis := ManySampleConvolutionalPerceptron.axis
abbrev Data (d n : ℕ) := Fin (n + 1) → Features d
abbrev Query (d n : ℕ) := Fin (n + 1) × Space d

structure Geometry {d n : ℕ} (D : Data d n) (g R μ κ : ℝ) where
  background : Fin (n + 1) → ℝ
  defect : Fin (n + 1) → Features d
  center : Features d
  sample_eq : ∀ i, D i = (background i / Real.sqrt 2) • axis d + μ • defect i
  background_lower : ∀ i, g ≤ |background i|
  background_upper : ∀ i, |background i| ≤ R
  centered : ∀ i, ⟪axis d, defect i⟫ = 0
  center_norm : ‖center‖ ≤ 1 / 2
  derivative_lower : 2 * κ ≤ ‖(Real.sqrt 2)⁻¹ •
    (center - TwoSampleQuadraticPerceptron.shift center)‖
  cap : ∀ i, ‖defect i - center‖ ≤ κ / 64

noncomputable def answer {d n : ℕ} (D : Data d n) (query : Query d n) : Reply d :=
  ⟨TwoSampleQuadraticPerceptron.margin .conv d (D query.1) query.2,
    TwoSampleQuadraticPerceptron.direction .conv d (D query.1) query.2⟩

def Separates {d n : ℕ} (D : Data d n) (θ : Space d) : Prop :=
  ∀ i, 0 < TwoSampleQuadraticPerceptron.margin .conv d (D i) θ

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
    0 < p.dimension ∧ 0 < p.lower ∧ p.lower ≤ p.upper ∧ 0 < p.contrast ∧
      0 < p.derivativeMargin ∧ p.derivativeMargin ≤ 1 / 4 ∧
      (p.contrast / (4 * p.upper)) ^ 2 ≤
        p.derivativeMargin ^ 2 * (p.lower / (4 * p.upper)) ^ 8 / 4096
  admissible p D oracle :=
    Nonempty (Geometry D p.lower p.upper p.contrast p.derivativeMargin) ∧
    ∀ history query seed, oracle.answer history query seed = answer D query.2
  successful _ D output _ := ∀ ω, Separates D (output ω)

end LongTails.Setups.ClusteredConvolutionalPerceptron
