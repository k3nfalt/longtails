import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.TwoSidedConvolutionalPerceptron

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Space := ManySampleConvolutionalPerceptron.Space
abbrev Reply := ManySampleConvolutionalPerceptron.Reply
noncomputable abbrev axis := ManySampleConvolutionalPerceptron.axis
abbrev Data (d n : ℕ) := Fin (n + 1) → Features d
abbrev Query (d n : ℕ) := Fin (n + 1) × Space d

noncomputable def derivative {d : ℕ} (u : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (u - TwoSampleQuadraticPerceptron.shift u)

structure Geometry {d n : ℕ} (D : Data d n) (g R μ κ : ℝ) where
  background : Fin (n + 1) → ℝ
  defect : Fin (n + 1) → Features d
  separator : Features d
  sample_eq : ∀ i, D i = background i • axis d + μ • defect i
  background_lower : ∀ i, g ≤ |background i|
  background_upper : ∀ i, |background i| ≤ R
  centered : ∀ i, ⟪axis d, defect i⟫ = 0
  defect_norm : ∀ i, ‖defect i‖ ≤ (Real.sqrt 2)⁻¹
  separator_unit : ‖separator‖ = 1
  derivative_margin : ∀ i, κ ≤ ⟪derivative (defect i), separator⟫

noncomputable def answer {d n : ℕ} (D : Data d n) (query : Query d n) : Reply d :=
  ⟨TwoSampleQuadraticPerceptron.margin .conv d (D query.1) query.2,
    TwoSampleQuadraticPerceptron.direction .conv d (D query.1) query.2⟩

def Separates {d n : ℕ} (D : Data d n) (θ : Space d) : Prop :=
  ∀ i, 0 < TwoSampleQuadraticPerceptron.margin .conv d (D i) θ

noncomputable def identityStart (d : ℕ) : Space d := ((1, 0), 0)

structure Params where
  dimension : ℕ
  samples : ℕ
  lower : ℝ
  upper : ℝ
  contrast : ℝ
  margin : ℝ

def family (p : Params)
    (A : Algorithm (Query p.dimension p.samples) (Reply p.dimension) (Space p.dimension)) :
    Prop :=
  ∃ (point : A.State → Space p.dimension) (index : A.State → Fin (p.samples + 1)) (η : ℝ),
    0 < η ∧
    (∀ seed, point (A.initial seed) = identityStart p.dimension ∧ index (A.initial seed) = 0) ∧
    (∀ s, A.query s = (0, (index s, point s))) ∧
    (∀ s r, point (A.update s r) =
      if r.margin ≤ 0 then point s + η • r.direction else point s) ∧
    (∀ s r, index (A.update s r) = finRotate (p.samples + 1) (index s)) ∧
    (∀ s, A.output s = point s)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Data p.dimension p.samples
  Query p := Query p.dimension p.samples
  Reply p := Reply p.dimension
  Output p := Space p.dimension
  publicInput := id
  valid p :=
    0 < p.dimension ∧ 0 < p.lower ∧ p.lower ≤ p.upper ∧ 0 < p.contrast ∧ 0 < p.margin ∧
      p.margin * p.contrast * ⌈2 ^ 24 * (p.upper / p.lower) ^ 2 *
        (1 + Real.log (1 + p.lower / p.contrast)) / p.margin ^ 3⌉₊ ≤ 3 * p.upper / 2
  admissible p D oracle :=
    Nonempty (Geometry D p.lower p.upper p.contrast p.margin) ∧
    ∀ history query seed, oracle.answer history query seed = answer D query.2
  successful _ D output _ := ∀ ω, Separates D (output ω)
  allowedAlgorithm := family

end LongTails.Setups.TwoSidedConvolutionalPerceptron
