import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.KernelConvolutionalPerceptron

abbrev Features := TwoSampleQuadraticPerceptron.Features
abbrev Filter (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Space (k d : ℕ) := Filter k × Features d
noncomputable abbrev axis := ManySampleConvolutionalPerceptron.axis
abbrev Data (d n : ℕ) := Fin (n + 1) → Features d
abbrev Query (k d n : ℕ) := Fin (n + 1) × Space k d

noncomputable def shifted {d : ℕ} (j : ℕ) (b : Features d) : Features d :=
  (TwoSampleQuadraticPerceptron.shift)^[j] b

noncomputable def response {k d : ℕ} (c : Filter k) (b : Features d) : Features d :=
  ∑ j : Fin k, c j • shifted j b

noncomputable def margin {k d : ℕ} (b : Features d) (θ : Space k d) : ℝ :=
  ⟪response θ.1 b, θ.2⟫

noncomputable def direction {k d : ℕ} (b : Features d) (θ : Space k d) : Space k d :=
  (WithLp.toLp 2 fun j => ⟪shifted j b, θ.2⟫, response θ.1 b)

noncomputable def highPass (k : ℕ) {d : ℕ} (u : Features d) : Features d :=
  (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ • (u - (k : ℝ)⁻¹ • ∑ j : Fin k, shifted j u)

structure Geometry {d n : ℕ} (k : ℕ) (D : Data d n) (g R μ κ : ℝ) where
  background : Fin (n + 1) → ℝ
  defect : Fin (n + 1) → Features d
  separator : Features d
  sample_eq : ∀ i, D i = (background i / Real.sqrt 2) • axis d + μ • defect i
  background_lower : ∀ i, g ≤ |background i|
  background_upper : ∀ i, |background i| ≤ R
  centered : ∀ i, ⟪axis d, defect i⟫ = 0
  defect_norm : ∀ i, ‖defect i‖ ≤ (Real.sqrt k)⁻¹
  separator_unit : ‖separator‖ = 1
  derivative_margin : ∀ i, κ ≤ ⟪separator, highPass k (defect i)⟫

structure Reply (k d : ℕ) where
  margin : ℝ
  direction : Space k d

noncomputable def answer {k d n : ℕ} (D : Data d n) (query : Query k d n) : Reply k d :=
  ⟨margin (D query.1) query.2, direction (D query.1) query.2⟩

def Separates {k d n : ℕ} (D : Data d n) (θ : Space k d) : Prop :=
  ∀ i, 0 < margin (D i) θ

noncomputable def identityFilter (k d : ℕ) : Space k d :=
  (WithLp.toLp 2 fun j => if j.val = 0 then (1 : ℝ) else 0, 0)

def family {k d n : ℕ} (A : Algorithm (Query k d n) (Reply k d) (Space k d)) : Prop :=
  ∃ (point : A.State → Space k d) (cursor : A.State → Fin (n + 1)) (η : ℝ),
    0 < η ∧
    (∀ seed, point (A.initial seed) = identityFilter k d ∧ cursor (A.initial seed) = 0) ∧
    (∀ s, A.query s = (0, (cursor s, point s))) ∧
    (∀ s r, point (A.update s r) =
      if r.margin ≤ 0 then point s + η • r.direction else point s) ∧
    (∀ s r, cursor (A.update s r) = finRotate (n + 1) (cursor s)) ∧
    (∀ s, A.output s = point s)

structure Params where
  dimension : ℕ
  kernel : ℕ
  samples : ℕ
  lower : ℝ
  upper : ℝ
  contrast : ℝ
  derivativeMargin : ℝ

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Data p.dimension p.samples
  Query p := Query p.kernel p.dimension p.samples
  Reply p := Reply p.kernel p.dimension
  Output p := Space p.kernel p.dimension
  publicInput := id
  valid p :=
    0 < p.dimension ∧ 2 ≤ p.kernel ∧ 0 < p.lower ∧ p.lower ≤ p.upper ∧ 0 < p.contrast ∧
      p.contrast ≤ p.upper ∧ 0 < p.derivativeMargin ∧ p.derivativeMargin ≤ 1 ∧
      p.contrast ^ 2 * (p.upper / p.lower) ^ 4 *
        Real.log (128 * p.kernel * p.upper ^ 2 / (p.derivativeMargin * p.contrast) ^ 2) ^ 2 ≤
        p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 / 10 ^ 13
  admissible p D oracle :=
    Nonempty (Geometry p.kernel D p.lower p.upper p.contrast p.derivativeMargin) ∧
    ∀ history query seed, oracle.answer history query seed = answer D query.2
  successful _ D output _ := ∀ ω, Separates D (output ω)
  allowedAlgorithm _ := family

end LongTails.Setups.KernelConvolutionalPerceptron
