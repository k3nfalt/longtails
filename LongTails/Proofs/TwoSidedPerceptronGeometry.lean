import LongTails.Setups.TwoSidedConvolutionalPerceptron
import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
import LongTails.Proofs.TwoSidedPerceptronDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronGeometry

open LongTails.Setups.TwoSidedConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones margin direction)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry (axis_inner axis_norm shift_axis axis_shift_inner)
open TwoSidedPerceptronDynamics

variable {d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

noncomputable def encode (θ : Space d) : State (Features d) :=
  ⟨(θ.1.1 + θ.1.2) / Real.sqrt 2, ⟪θ.2, axis d⟫, (θ.1.1 - θ.1.2) / Real.sqrt 2,
    θ.2 - ⟪θ.2, axis d⟫ • axis d⟩

noncomputable def plus (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  (Real.sqrt 2)⁻¹ • (G.defect i + shift (G.defect i))

noncomputable def minus (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  derivative (G.defect i)

noncomputable def coeff (G : Geometry D g R μ κ) (η : ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.sqrt 2 * η * G.background i

lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma encode_initial : encode (identityStart d) = ⟨1 / Real.sqrt 2, 0, 1 / Real.sqrt 2, 0⟩ := by
  simp [encode, identityStart]

lemma encode_z_centered (hd : 0 < d) (θ : Space d) : ⟪axis d, (encode θ).z⟫ = 0 := by
  simp only [encode, inner_sub_right, real_inner_smul_right, axis_inner hd, mul_one,
    real_inner_comm (axis d) θ.2, sub_self]

lemma plus_centered (G : Geometry D g R μ κ) (i : Fin (n + 1)) : ⟪axis d, plus G i⟫ = 0 := by
  simp only [plus, real_inner_smul_right, inner_add_right, axis_shift_inner, G.centered,
    add_zero, mul_zero]

lemma minus_centered (G : Geometry D g R μ κ) (i : Fin (n + 1)) : ⟪axis d, minus G i⟫ = 0 := by
  simp only [minus, derivative, real_inner_smul_right, inner_sub_right, axis_shift_inner,
    G.centered, sub_self, mul_zero]

lemma plus_norm (G : Geometry D g R μ κ) (i : Fin (n + 1)) : ‖plus G i‖ ≤ 1 := by
  have hs := sqrt_two_pos
  have he : (Real.sqrt (2 : ℝ))⁻¹ * (2 * (Real.sqrt 2)⁻¹) = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hn := norm_add_le (G.defect i) (shift (G.defect i))
  rw [norm_shift] at hn
  have hb := G.defect_norm i
  have hm := mul_le_mul_of_nonneg_left (show ‖G.defect i + shift (G.defect i)‖ ≤
    2 * (Real.sqrt 2)⁻¹ by linarith) (inv_nonneg.mpr hs.le)
  rw [he] at hm
  simpa only [plus, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] using hm

lemma minus_norm (G : Geometry D g R μ κ) (i : Fin (n + 1)) : ‖minus G i‖ ≤ 1 := by
  have hs := sqrt_two_pos
  have he : (Real.sqrt (2 : ℝ))⁻¹ * (2 * (Real.sqrt 2)⁻¹) = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hn := norm_sub_le (G.defect i) (shift (G.defect i))
  rw [norm_shift] at hn
  have hb := G.defect_norm i
  have hm := mul_le_mul_of_nonneg_left (show ‖G.defect i - shift (G.defect i)‖ ≤
    2 * (Real.sqrt 2)⁻¹ by linarith) (inv_nonneg.mpr hs.le)
  rw [he] at hm
  simpa only [minus, derivative, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] using hm

lemma coeff_abs (G : Geometry D g R μ κ) {η : ℝ} (hη : 0 < η) (i : Fin (n + 1)) :
    |coeff G η i| = Real.sqrt 2 * η * |G.background i| := by
  unfold coeff
  rw [abs_mul, abs_mul, abs_of_pos sqrt_two_pos, abs_of_pos hη]

lemma shift_sample (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    shift (D i) = G.background i • axis d + μ • shift (G.defect i) := by
  rw [G.sample_eq i, shift_add, shift_smul, shift_smul, shift_axis]

lemma encode_a (θ : Space d) : (encode θ).a = (θ.1.1 + θ.1.2) / Real.sqrt 2 := rfl
lemma encode_q (θ : Space d) : (encode θ).q = ⟪θ.2, axis d⟫ := rfl
lemma encode_t (θ : Space d) : (encode θ).t = (θ.1.1 - θ.1.2) / Real.sqrt 2 := rfl
lemma encode_z (θ : Space d) : (encode θ).z = θ.2 - ⟪θ.2, axis d⟫ • axis d := rfl

section Scalars

lemma scale_half (x : ℝ) : x / Real.sqrt 2 * (Real.sqrt 2)⁻¹ = x / 2 := by
  rw [mul_comm, ← div_eq_inv_mul, div_div, sqrt_two_mul_self]

lemma comb_scalar (c₁ c₂ X Y : ℝ) :
    (c₁ + c₂) / Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * (X + Y)) +
      (c₁ - c₂) / Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * (X - Y)) = c₁ * X + c₂ * Y := by
  rw [← mul_assoc, ← mul_assoc, scale_half, scale_half]
  ring

lemma a_scalar (c₁ c₂ η α q μ X Y : ℝ) :
    (c₁ + η * (α * q + μ * X) + (c₂ + η * (α * q + μ * Y))) / Real.sqrt 2 =
      (c₁ + c₂) / Real.sqrt 2 + Real.sqrt 2 * η * α * q +
        η * μ * ((Real.sqrt 2)⁻¹ * (X + Y)) := by
  have hs := sqrt_two_mul_self
  have hs0 := sqrt_two_pos.ne'
  field_simp
  linear_combination (-(η * α * q)) * hs

lemma t_scalar (c₁ c₂ η α q μ X Y : ℝ) :
    (c₁ + η * (α * q + μ * X) - (c₂ + η * (α * q + μ * Y))) / Real.sqrt 2 =
      (c₁ - c₂) / Real.sqrt 2 + η * μ * ((Real.sqrt 2)⁻¹ * (X - Y)) := by
  have hs0 := sqrt_two_pos.ne'
  field_simp
  try ring

lemma q_scalar (c₁ c₂ η α q : ℝ) :
    q + η * (c₁ * α + c₂ * α) = q + Real.sqrt 2 * η * α * ((c₁ + c₂) / Real.sqrt 2) := by
  have hs0 := sqrt_two_pos.ne'
  field_simp
  try ring

lemma margin_scalar (c₁ c₂ α q μ X Y : ℝ) :
    c₁ * (α * q + μ * X) + c₂ * (α * q + μ * Y) =
      Real.sqrt 2 * α * ((c₁ + c₂) / Real.sqrt 2) * q + μ * (c₁ * X + c₂ * Y) := by
  have hs0 := sqrt_two_pos.ne'
  field_simp
  ring

end Scalars

lemma filter_combination (c₁ c₂ : ℝ) (u : Features d) :
    ((c₁ + c₂) / Real.sqrt 2) • ((Real.sqrt 2)⁻¹ • (u + shift u)) +
      ((c₁ - c₂) / Real.sqrt 2) • ((Real.sqrt 2)⁻¹ • (u - shift u)) = c₁ • u + c₂ • shift u := by
  rw [smul_smul, smul_smul, scale_half, scale_half]
  module

lemma inner_sample (hd : 0 < d) (G : Geometry D g R μ κ) (i : Fin (n + 1)) (θ : Space d) :
    ⟪D i, θ.2⟫ = G.background i * (encode θ).q + μ * ⟪G.defect i, (encode θ).z⟫ := by
  have hz : θ.2 = (encode θ).q • axis d + (encode θ).z := by
    simp [encode]
  have hc : ⟪G.defect i, axis d⟫ = 0 := by rw [real_inner_comm]; exact G.centered i
  have hze : ⟪axis d, (encode θ).z⟫ = 0 := encode_z_centered hd θ
  conv_lhs => rw [hz, G.sample_eq i]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    axis_inner hd, hc, hze]
  ring

lemma inner_shift_sample (hd : 0 < d) (G : Geometry D g R μ κ) (i : Fin (n + 1)) (θ : Space d) :
    ⟪shift (D i), θ.2⟫ =
      G.background i * (encode θ).q + μ * ⟪shift (G.defect i), (encode θ).z⟫ := by
  have hz : θ.2 = (encode θ).q • axis d + (encode θ).z := by
    simp [encode]
  have hc : ⟪shift (G.defect i), axis d⟫ = 0 := by
    rw [real_inner_comm, axis_shift_inner]; exact G.centered i
  have hze : ⟪axis d, (encode θ).z⟫ = 0 := encode_z_centered hd θ
  conv_lhs => rw [hz, shift_sample G i]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    axis_inner hd, hc, hze]
  ring

lemma inner_plus (G : Geometry D g R μ κ) (i : Fin (n + 1)) (z : Features d) :
    ⟪plus G i, z⟫ = (Real.sqrt 2)⁻¹ * (⟪G.defect i, z⟫ + ⟪shift (G.defect i), z⟫) := by
  simp only [plus, inner_add_left, real_inner_smul_left]

lemma inner_minus (G : Geometry D g R μ κ) (i : Fin (n + 1)) (z : Features d) :
    ⟪minus G i, z⟫ = (Real.sqrt 2)⁻¹ * (⟪G.defect i, z⟫ - ⟪shift (G.defect i), z⟫) := by
  simp only [minus, derivative, inner_sub_left, real_inner_smul_left]

lemma inner_plus_minus (G : Geometry D g R μ κ) (i : Fin (n + 1)) (θ : Space d) :
    (encode θ).a * ⟪plus G i, (encode θ).z⟫ + (encode θ).t * ⟪minus G i, (encode θ).z⟫ =
      θ.1.1 * ⟪G.defect i, (encode θ).z⟫ + θ.1.2 * ⟪shift (G.defect i), (encode θ).z⟫ := by
  rw [inner_plus, inner_minus, encode_a, encode_t]
  exact comb_scalar _ _ _ _

lemma margin_encode (hd : 0 < d) (G : Geometry D g R μ κ) (i : Fin (n + 1)) (θ : Space d) :
    margin .conv d (D i) θ =
      Real.sqrt 2 * G.background i * (encode θ).a * (encode θ).q +
        μ * ((encode θ).a * ⟪plus G i, (encode θ).z⟫ + (encode θ).t * ⟪minus G i, (encode θ).z⟫) := by
  change θ.1.1 * ⟪D i, θ.2⟫ + θ.1.2 * ⟪shift (D i), θ.2⟫ = _
  rw [inner_sample hd G i θ, inner_shift_sample hd G i θ, inner_plus_minus G i θ, encode_a]
  exact margin_scalar _ _ _ _ _ _ _

lemma margin_encode_scaled (hd : 0 < d) (G : Geometry D g R μ κ) {η : ℝ} (i : Fin (n + 1))
    (θ : Space d) :
    η * margin .conv d (D i) θ =
      TwoSidedPerceptronDynamics.margin (coeff G η i) (η * μ) (plus G i) (minus G i) (encode θ) := by
  rw [margin_encode hd G i θ]
  unfold TwoSidedPerceptronDynamics.margin coeff
  rw [feature_inner]
  ring

lemma inner_sample_axis (hd : 0 < d) (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ⟪D i, axis d⟫ = G.background i := by
  rw [G.sample_eq i, inner_add_left, real_inner_smul_left, real_inner_smul_left, axis_inner hd,
    real_inner_comm, G.centered i]
  ring

lemma inner_shift_sample_axis (hd : 0 < d) (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ⟪shift (D i), axis d⟫ = G.background i := by
  rw [shift_sample G i, inner_add_left, real_inner_smul_left, real_inner_smul_left, axis_inner hd,
    real_inner_comm, axis_shift_inner, G.centered i]
  ring

lemma encode_step (hd : 0 < d) (G : Geometry D g R μ κ) (η : ℝ) (i : Fin (n + 1)) (θ : Space d) :
    encode (θ + η • direction .conv d (D i) θ) =
      step (coeff G η i) (η * μ) (plus G i) (minus G i) (encode θ) := by
  have h1 := inner_sample hd G i θ
  have h2 := inner_shift_sample hd G i θ
  have hA := inner_sample_axis hd G i
  have hA' := inner_shift_sample_axis hd G i
  have hcomb := filter_combination θ.1.1 θ.1.2 (G.defect i)
  set θ' := θ + η • direction .conv d (D i) θ with hθ'
  have hc₁ : θ'.1.1 = θ.1.1 + η * ⟪D i, θ.2⟫ := rfl
  have hc₂ : θ'.1.2 = θ.1.2 + η * ⟪shift (D i), θ.2⟫ := rfl
  have hv : θ'.2 = θ.2 + η • (θ.1.1 • D i + θ.1.2 • shift (D i)) := rfl
  have hq' : ⟪θ'.2, axis d⟫ = (encode θ).q + η * (θ.1.1 * G.background i + θ.1.2 * G.background i) := by
    rw [hv, inner_add_left, real_inner_smul_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hA, hA', encode_q]
  refine State.ext ?_ ?_ ?_ ?_
  · rw [encode_a, hc₁, hc₂, step_a, h1, h2, inner_plus, encode_a]
    unfold coeff
    exact a_scalar _ _ _ _ _ _ _ _
  · rw [encode_q, hq', step_q, encode_a]
    unfold coeff
    exact q_scalar _ _ _ _ _
  · rw [encode_t, hc₁, hc₂, step_t, h1, h2, inner_minus, encode_t]
    exact t_scalar _ _ _ _ _ _ _ _
  · rw [encode_z, hq', step_z, hv, encode_z]
    unfold feature
    rw [encode_a, encode_t]
    simp only [plus, minus, derivative]
    rw [hcomb, shift_sample G i, G.sample_eq i, encode_q]
    module

lemma separates_iff (hd : 0 < d) (G : Geometry D g R μ κ) {η : ℝ} (hη : 0 < η) (θ : Space d) :
    Separates D θ ↔ ∀ i, 0 < TwoSidedPerceptronDynamics.margin (coeff G η i) (η * μ)
      (plus G i) (minus G i) (encode θ) := by
  unfold Separates
  constructor
  · intro h i
    rw [← margin_encode_scaled hd G i θ]
    exact mul_pos hη (h i)
  · intro h i
    have := h i
    rw [← margin_encode_scaled hd G i θ] at this
    exact pos_of_mul_pos_right this hη.le

end LongTails.Proofs.TwoSidedPerceptronGeometry
