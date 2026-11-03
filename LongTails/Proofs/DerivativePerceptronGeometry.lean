import LongTails.Setups.DerivativeConvolutionalPerceptron
import LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronGeometry

open LongTails.Setups.DerivativeConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry
  (plusFeature minusFeature decode axis_inner axis_shift_inner shift_axis margin_decode direction_decode decode_axis)
open ManySampleConvolutionalPerceptronDynamics (State)

variable {d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

noncomputable def plusResidual (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  plusFeature (G.defect i)

noncomputable def minusResidual (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  minusFeature (G.defect i)

lemma plus_norm (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ‖plusResidual G i‖ ≤ 1 := by
  have hn := ClusteredConvolutionalPerceptronGeometry.plus_norm_bound (G.defect i)
  have hd := G.defect_norm i
  change ‖plusFeature (G.defect i)‖ ≤ 1
  linarith

lemma minus_norm (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ‖minusResidual G i‖ ≤ 1 := by
  have hn := ClusteredConvolutionalPerceptronGeometry.minus_norm_bound (G.defect i)
  have hd := G.defect_norm i
  change ‖minusFeature (G.defect i)‖ ≤ 1
  linarith

lemma derivative_margin (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    κ ≤ ⟪minusResidual G i, G.separator⟫ := G.derivative_margin i

lemma plus_centered (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ⟪axis d, plusResidual G i⟫ = 0 := by
  simp only [plusResidual, plusFeature, real_inner_smul_right, inner_add_right,
    axis_shift_inner, G.centered, add_zero, mul_zero]

lemma minus_centered (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    ⟪axis d, minusResidual G i⟫ = 0 := by
  simp only [minusResidual, minusFeature, real_inner_smul_right, inner_sub_right,
    axis_shift_inner, sub_self, mul_zero]

lemma sample_plus (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    plusFeature (D i) = G.background i • axis d + μ • plusResidual G i := by
  have he : (Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2)) = G.background i := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold plusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  calc
    _ = ((Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2))) • axis d +
        μ • ((Real.sqrt 2)⁻¹ • (G.defect i + shift (G.defect i))) := by module
    _ = _ := by rw [he]; rfl

lemma sample_minus (G : Geometry D g R μ κ) (i : Fin (n + 1)) :
    minusFeature (D i) = μ • minusResidual G i := by
  unfold minusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  unfold minusResidual minusFeature
  module

lemma plus_decode_inner (G : Geometry D g R μ κ) (i : Fin (n + 1)) (ε : ℝ)
    (x : State (Features d)) : ⟪plusResidual G i, (decode ε x).2⟫ = ε * ⟪plusResidual G i, x.z⟫ := by
  have hc : ⟪plusResidual G i, axis d⟫ = 0 := by rw [real_inner_comm, plus_centered]
  simp only [decode, inner_add_right, real_inner_smul_right, hc, mul_zero, zero_add]

lemma minus_decode_inner (G : Geometry D g R μ κ) (i : Fin (n + 1)) (ε : ℝ)
    (x : State (Features d)) : ⟪minusResidual G i, (decode ε x).2⟫ = ε * ⟪minusResidual G i, x.z⟫ := by
  have hc : ⟪minusResidual G i, axis d⟫ = 0 := by rw [real_inner_comm, minus_centered]
  simp only [decode, inner_add_right, real_inner_smul_right, hc, mul_zero, zero_add]

lemma sample_margin (G : Geometry D g R μ κ) {η : ℝ} {x : State (Features d)}
    (i : Fin (n + 1)) (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    η * LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d (D i) (decode (η * μ) x) =
      (η * G.background i) * x.a * x.q + (η * μ) ^ 2 *
        (x.a * ⟪plusResidual G i, x.z⟫ + x.t * ⟪minusResidual G i, x.z⟫) := by
  rw [margin_decode, sample_plus G i, sample_minus G i, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, decode_axis hd hx,
    plus_decode_inner G i, minus_decode_inner G i]
  ring

lemma next_centered (G : Geometry D g R μ κ) {η : ℝ} {x : State (Features d)}
    (hx : ⟪axis d, x.z⟫ = 0) (i : Fin (n + 1)) :
    ⟪axis d, (ClusteredConvolutionalPerceptronDynamics.step (η * G.background i)
      ((η * μ) ^ 2) (plusResidual G i) (minusResidual G i) x).z⟫ = 0 := by
  simp only [ClusteredConvolutionalPerceptronDynamics.step, inner_add_right,
    real_inner_smul_right, hx, plus_centered, minus_centered, mul_zero, add_zero]

lemma decode_step (G : Geometry D g R μ κ) {η : ℝ} {x : State (Features d)}
    (i : Fin (n + 1)) (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    decode (η * μ) (ClusteredConvolutionalPerceptronDynamics.step (η * G.background i)
      ((η * μ) ^ 2) (plusResidual G i) (minusResidual G i) x) =
      decode (η * μ) x + η •
        LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d (D i) (decode (η * μ) x) := by
  rw [direction_decode, sample_plus G i, sample_minus G i, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, decode_axis hd hx,
    plus_decode_inner G i, minus_decode_inner G i]
  apply Prod.ext
  · apply Prod.ext <;> simp [decode, ClusteredConvolutionalPerceptronDynamics.step, smul_eq_mul] <;> ring
  · change (x.q + η * G.background i * x.a) • axis d +
      (η * μ) • (x.z + x.a • plusResidual G i + x.t • minusResidual G i) =
      (x.q • axis d + (η * μ) • x.z) +
        η • (x.a • (G.background i • axis d + μ • plusResidual G i) + x.t • (μ • minusResidual G i))
    module

end LongTails.Proofs.DerivativePerceptronGeometry
