import LongTails.Setups.ClusteredConvolutionalPerceptron
import LongTails.Proofs.ClusteredConvolutionalPerceptronHistory
import LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics
import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry

open LongTails.Setups.ClusteredConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry
  (plusFeature minusFeature decode axis_inner axis_shift_inner shift_axis margin_decode direction_decode decode_axis)
open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronHistory

variable {d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

lemma inv_sqrt_two_bound : (Real.sqrt (2 : ℝ))⁻¹ ≤ 3 / 4 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [← one_div]
  apply (div_le_iff₀ hs).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

lemma plus_norm_bound (u : Features d) : ‖plusFeature u‖ ≤ 3 / 2 * ‖u‖ := by
  have hs : 0 < (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  have hn := norm_add_le u (shift u)
  rw [norm_shift] at hn
  have hm := mul_le_mul_of_nonneg_left hn hs.le
  have hb := mul_le_mul_of_nonneg_right inv_sqrt_two_bound (norm_nonneg u)
  simp only [plusFeature, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  nlinarith

lemma minus_norm_bound (u : Features d) : ‖minusFeature u‖ ≤ 3 / 2 * ‖u‖ := by
  have hs : 0 < (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  have hn := norm_sub_le u (shift u)
  rw [norm_shift] at hn
  have hm := mul_le_mul_of_nonneg_left hn hs.le
  have hb := mul_le_mul_of_nonneg_right inv_sqrt_two_bound (norm_nonneg u)
  simp only [minusFeature, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  nlinarith

lemma plus_sub (u v : Features d) : plusFeature (u - v) = plusFeature u - plusFeature v := by
  simp only [plusFeature, shift_sub]
  module

lemma minus_sub (u v : Features d) : minusFeature (u - v) = minusFeature u - minusFeature v := by
  simp only [minusFeature, shift_sub]
  module

lemma center_orthogonal (u : Features d) : ⟪plusFeature u, minusFeature u⟫ = 0 := by
  simp only [plusFeature, minusFeature, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_right, inner_shift_shift]
  rw [real_inner_comm (shift u) u]
  ring

noncomputable def plusResidual (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  plusFeature (G.defect i)

noncomputable def minusResidual (G : Geometry D g R μ κ) (i : Fin (n + 1)) : Features d :=
  minusFeature (G.defect i)

lemma defect_norm (G : Geometry D g R μ κ) (hκ1 : κ ≤ 1 / 4) (i : Fin (n + 1)) :
    ‖G.defect i‖ ≤ 2 / 3 := by
  have hn := norm_add_le (G.defect i - G.center) G.center
  rw [sub_add_cancel] at hn
  linarith [G.cap i, G.center_norm]

lemma plus_norm (G : Geometry D g R μ κ) (hκ1 : κ ≤ 1 / 4) (i : Fin (n + 1)) :
    ‖plusResidual G i‖ ≤ 1 := by
  have hn := plus_norm_bound (G.defect i)
  have hd := defect_norm G hκ1 i
  change ‖plusFeature (G.defect i)‖ ≤ 1
  linarith

lemma minus_norm (G : Geometry D g R μ κ) (hκ1 : κ ≤ 1 / 4) (i : Fin (n + 1)) :
    ‖minusResidual G i‖ ≤ 1 := by
  have hn := minus_norm_bound (G.defect i)
  have hd := defect_norm G hκ1 i
  change ‖minusFeature (G.defect i)‖ ≤ 1
  linarith

lemma plus_close (G : Geometry D g R μ κ) (hκ : 0 < κ) (i : Fin (n + 1)) :
    ‖plusResidual G i - plusFeature G.center‖ ≤ κ / 32 := by
  have hn := plus_norm_bound (G.defect i - G.center)
  rw [plus_sub] at hn
  change ‖plusFeature (G.defect i) - plusFeature G.center‖ ≤ κ / 32
  linarith [G.cap i]

lemma minus_close (G : Geometry D g R μ κ) (hκ : 0 < κ) (i : Fin (n + 1)) :
    ‖minusResidual G i - minusFeature G.center‖ ≤ κ / 32 := by
  have hn := minus_norm_bound (G.defect i - G.center)
  rw [minus_sub] at hn
  change ‖minusFeature (G.defect i) - minusFeature G.center‖ ≤ κ / 32
  linarith [G.cap i]

lemma cross (G : Geometry D g R μ κ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (i j : Fin (n + 1)) : |⟪plusResidual G i, minusResidual G j⟫| ≤ κ / 8 := by
  have hc : ‖plusFeature G.center‖ ≤ 1 := by
    have hn := plus_norm_bound G.center
    linarith [G.center_norm]
  have h := cross_perturbation (plus_close G hκ i) (minus_close G hκ j)
    (minus_norm G hκ1 j) hc (center_orthogonal G.center)
  linarith

lemma gram (G : Geometry D g R μ κ) (hκ : 0 < κ) (i j : Fin (n + 1)) :
    κ ^ 2 ≤ ⟪minusResidual G i, minusResidual G j⟫ := by
  exact cap_gram hκ (minus_close G hκ i) (minus_close G hκ j) G.derivative_lower

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

lemma abstract_geometry (G : Geometry D g R μ κ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (c : ClusteredConvolutionalPerceptronDynamics.Control) {η : ℝ} (hη : 0 ≤ η)
    (he : c.e = κ / 8) (hg : c.g = κ ^ 2) (hρ : c.ρ ≤ η * g) (hR : η * R ≤ 1) :
    ClusteredConvolutionalPerceptronDynamics.Geometry c (fun i => η * G.background i)
      (plusResidual G) (minusResidual G) := by
  constructor
  · intro i
    rw [abs_mul, abs_of_nonneg hη]
    exact hρ.trans (mul_le_mul_of_nonneg_left (G.background_lower i) hη)
  · intro i
    rw [abs_mul, abs_of_nonneg hη]
    exact (mul_le_mul_of_nonneg_left (G.background_upper i) hη).trans hR
  · exact plus_norm G hκ1
  · intro i j
    rw [he]
    exact cross G hκ hκ1 i j
  · intro i j
    rw [hg]
    exact gram G hκ i j

end LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry
