import LongTails.Algorithms.ManySampleConvolutionalPerceptron
import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
import LongTails.Proofs.ManySampleConvolutionalPerceptronTrajectory

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry

open LongTails.Setups.ManySampleConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronTrajectory

variable {d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

lemma axis_inner (hd : 0 < d) : ⟪axis d, axis d⟫ = 1 := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  simp only [axis, real_inner_smul_left, real_inner_smul_right, inner_ones_ones]
  field_simp [ne_of_gt hs]
  nlinarith

lemma axis_norm (hd : 0 < d) : ‖axis d‖ = 1 := by
  have h := axis_inner hd
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (axis d)]

lemma shift_axis : shift (axis d) = axis d := by
  rw [axis, shift_smul, shift_ones]

lemma axis_shift_inner (u : Features d) : ⟪axis d, shift u⟫ = ⟪axis d, u⟫ := by
  rw [← shift_axis, inner_shift_shift, shift_axis]

noncomputable def plusResidual (G : Geometry D g R μ κ) (i : Fin n) : Features d :=
  (Real.sqrt 2)⁻¹ • (G.defect i + shift (G.defect i))

noncomputable def minusResidual (G : Geometry D g R μ κ) (i : Fin n) : Features d :=
  (Real.sqrt 2)⁻¹ • (G.defect i - shift (G.defect i))

lemma plus_centered (G : Geometry D g R μ κ) (i : Fin n) : ⟪axis d, plusResidual G i⟫ = 0 := by
  simp only [plusResidual, real_inner_smul_right, inner_add_right, axis_shift_inner, G.centered,
    add_zero, mul_zero]

lemma minus_centered (G : Geometry D g R μ κ) (i : Fin n) : ⟪axis d, minusResidual G i⟫ = 0 := by
  simp only [minusResidual, real_inner_smul_right, inner_sub_right, axis_shift_inner,
    sub_self, mul_zero]

lemma plus_norm (G : Geometry D g R μ κ) (i : Fin n) : ‖plusResidual G i‖ ≤ 1 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have he : (Real.sqrt (2 : ℝ))⁻¹ * (2 * (Real.sqrt 2)⁻¹) = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hn := norm_add_le (G.defect i) (shift (G.defect i))
  rw [norm_shift] at hn
  have hb := G.defect_norm i
  have hm := mul_le_mul_of_nonneg_left (show ‖G.defect i + shift (G.defect i)‖ ≤
    2 * (Real.sqrt 2)⁻¹ by linarith) (inv_nonneg.mpr hs.le)
  rw [he] at hm
  simpa only [plusResidual, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] using hm

lemma minus_norm (G : Geometry D g R μ κ) (i : Fin n) : ‖minusResidual G i‖ ≤ 1 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have he : (Real.sqrt (2 : ℝ))⁻¹ * (2 * (Real.sqrt 2)⁻¹) = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hn := norm_sub_le (G.defect i) (shift (G.defect i))
  rw [norm_shift] at hn
  have hb := G.defect_norm i
  have hm := mul_le_mul_of_nonneg_left (show ‖G.defect i - shift (G.defect i)‖ ≤
    2 * (Real.sqrt 2)⁻¹ by linarith) (inv_nonneg.mpr hs.le)
  rw [he] at hm
  simpa only [minusResidual, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] using hm

noncomputable def gains (G : Geometry D g R μ κ) (η σ : ℝ) : Gains (Features d) n where
  reference := η * G.referenceScale
  longitudinal i := η * G.background i
  plus := plusResidual G
  minus := minusResidual G
  contrast := (η * μ) ^ 2
  kick := σ

noncomputable def decode (ε : ℝ) (x : State (Features d)) : Space d :=
  (((x.a + x.t) / Real.sqrt 2, (x.a - x.t) / Real.sqrt 2), x.q • axis d + ε • x.z)

lemma decode_initial (ε : ℝ) : decode (d := d) ε ⟨1, 0, 1, 0⟩ = ((Real.sqrt 2, 0), 0) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num [decode, he]

lemma decode_axis {ε : ℝ} {x : State (Features d)} (hd : 0 < d)
    (hx : ⟪axis d, x.z⟫ = 0) : ⟪axis d, (decode ε x).2⟫ = x.q := by
  simp only [decode, inner_add_right, real_inner_smul_right, axis_inner hd, hx, mul_one,
    mul_zero, add_zero]

noncomputable def plusFeature (b : Features d) : Features d := (Real.sqrt 2)⁻¹ • (b + shift b)
noncomputable def minusFeature (b : Features d) : Features d := (Real.sqrt 2)⁻¹ • (b - shift b)

lemma sample_plus (G : Geometry D g R μ κ) (i : Fin n) :
    plusFeature (D.samples i) = G.background i • axis d + μ • plusResidual G i := by
  have he : (Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2)) = G.background i := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold plusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  calc
    _ = ((Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2))) • axis d +
        μ • ((Real.sqrt 2)⁻¹ • (G.defect i + shift (G.defect i))) := by module
    _ = _ := by rw [he]; rfl

lemma sample_minus (G : Geometry D g R μ κ) (i : Fin n) :
    minusFeature (D.samples i) = μ • minusResidual G i := by
  unfold minusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  unfold minusResidual
  module

lemma reference_plus (G : Geometry D g R μ κ) :
    plusFeature D.reference = G.referenceScale • axis d := by
  have he : (Real.sqrt 2)⁻¹ * (2 * (G.referenceScale / Real.sqrt 2)) = G.referenceScale := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold plusFeature
  rw [G.reference_eq, shift_smul, shift_axis]
  calc
    _ = ((Real.sqrt 2)⁻¹ * (2 * (G.referenceScale / Real.sqrt 2))) • axis d := by module
    _ = _ := by rw [he]

lemma reference_minus (G : Geometry D g R μ κ) : minusFeature D.reference = 0 := by
  simp only [minusFeature, G.reference_eq, shift_smul, shift_axis, sub_self, smul_zero]

lemma margin_decode (b : Features d) (ε : ℝ) (x : State (Features d)) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d b (decode ε x) =
      x.a * ⟪plusFeature b, (decode ε x).2⟫ + x.t * ⟪minusFeature b, (decode ε x).2⟫ := by
  simp only [LongTails.Setups.TwoSampleQuadraticPerceptron.margin, decode, plusFeature,
    minusFeature, real_inner_smul_left, inner_add_left, inner_sub_left]
  ring

lemma plus_decode_inner (G : Geometry D g R μ κ) (i : Fin n) (ε : ℝ) (x : State (Features d)) :
    ⟪plusResidual G i, (decode ε x).2⟫ = ε * ⟪plusResidual G i, x.z⟫ := by
  have hc : ⟪plusResidual G i, axis d⟫ = 0 := by rw [real_inner_comm, plus_centered]
  simp only [decode, inner_add_right, real_inner_smul_right, hc, mul_zero, zero_add]

lemma minus_decode_inner (G : Geometry D g R μ κ) (i : Fin n) (ε : ℝ) (x : State (Features d)) :
    ⟪minusResidual G i, (decode ε x).2⟫ = ε * ⟪minusResidual G i, x.z⟫ := by
  have hc : ⟪minusResidual G i, axis d⟫ = 0 := by rw [real_inner_comm, minus_centered]
  simp only [decode, inner_add_right, real_inner_smul_right, hc, mul_zero, zero_add]

lemma reference_margin (G : Geometry D g R μ κ) {ε : ℝ} {x : State (Features d)}
    (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d D.reference (decode ε x) =
      G.referenceScale * x.a * x.q := by
  rw [margin_decode, reference_plus G, reference_minus G, real_inner_smul_left, decode_axis hd hx]
  simp only [inner_zero_left, mul_zero, add_zero]
  ring

lemma sample_margin (G : Geometry D g R μ κ) {η : ℝ} {x : State (Features d)}
    (i : Fin n) (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    η * LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d (D.samples i) (decode (η * μ) x) =
      (η * G.background i) * x.a * x.q + (η * μ) ^ 2 *
        (x.a * ⟪plusResidual G i, x.z⟫ + x.t * ⟪minusResidual G i, x.z⟫) := by
  rw [margin_decode, sample_plus G i, sample_minus G i, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, decode_axis hd hx,
    plus_decode_inner G i, minus_decode_inner G i]
  ring

lemma direction_decode (b : Features d) (ε : ℝ) (x : State (Features d)) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d b (decode ε x) =
      (((⟪plusFeature b, (decode ε x).2⟫ + ⟪minusFeature b, (decode ε x).2⟫) / Real.sqrt 2,
        (⟪plusFeature b, (decode ε x).2⟫ - ⟪minusFeature b, (decode ε x).2⟫) / Real.sqrt 2),
       x.a • plusFeature b + x.t • minusFeature b) := by
  apply Prod.ext
  · apply Prod.ext
    · change ⟪b, (decode ε x).2⟫ = _
      simp only [plusFeature, minusFeature, real_inner_smul_left, inner_add_left, inner_sub_left]
      field_simp
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
    · change ⟪shift b, (decode ε x).2⟫ = _
      simp only [plusFeature, minusFeature, real_inner_smul_left, inner_add_left, inner_sub_left]
      field_simp
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
  · change ((x.a + x.t) / Real.sqrt 2) • b + ((x.a - x.t) / Real.sqrt 2) • shift b = _
    unfold plusFeature minusFeature
    module

lemma next_centered (G : Geometry D g R μ κ) {η σ : ℝ} {x : State (Features d)}
    (hx : ⟪axis d, x.z⟫ = 0) (e : Option (Fin n)) :
    ⟪axis d, (next (gains G η σ) e x).z⟫ = 0 := by
  cases e with
  | none => exact hx
  | some i =>
    change ⟪axis d, x.z - (x.a • plusResidual G i + x.t • minusResidual G i)⟫ = 0
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hx,
      plus_centered, minus_centered, mul_zero, add_zero, sub_zero]

lemma decode_negative (G : Geometry D g R μ κ) {η : ℝ} {x : State (Features d)}
    (i : Fin n) (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    decode (η * μ) (negative (η * G.background i) ((η * μ) ^ 2)
      (plusResidual G i) (minusResidual G i) x) =
      decode (η * μ) x - η •
        LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d (D.samples i) (decode (η * μ) x) := by
  rw [direction_decode, sample_plus G i, sample_minus G i, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, decode_axis hd hx,
    plus_decode_inner G i, minus_decode_inner G i]
  apply Prod.ext
  · apply Prod.ext <;> simp [decode, negative, smul_eq_mul] <;> ring
  · change (x.q - η * G.background i * x.a) • axis d +
      (η * μ) • (x.z - (x.a • plusResidual G i + x.t • minusResidual G i)) =
      (x.q • axis d + (η * μ) • x.z) -
        η • (x.a • (G.background i • axis d + μ • plusResidual G i) + x.t • (μ • minusResidual G i))
    module

lemma unstable_decode {ε : ℝ} {x : State (Features d)} (hd : 0 < d)
    (hx : ⟪axis d, x.z⟫ = 0) :
    LongTails.Algorithms.ManySampleConvolutionalPerceptron.unstableCoordinate (decode ε x) = x.a + x.q := by
  unfold LongTails.Algorithms.ManySampleConvolutionalPerceptron.unstableCoordinate
  rw [real_inner_comm (axis d) (decode ε x).2, decode_axis hd hx]
  change (((x.a + x.t) / Real.sqrt 2 + (x.a - x.t) / Real.sqrt 2) / Real.sqrt 2) + x.q = _
  field_simp
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

lemma kick_decode {ε σ : ℝ} {x : State (Features d)} (hd : 0 < d)
    (hx : ⟪axis d, x.z⟫ = 0) :
    LongTails.Algorithms.ManySampleConvolutionalPerceptron.referenceKick σ (decode ε x) =
      ((ManySampleConvolutionalPerceptronStability.escapeKick σ (x.a + x.q) / Real.sqrt 2,
        ManySampleConvolutionalPerceptronStability.escapeKick σ (x.a + x.q) / Real.sqrt 2), 0) := by
  unfold LongTails.Algorithms.ManySampleConvolutionalPerceptron.referenceKick
  rw [unstable_decode hd hx]
  rfl

lemma decode_positive (G : Geometry D g R μ κ) {η σ : ℝ} {x : State (Features d)}
    (hd : 0 < d) (hx : ⟪axis d, x.z⟫ = 0) :
    decode (η * μ) (positive (η * G.referenceScale) σ x) =
      decode (η * μ) x + η •
        LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d D.reference (decode (η * μ) x) +
        LongTails.Algorithms.ManySampleConvolutionalPerceptron.referenceKick σ (decode (η * μ) x) := by
  rw [direction_decode, reference_plus G, reference_minus G, real_inner_smul_left,
    decode_axis hd hx, kick_decode hd hx]
  simp only [inner_zero_left, add_zero, sub_zero, smul_zero]
  apply Prod.ext
  · apply Prod.ext <;> simp [decode, positive, smul_eq_mul] <;> ring
  · change (x.q + η * G.referenceScale * x.a) • axis d + (η * μ) • x.z =
      (x.q • axis d + (η * μ) • x.z) + η • (x.a • (G.referenceScale • axis d)) + 0
    module

lemma shift_neg (b : Features d) : shift (-b) = -shift b := by
  simpa using shift_smul (-1) b

lemma margin_neg (b : Features d) (θ : Space d) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d (-b) θ =
      -LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d b θ := by
  simp only [LongTails.Setups.TwoSampleQuadraticPerceptron.margin, shift_neg, inner_neg_left]
  ring

lemma direction_neg (b : Features d) (θ : Space d) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d (-b) θ =
      -LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d b θ := by
  apply Prod.ext
  · apply Prod.ext <;> simp [LongTails.Setups.TwoSampleQuadraticPerceptron.direction, shift_neg]
  · change θ.1.1 • (-b) + θ.1.2 • shift (-b) = -(θ.1.1 • b + θ.1.2 • shift b)
    rw [shift_neg]
    module

end LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
