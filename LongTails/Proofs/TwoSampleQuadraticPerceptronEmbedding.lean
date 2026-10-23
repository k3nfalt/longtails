import LongTails.Setups.TwoSampleQuadraticPerceptron

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open LongTails.Setups.TwoSampleQuadraticPerceptron

lemma inner_eq_sum {d : ℕ} (x y : Features d) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

lemma shift_apply {d : ℕ} (x : Features d) (i : Fin d) : shift x i = x ((finRotate d).symm i) := rfl

lemma ones_apply {d : ℕ} (i : Fin d) : ones d i = 1 := rfl

lemma inner_shift_shift {d : ℕ} (x y : Features d) : ⟪shift x, shift y⟫ = ⟪x, y⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  simp only [shift_apply]
  exact Equiv.sum_comp (finRotate d).symm (fun j => x j * y j)

lemma shift_ones (d : ℕ) : shift (ones d) = ones d := by
  ext i; rfl

lemma inner_shift_ones {d : ℕ} (x : Features d) : ⟪shift x, ones d⟫ = ⟪x, ones d⟫ := by
  rw [← inner_shift_shift x (ones d), shift_ones]

lemma shift_add {d : ℕ} (x y : Features d) : shift (x + y) = shift x + shift y := by
  ext i; simp [shift_apply]

lemma shift_smul {d : ℕ} (a : ℝ) (x : Features d) : shift (a • x) = a • shift x := by
  ext i; simp [shift_apply]

lemma shift_sub {d : ℕ} (x y : Features d) : shift (x - y) = shift x - shift y := by
  ext i; simp [shift_apply]

lemma norm_shift {d : ℕ} (x : Features d) : ‖shift x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_shift_shift]

lemma inner_ones_ones (d : ℕ) : ⟪ones d, ones d⟫ = d := by
  rw [inner_eq_sum]; simp [ones_apply]

lemma inner_eq_norm_mul_coord {d : ℕ} (x v : Features d) : ⟪x, v⟫ = ‖x‖ * (⟪v, x⟫ / ‖x‖) := by
  by_cases hx : x = 0
  · simp [hx]
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [real_inner_comm]; field_simp

section TwoLayer

variable {d : ℕ} (D : Data d)

lemma positive_eq (h : D.positive ≠ 0) : D.positive = ‖D.positive‖ • axisA d D := by
  unfold axisA
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

lemma inner_axisA_self (h : D.positive ≠ 0) : ⟪axisA d D, axisA d D⟫ = 1 := by
  unfold axisA
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖D.positive‖ ≠ 0 := norm_ne_zero_iff.mpr h
  field_simp

lemma inner_normalPart_axisA (h : D.positive ≠ 0) : ⟪normalPart d D, axisA d D⟫ = 0 := by
  unfold normalPart
  rw [inner_sub_left, real_inner_smul_left, inner_axisA_self D h]; ring

lemma inner_axisB_axisA (h : D.positive ≠ 0) : ⟪axisB d D, axisA d D⟫ = 0 := by
  unfold axisB; rw [real_inner_smul_left, inner_normalPart_axisA D h, mul_zero]

lemma negative_eq :
    D.negative = ⟪D.negative, axisA d D⟫ • axisA d D + ‖normalPart d D‖ • axisB d D := by
  by_cases hr : normalPart d D = 0
  · have : D.negative = ⟪D.negative, axisA d D⟫ • axisA d D := by
      have := hr; unfold normalPart at this; exact sub_eq_zero.mp this
    rw [hr]; simpa using this
  · unfold axisB
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr), one_smul]
    unfold normalPart; abel

lemma inner_positive_axisB (h : D.positive ≠ 0) : ⟪D.positive, axisB d D⟫ = 0 := by
  rw [positive_eq D h, real_inner_smul_left, real_inner_comm, inner_axisB_axisA D h, mul_zero]

lemma inner_negative_axisB : ⟪D.negative, axisB d D⟫ = ‖normalPart d D‖ := by
  by_cases hr : normalPart d D = 0
  · simp [axisB, hr]
  · have hD : D.negative = normalPart d D + ⟪D.negative, axisA d D⟫ • axisA d D := by
      unfold normalPart; abel
    have hn : ‖normalPart d D‖ ≠ 0 := norm_ne_zero_iff.mpr hr
    unfold axisB
    rw [real_inner_smul_right]
    conv_lhs => rw [hD]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have : ⟪axisA d D, normalPart d D⟫ = 0 := by
      by_cases hp : D.positive = 0
      · simp [axisA, hp]
      · rw [real_inner_comm]; exact inner_normalPart_axisA D hp
    rw [this, mul_zero, add_zero]; field_simp

end TwoLayer

end LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
