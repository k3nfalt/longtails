import LongTails.Setups.FiniteLogisticTwoTap
import LongTails.Proofs.TwoSampleQuadraticPerceptronSpectrum

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (shift_add shift_smul norm_shift norm_ones)

namespace LongTails.Proofs.FiniteLogisticTwoTapSpectrum

lemma lift_add {d : ℕ} (a b : Features d) :
    liftReadout (a + b) = liftReadout a + liftReadout b := by
  ext i
  cases i <;> simp [liftReadout]

lemma lift_smul {d : ℕ} (s : ℝ) (b : Features d) : liftReadout (s • b) = s • liftReadout b := by
  ext i
  cases i <;> simp [liftReadout]

lemma norm_lift {d : ℕ} (b : Features d) : ‖liftReadout b‖ = ‖b‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, liftReadout]

lemma sampleMatrix_norm {d : ℕ} (b : Features d) : ‖sampleMatrix b‖ ≤ 4 * ‖b‖ := by
  unfold sampleMatrix
  grw [norm_add_le, norm_add_le, norm_add_le]
  simp [norm_lift, norm_shift]
  ring_nf
  rfl

lemma signed_norms {d : ℕ} (i : Fin d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ' : μ ≤ 1) :
    ‖sampleMatrix (signedInput μ i false)‖ ^ 2 +
      ‖sampleMatrix (signedInput μ i true)‖ ^ 2 ≤ 80 * d := by
  have hroot : 1 ≤ Real.sqrt d := by
    simpa using (Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d by exact_mod_cast Nat.zero_lt_of_lt i.isLt))
  have h₁ := sampleMatrix_norm (signedInput μ i false)
  simp [signedInput, norm_ones] at h₁
  have h₂ := sampleMatrix_norm (signedInput μ i true)
  have he := norm_add_le (ones d) (μ • EuclideanSpace.single i (1 : ℝ))
  simp [norm_ones, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at he
  simp only [signedInput, ↓reduceIte, norm_neg] at h₂
  have hb : ‖sampleMatrix (signedInput μ i true)‖ ≤ 8 * Real.sqrt d := by
    simp only [signedInput, ↓reduceIte]
    linarith
  have ha : ‖sampleMatrix (signedInput μ i false)‖ ≤ 4 * Real.sqrt d := h₁
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), pow_le_pow_left₀ (norm_nonneg _) ha 2,
    pow_le_pow_left₀ (norm_nonneg _) hb 2]

lemma matrix_add {d : ℕ} (a b : Features d) :
    sampleMatrix (a + b) = sampleMatrix a + sampleMatrix b := by
  simp only [sampleMatrix, shift_add, lift_add, map_add, add_apply]
  abel

lemma matrix_smul {d : ℕ} (s : ℝ) (b : Features d) :
    sampleMatrix (s • b) = s • sampleMatrix b := by
  ext x : 1
  simp only [sampleMatrix, shift_smul, lift_smul, add_apply, smul_apply,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, smul_smul, smul_add]
  module

lemma sum_matrices {d : ℕ} (μ : ℝ) (i : Fin d) :
    sampleMatrix (signedInput μ i false) + sampleMatrix (signedInput μ i true) =
      (-μ) • sampleMatrix (EuclideanSpace.single i 1) := by
  simp only [signedInput, Bool.false_eq_true, ↓reduceIte, ← neg_one_smul ℝ
    (ones d + μ • EuclideanSpace.single i 1), matrix_smul, matrix_add]
  module

lemma shifted_single {d : ℕ} (i : Fin d) :
    shift (EuclideanSpace.single i 1) = EuclideanSpace.single (finRotate d i) 1 := by
  ext j
  change (EuclideanSpace.single i (1 : ℝ)) ((finRotate d).symm j) = _
  simp only [PiLp.single_apply, Equiv.symm_apply_eq]

lemma lifted_single {d : ℕ} (i : Fin d) :
    liftReadout (EuclideanSpace.single i 1) = EuclideanSpace.single (.inr i) 1 := by
  ext j
  cases j <;> simp [liftReadout]

lemma defect_action {d : ℕ} (i : Fin d) (x : Weights d) :
    sampleMatrix (EuclideanSpace.single i 1) x =
      x (.inr i) • EuclideanSpace.single (.inl 0) 1 +
      x (.inl 0) • EuclideanSpace.single (.inr i) 1 +
      x (.inr (finRotate d i)) • EuclideanSpace.single (.inl 1) 1 +
      x (.inl 1) • EuclideanSpace.single (.inr (finRotate d i)) 1 := by
  simp [sampleMatrix, shifted_single, lifted_single, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_single_left]

lemma defect_norm {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) (x : Weights d) :
    ‖sampleMatrix (EuclideanSpace.single i 1) x‖ ≤ ‖x‖ := by
  let support : Finset (Fin 2 ⊕ Fin d) := {.inl 0, .inl 1, .inr i, .inr (finRotate d i)}
  have hs := Finset.sum_le_univ_sum_of_nonneg (s := support) (fun j => sq_nonneg (x j))
  rw [← EuclideanSpace.real_norm_sq_eq] at hs
  simp [support, -finRotate_apply, Ne.symm hi] at hs
  have he : ‖sampleMatrix (EuclideanSpace.single i 1) x‖ ^ 2 =
      x (.inr i) ^ 2 + x (.inl 0) ^ 2 + x (.inr (finRotate d i)) ^ 2 + x (.inl 1) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, defect_action]
    simp only [inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left,
      map_one, one_mul, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    simp [-finRotate_apply,
      hi, Ne.symm hi, pow_two]
  nlinarith [norm_nonneg x]

lemma linear_growth {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i)
    {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) (x : Weights d) :
    ‖x + (η / 4) • ((sampleMatrix (signedInput μ i false) +
      sampleMatrix (signedInput μ i true)) x)‖ ≤ (1 + η * μ / 4) * ‖x‖ := by
  rw [sum_matrices, smul_apply, smul_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hμ,
    abs_of_nonneg (show 0 ≤ η / 4 by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (defect_norm i hi x) (mul_nonneg hη hμ)]

lemma defect_cube {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) (x : Weights d) :
    let M := sampleMatrix (EuclideanSpace.single i 1)
    M (M (M x)) = M x := by
  dsimp only
  simp only [defect_action, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  simp [-finRotate_apply, hi, Ne.symm hi]

noncomputable def growingPart {d : ℕ} (i : Fin d) (x : Weights d) : Weights d :=
  let M := sampleMatrix (EuclideanSpace.single i 1)
  (1 / 2 : ℝ) • (M (M x) - M x)

lemma growingPart_explicit {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) (x : Weights d) :
    let j := finRotate d i
    let a := (x (.inl 0) - x (.inr i)) / 2
    let b := (x (.inl 1) - x (.inr j)) / 2
    growingPart i x = a • (EuclideanSpace.single (.inl 0) 1 - EuclideanSpace.single (.inr i) 1) +
      b • (EuclideanSpace.single (.inl 1) 1 - EuclideanSpace.single (.inr j) 1) := by
  dsimp only [growingPart]
  simp only [defect_action, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  simp [-finRotate_apply, hi, Ne.symm hi]
  module

lemma linear_trajectory {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i)
    (s : ℝ) (x : Weights d) (n : ℕ) :
    let M := sampleMatrix (EuclideanSpace.single i 1)
    (fun y => y - s • M y)^[n] x =
      (1 + s) ^ n • growingPart i x +
      (1 - s) ^ n • ((1 / 2 : ℝ) • (M (M x) + M x)) + (x - M (M x)) := by
  let M := sampleMatrix (EuclideanSpace.single i 1)
  change (fun y => y - s • M y)^[n] x = _
  have hM : M (M (M x)) = M x := defect_cube i hi x
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, one_smul, growingPart]
    module
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change _ - s • M _ = _
    change _ - s • M ((1 + s) ^ n • ((1 / 2 : ℝ) • (M (M x) - M x)) +
      (1 - s) ^ n • ((1 / 2 : ℝ) • (M (M x) + M x)) + (x - M (M x))) =
      (1 + s) ^ (n+1) • ((1 / 2 : ℝ) • (M (M x) - M x)) +
      (1 - s) ^ (n+1) • ((1 / 2 : ℝ) • (M (M x) + M x)) + (x - M (M x))
    simp only [map_add, map_sub, map_smul, hM, growingPart, pow_succ]
    dsimp only [M]
    module

lemma linear_residual {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (x : Weights d) (n : ℕ) :
    let M := sampleMatrix (EuclideanSpace.single i 1)
    ‖(fun y => y - s • M y)^[n] x - (1 + s) ^ n • growingPart i x‖ ≤ 3 * ‖x‖ := by
  let M := sampleMatrix (EuclideanSpace.single i 1)
  have h₁ : ‖M x‖ ≤ ‖x‖ := defect_norm i hi x
  have h₂ : ‖M (M x)‖ ≤ ‖x‖ := (defect_norm i hi (M x)).trans h₁
  dsimp only
  rw [linear_trajectory i hi]
  change ‖_ + _ + (x - M (M x)) - _‖ ≤ _
  rw [add_assoc, add_sub_cancel_left]
  have h₃ : |(1 - s) ^ n| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (by linarith) _)]
    exact pow_le_one₀ (by linarith) (by linarith)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hb : ‖M (M x) + M x‖ ≤ 2 * ‖x‖ := by linarith [norm_add_le (M (M x)) (M x)]
  have hc := mul_le_mul_of_nonneg_right h₃ (show 0 ≤ 1 / 2 * ‖M (M x) + M x‖ by positivity)
  change |(1 - s) ^ n| * (1 / 2 * ‖M (M x) + M x‖) + ‖x - M (M x)‖ ≤ _
  linarith [norm_sub_le x (M (M x))]

end LongTails.Proofs.FiniteLogisticTwoTapSpectrum
