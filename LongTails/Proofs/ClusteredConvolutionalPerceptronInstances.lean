import LongTails.Proofs.ClusteredPerceptronLowerBound
import LongTails.Proofs.ClusteredConvolutionalPerceptronConvergence

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronInstances

open LongTails.Setups.ClusteredConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones)
open TwoSampleQuadraticPerceptronEmbedding
open ClusteredPerceptronLowerBound

noncomputable def unitVector {d : ℕ} (i : Fin d) : Features d := EuclideanSpace.single i 1

noncomputable def center (n : ℕ) : Features (2 * n + 4) :=
  (1 / 4 : ℝ) • (unitVector ⟨0, by omega⟩ - unitVector ⟨1, by omega⟩)

noncomputable def perturbation (n : ℕ) (i : Fin (2 * n + 2)) : Features (2 * n + 4) :=
  (1 / 2 : ℝ) • (unitVector ⟨i.val + 2, by have := i.isLt; omega⟩ - unitVector ⟨1, by omega⟩)

noncomputable def residual (n : ℕ) (i : Fin (2 * n + 2)) : Features (2 * n + 4) :=
  center n + (1 / 512 : ℝ) • perturbation n i

lemma unit_norm {d : ℕ} (i : Fin d) : ‖unitVector i‖ = 1 := by simp [unitVector]

lemma unit_axis_inner {d : ℕ} (i : Fin d) : ⟪axis d, unitVector i⟫ = (Real.sqrt d)⁻¹ := by
  simp [axis, LongTails.Setups.ManySampleConvolutionalPerceptron.axis, unitVector,
    EuclideanSpace.inner_single_right, ones]

lemma center_norm (n : ℕ) : ‖center n‖ ≤ 1 / 2 := by
  have h := norm_sub_le (unitVector (⟨0, by omega⟩ : Fin (2 * n + 4))) (unitVector ⟨1, by omega⟩)
  rw [unit_norm, unit_norm] at h
  simp only [center, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  linarith

lemma perturbation_norm (n : ℕ) (i : Fin (2 * n + 2)) : ‖perturbation n i‖ ≤ 1 := by
  have h := norm_sub_le
    (unitVector (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (2 * n + 4))) (unitVector ⟨1, by omega⟩)
  rw [unit_norm, unit_norm] at h
  simp only [perturbation, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

lemma center_centered (n : ℕ) : ⟪axis (2 * n + 4), center n⟫ = 0 := by
  simp only [center, real_inner_smul_right, inner_sub_right, unit_axis_inner, sub_self, mul_zero]

lemma perturbation_centered (n : ℕ) (i : Fin (2 * n + 2)) :
    ⟪axis (2 * n + 4), perturbation n i⟫ = 0 := by
  simp only [perturbation, real_inner_smul_right, inner_sub_right, unit_axis_inner, sub_self, mul_zero]

lemma residual_centered (n : ℕ) (i : Fin (2 * n + 2)) :
    ⟪axis (2 * n + 4), residual n i⟫ = 0 := by
  simp only [residual, inner_add_right, real_inner_smul_right, center_centered,
    perturbation_centered, mul_zero, add_zero]

lemma residual_cap (n : ℕ) (i : Fin (2 * n + 2)) : ‖residual n i - center n‖ ≤ 1 / 512 := by
  have h := perturbation_norm n i
  simp only [residual, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 512)]
  linarith

lemma residual_norm (n : ℕ) (i : Fin (2 * n + 2)) : ‖residual n i‖ ≤ 2 / 3 := by
  have h := norm_add_le (residual n i - center n) (center n)
  rw [sub_add_cancel] at h
  linarith [residual_cap n i, center_norm n]

lemma center_coordinate_zero (n : ℕ) : center n ⟨0, by omega⟩ = 1 / 4 := by
  norm_num [center, unitVector]

lemma center_coordinate_one (n : ℕ) : center n ⟨1, by omega⟩ = -1 / 4 := by
  norm_num [center, unitVector]

lemma center_derivative (n : ℕ) :
    1 / 4 ≤ ‖(Real.sqrt 2)⁻¹ • (center n - shift (center n))‖ := by
  let j : Fin (2 * n + 4) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by simp [j]
  have hprev : (finRotate (2 * n + 4)).symm j = ⟨0, by omega⟩ := by
    apply Fin.ext
    rw [coe_finRotate_symm_of_ne_zero hj]
    rfl
  have hcoord : ((Real.sqrt 2)⁻¹ • (center n - shift (center n))) j =
      -(Real.sqrt 2)⁻¹ / 2 := by
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, shift_apply, hprev]
    change (Real.sqrt 2)⁻¹ * (center n ⟨1, by omega⟩ - center n ⟨0, by omega⟩) = _
    rw [center_coordinate_one, center_coordinate_zero]
    ring
  have hnorm := PiLp.norm_apply_le ((Real.sqrt 2)⁻¹ • (center n - shift (center n))) j
  rw [hcoord, Real.norm_eq_abs] at hnorm
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hinv : (1 / 2 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hs).mpr
    linarith
  have hneg : -(Real.sqrt 2)⁻¹ / 2 ≤ 0 := by
    have hi : 0 ≤ (Real.sqrt (2 : ℝ))⁻¹ := inv_nonneg.mpr hs.le
    linarith
  rw [abs_of_nonpos hneg] at hnorm
  linarith

lemma residual_coordinate (n : ℕ) (i j : Fin (2 * n + 2)) :
    residual n j ⟨i.val + 2, by have := i.isLt; omega⟩ = if i = j then 1 / 1024 else 0 := by
  have h0 : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (2 * n + 4)) ≠ ⟨0, by omega⟩ := by
    intro h
    have he := congrArg Fin.val h
    change i.val + 2 = 0 at he
    omega
  have h1 : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (2 * n + 4)) ≠ ⟨1, by omega⟩ := by
    intro h
    have he := congrArg Fin.val h
    change i.val + 2 = 1 at he
    omega
  have he : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (2 * n + 4)) =
      ⟨j.val + 2, by have := j.isLt; omega⟩ ↔ i = j := by
    rw [Fin.ext_iff, Fin.ext_iff]
    exact Nat.add_right_cancel_iff
  simp only [residual, center, perturbation, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, unitVector, PiLp.single_apply, ite_eq_right h0, ite_eq_right h1, he]
  split_ifs <;> norm_num

lemma residual_independent (n : ℕ) : LinearIndependent ℝ (residual n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hi := congrArg (fun x : Features (2 * n + 4) => x ⟨i.val + 2, by have := i.isLt; omega⟩) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hi
  simp_rw [residual_coordinate] at hi
  simp only [mul_ite, mul_zero] at hi
  simp at hi
  linarith

noncomputable def positiveSample (n : ℕ) (μ : ℝ) (i : Fin (n + 1)) : Features (2 * n + 4) :=
  axis (2 * n + 4) + μ • residual n ⟨2 * i.val, by have := i.isLt; omega⟩

noncomputable def negativeSample (n : ℕ) (μ : ℝ) (i : Fin (n + 1)) : Features (2 * n + 4) :=
  (1 + μ) • axis (2 * n + 4) - μ • residual n ⟨2 * i.val + 1, by have := i.isLt; omega⟩

noncomputable def dataset (n : ℕ) (μ : ℝ) : Data (2 * n + 4) (2 * n + 1) := fun j =>
  if j.val % 2 = 0 then axis (2 * n + 4) + μ • residual n j
  else -((1 + μ) • axis (2 * n + 4) - μ • residual n j)

lemma dataset_even (n : ℕ) (μ : ℝ) (i : Fin (n + 1)) :
    dataset n μ ⟨2 * i.val, by have := i.isLt; omega⟩ = positiveSample n μ i := by
  simp [dataset, positiveSample]

lemma dataset_odd (n : ℕ) (μ : ℝ) (i : Fin (n + 1)) :
    dataset n μ ⟨2 * i.val + 1, by have := i.isLt; omega⟩ = -negativeSample n μ i := by
  simp [dataset, negativeSample]

noncomputable def familyGeometry (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    Geometry (dataset n μ) (Real.sqrt 2) (2 * Real.sqrt 2) μ (1 / 8) where
  background j := if j.val % 2 = 0 then Real.sqrt 2 else -(1 + μ) * Real.sqrt 2
  defect := residual n
  center := center n
  sample_eq := by
    intro j
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    by_cases hj : j.val % 2 = 0
    · simp [dataset, hj, hs]
    · have he : (-(1 + μ) * Real.sqrt 2) / Real.sqrt 2 = -(1 + μ) := by field_simp
      simp only [dataset, ite_eq_right hj, he]
      module
  background_lower := by
    intro j
    have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    split_ifs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_nonpos (by nlinarith : -(1 + μ) * Real.sqrt 2 ≤ 0)]
      nlinarith
  background_upper := by
    intro j
    have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    split_ifs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_nonpos (by nlinarith : -(1 + μ) * Real.sqrt 2 ≤ 0)]
      nlinarith
  centered := residual_centered n
  center_norm := center_norm n
  derivative_lower := by norm_num; exact center_derivative n
  cap := by intro j; norm_num; exact residual_cap n j

noncomputable def parameters (n : ℕ) (μ : ℝ) : Params :=
  ⟨2 * n + 4, 2 * n + 1, Real.sqrt 2, 2 * Real.sqrt 2, μ, 1 / 8⟩

lemma parameters_valid (n : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1048576) :
    spec.valid (parameters n μ) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hr : Real.sqrt 2 / (4 * (2 * Real.sqrt 2)) = (1 / 8 : ℝ) := by field_simp; norm_num
  have hd : (μ / (4 * (2 * Real.sqrt 2))) ^ 2 = μ ^ 2 / 128 := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  change 0 < 2 * n + 4 ∧ 0 < Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 * Real.sqrt 2 ∧
    0 < μ ∧ 0 < (1 / 8 : ℝ) ∧ (1 / 8 : ℝ) ≤ 1 / 4 ∧ _
  refine ⟨by omega, hs, by linarith, hμ, by norm_num, by norm_num, ?_⟩
  change (μ / (4 * (2 * Real.sqrt 2))) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 *
    (Real.sqrt 2 / (4 * (2 * Real.sqrt 2))) ^ 8 / 4096
  rw [hr, hd]
  norm_num
  nlinarith

open LongTails.Algorithms.ClusteredConvolutionalPerceptron

lemma family_raw_mistakes (n : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1048576)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪positiveSample n μ j, pairedLinearIterate (positiveSample n μ) (negativeSample n μ) k⟫ ≤ 0 ∧
      ⟪-negativeSample n μ j, pairedLinearMiddle (positiveSample n μ) (negativeSample n μ) k⟫ < 0 := by
  have hm : μ ≤ 1 / 4 := by linarith
  have h := paired_linear_mistakes
    (ManySampleConvolutionalPerceptronGeometry.axis_inner (by omega : 0 < 2 * n + 4))
    (fun j : Fin (n + 1) => residual_centered n ⟨2 * j.val, by have := j.isLt; omega⟩)
    (fun j : Fin (n + 1) => show ⟪axis (2 * n + 4),
      -residual n ⟨2 * j.val + 1, by have := j.isLt; omega⟩⟫ = 0 by
      rw [inner_neg_right, residual_centered, neg_zero])
    hμ hm (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using hm)
    (fun j => (residual_norm n ⟨2 * j.val, by have := j.isLt; omega⟩).trans (by norm_num : (2 / 3 : ℝ) ≤ 1))
    (fun j => show ‖-residual n ⟨2 * j.val + 1, by have := j.isLt; omega⟩‖ ≤ 1 by
      rw [norm_neg]; exact (residual_norm n _).trans (by norm_num : (2 / 3 : ℝ) ≤ 1)) k hk
  dsimp only
  unfold positiveSample negativeSample
  simpa only [one_smul, mul_one, smul_neg, ← sub_eq_add_neg] using h

lemma family_frozen_mistakes (n : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1048576)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => frozenFeature (1 / 8) (positiveSample n μ j)
    let neg := fun j => frozenFeature (1 / 8) (negativeSample n μ j)
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, pairedLinearIterate pos neg k⟫ ≤ 0 ∧ ⟪-neg j, pairedLinearMiddle pos neg k⟫ < 0 := by
  have h := frozen_linear_mistakes (by omega : 0 < 2 * n + 4)
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4) hμ
    (show μ ≤ (1 / 8 : ℝ) ^ 2 / 512 by norm_num; linarith)
    (fun j : Fin (n + 1) => residual_centered n ⟨2 * j.val, by have := j.isLt; omega⟩)
    (fun j : Fin (n + 1) => show ⟪axis (2 * n + 4),
      -residual n ⟨2 * j.val + 1, by have := j.isLt; omega⟩⟫ = 0 by
      rw [inner_neg_right, residual_centered, neg_zero])
    (fun j => residual_norm n ⟨2 * j.val, by have := j.isLt; omega⟩)
    (fun j => show ‖-residual n ⟨2 * j.val + 1, by have := j.isLt; omega⟩‖ ≤ 2 / 3 by
      rw [norm_neg]; exact residual_norm n _) k hk
  simpa only [positiveSample, negativeSample, smul_neg, ← sub_eq_add_neg] using h

end LongTails.Proofs.ClusteredConvolutionalPerceptronInstances
