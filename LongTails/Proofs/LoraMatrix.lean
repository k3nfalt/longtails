import LongTails.Proofs.LoraGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace LongTails.Proofs.LoraMatrix

open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraGeometry

noncomputable def column {m n : ℕ} (B : MatrixSpace m n) (j : Fin n) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun i => B (i, j)

noncomputable def row {m n : ℕ} (B : MatrixSpace m n) (i : Fin m) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun j => B (i, j)

lemma column_norm_sq {m n : ℕ} (B : MatrixSpace m n) :
    ∑ j, ‖column B j‖ ^ 2 = ‖B‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, column, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma row_norm_sq {m n : ℕ} (B : MatrixSpace m n) :
    ∑ i, ‖row B i‖ ^ 2 = ‖B‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, row, Fintype.sum_prod_type]

noncomputable def action {m n : ℕ} (B : MatrixSpace m n)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => ∑ j, B (i, j) * v j

lemma action_norm {m n : ℕ} (B : MatrixSpace m n) (v : EuclideanSpace ℝ (Fin n)) :
    ‖action B v‖ ≤ ‖B‖ * ‖v‖ := by
  have hh : ‖action B v‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, action, Fintype.sum_prod_type]
    calc
      ∑ i, (∑ j, B (i, j) * v j) ^ 2 ≤
          ∑ i, (∑ j, B (i, j) ^ 2) * (∑ j, v j ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = _ := by rw [Finset.sum_mul]
  nlinarith [norm_nonneg (action B v), mul_nonneg (norm_nonneg B) (norm_nonneg v)]

noncomputable def actionMap {m n : ℕ} (B : MatrixSpace m n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.mkContinuous
    { toFun := action B
      map_add' := by
        intro u v
        ext i
        simp [action, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext i
        simp [action, PiLp.smul_apply, Finset.mul_sum, mul_left_comm] }
    ‖B‖ (action_norm B)

lemma multiply_column {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n)
    (j : Fin n) : column (multiply B A) j = action B (column A j) := rfl

lemma multiply_lower_left {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n)
    {s : ℝ} (hs : 0 ≤ s) (hB : ∀ v, s * ‖v‖ ≤ ‖action B v‖) :
    s * ‖A‖ ≤ ‖multiply B A‖ := by
  have hh : s ^ 2 * ‖A‖ ^ 2 ≤ ‖multiply B A‖ ^ 2 := by
    rw [← column_norm_sq A, ← column_norm_sq (multiply B A), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [multiply_column, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hs (norm_nonneg _)) (hB _) 2
  nlinarith [norm_nonneg (multiply B A), mul_nonneg hs (norm_nonneg A)]

noncomputable def transpose {m n : ℕ} (B : MatrixSpace m n) : MatrixSpace n m :=
  WithLp.toLp 2 fun ji => B (ji.2, ji.1)

lemma transpose_norm {m n : ℕ} (B : MatrixSpace m n) : ‖transpose B‖ = ‖B‖ := by
  have hh : ‖transpose B‖ ^ 2 = ‖B‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, transpose, Fintype.sum_prod_type]
    exact Finset.sum_comm
  nlinarith [norm_nonneg B, norm_nonneg (transpose B)]

lemma transpose_multiply {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    transpose (multiply B A) = multiply (transpose A) (transpose B) := by
  ext ji
  simp [transpose, multiply, mul_comm]

lemma multiply_lower_right {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n)
    {s : ℝ} (hs : 0 ≤ s) (hA : ∀ v, s * ‖v‖ ≤ ‖action (transpose A) v‖) :
    s * ‖B‖ ≤ ‖multiply B A‖ := by
  have hh := multiply_lower_left (transpose A) (transpose B) hs hA
  rw [← transpose_multiply, transpose_norm, transpose_norm] at hh
  exact hh

noncomputable def leftApply {m n l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (B : MatrixSpace m n) : MatrixSpace l n :=
  WithLp.toLp 2 fun ij => T (column B ij.2) ij.1

lemma leftApply_column {m n l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (B : MatrixSpace m n) (j : Fin n) :
    column (leftApply T B) j = T (column B j) := by
  ext i
  rfl

lemma leftApply_norm {m n l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (B : MatrixSpace m n) {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v, ‖T v‖ ≤ C * ‖v‖) :
    ‖leftApply T B‖ ≤ C * ‖B‖ := by
  have hh : ‖leftApply T B‖ ^ 2 ≤ C ^ 2 * ‖B‖ ^ 2 := by
    rw [← column_norm_sq, ← column_norm_sq B, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [leftApply_column, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hT _) 2
  nlinarith [norm_nonneg (leftApply T B), mul_nonneg hC (norm_nonneg B)]

lemma action_sum {m n : ℕ} (B : MatrixSpace m n) (v : EuclideanSpace ℝ (Fin n)) :
    action B v = ∑ j, v j • column B j := by
  ext i
  simp [action, column, mul_comm]

lemma action_leftApply {m n l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (B : MatrixSpace m n) (v : EuclideanSpace ℝ (Fin n)) :
    action (leftApply T B) v = T (action B v) := by
  simp only [action_sum, leftApply_column, map_sum, map_smul]

lemma leftApply_multiply {m n r l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (B : MatrixSpace m r) (A : MatrixSpace r n) :
    leftApply T (multiply B A) = multiply (leftApply T B) A := by
  ext ij
  have hh : column (leftApply T (multiply B A)) ij.2 =
      column (multiply (leftApply T B) A) ij.2 := by
    rw [leftApply_column, multiply_column, multiply_column, action_leftApply]
  exact congrArg (fun z => z ij.1) hh

lemma column_sub {m n : ℕ} (A B : MatrixSpace m n) (j : Fin n) :
    column (A - B) j = column A j - column B j := rfl

lemma leftApply_sub {m n l : ℕ}
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (A B : MatrixSpace m n) : leftApply T (A - B) = leftApply T A - leftApply T B := by
  ext ij
  simp [leftApply, column_sub, map_sub, PiLp.sub_apply]

lemma action_sub {m n : ℕ} (A B : MatrixSpace m n) (v : EuclideanSpace ℝ (Fin n)) :
    action (A - B) v = action A v - action B v := by
  ext i
  simp [action, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma multiply_sub_left {m n r : ℕ} (B C : MatrixSpace m r) (A : MatrixSpace r n) :
    multiply (B - C) A = multiply B A - multiply C A := by
  ext ij
  simp [multiply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma multiply_sub_right {m n r : ℕ} (B : MatrixSpace m r) (A C : MatrixSpace r n) :
    multiply B (A - C) = multiply B A - multiply B C := by
  ext ij
  simp [multiply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma exists_multiply_eq {m n r : ℕ} (B : MatrixSpace m r) (X : MatrixSpace m n)
    (hx : ∀ j, column X j ∈ (actionMap B).toLinearMap.range) :
    ∃ A : MatrixSpace r n, multiply B A = X := by
  classical
  choose v hv using hx
  let A : MatrixSpace r n := WithLp.toLp 2 fun kj => v kj.2 kj.1
  have hc : ∀ j, column A j = v j := fun j => by ext k; rfl
  refine ⟨A, ?_⟩
  ext ij
  have hh : column (multiply B A) ij.2 = column X ij.2 := by
    rw [multiply_column, hc]
    exact hv ij.2
  exact congrArg (fun z => z ij.1) hh

lemma lower_perturbation {m n : ℕ} (B B₀ : MatrixSpace m n) {s : ℝ}
    (hB₀ : ∀ v, s * ‖v‖ ≤ ‖action B₀ v‖) (hclose : ‖B - B₀‖ ≤ s / 2) :
    ∀ v, (s / 2) * ‖v‖ ≤ ‖action B v‖ := by
  intro v
  have hh : ‖action B v - action B₀ v‖ ≤ (s / 2) * ‖v‖ := by
    rw [← action_sub]
    exact (action_norm _ _).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have hn := norm_sub_le (action B v) (action B v - action B₀ v)
  rw [sub_sub_cancel] at hn
  have hb := hB₀ v
  linarith

lemma column_mem_range {m n : ℕ} (B : MatrixSpace m n) (j : Fin n) :
    column B j ∈ (actionMap B).toLinearMap.range := by
  refine ⟨EuclideanSpace.single j 1, ?_⟩
  change action B (EuclideanSpace.single j 1) = column B j
  ext i
  simp [action, column]

lemma leftApply_projection_fixed {m n : ℕ} (B : MatrixSpace m n) :
    leftApply (actionMap B).toLinearMap.range.starProjection B = B := by
  ext ij
  have hh := (actionMap B).toLinearMap.range.starProjection_eq_self_iff.mpr
    (column_mem_range B ij.2)
  exact congrArg (fun z => z ij.1) hh

lemma leftApply_projection_complement {m n : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (B : MatrixSpace m n) :
    leftApply Uᗮ.starProjection B = B - leftApply U.starProjection B := by
  ext ij
  have hh := congrArg (fun z => z ij.1)
    (U.starProjection_add_starProjection_orthogonal (column B ij.2))
  change Uᗮ.starProjection (column B ij.2) ij.1 =
    B ij - U.starProjection (column B ij.2) ij.1
  change U.starProjection (column B ij.2) ij.1 +
    Uᗮ.starProjection (column B ij.2) ij.1 = B ij at hh
  linarith

lemma transpose_sub {m n : ℕ} (A B : MatrixSpace m n) :
    transpose (A - B) = transpose A - transpose B := rfl

end LongTails.Proofs.LoraMatrix
