import LongTails.Proofs.MatrixCovariance
import LongTails.Proofs.MatrixPolarCharacterization
import LongTails.Proofs.AdamSymmetricGeometry

namespace LongTails.Proofs.AdamMatrixGeometry

open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.MatrixPolarCharacterization

noncomputable def unitOnes (r : ℕ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun _ => (Real.sqrt r)⁻¹)

lemma unitOnes_norm {r : ℕ} (hr : 0 < r) : ‖unitOnes r‖ = 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr'
  have hsq : ‖unitOnes r‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [unitOnes, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [inv_pow, Real.sq_sqrt hr'.le]
    exact mul_inv_cancel₀ hr'.ne'
  nlinarith [norm_nonneg (unitOnes r)]

lemma exists_basis_unitOnes {r : ℕ} (hr : 0 < r) :
    ∃ b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)),
      b ⟨0, hr⟩ = unitOnes r := by
  classical
  let i : Fin r := ⟨0, hr⟩
  have ho : Orthonormal ℝ (({i} : Set (Fin r)).domRestrict (fun _ => unitOnes r)) := by
    rw [orthonormal_subsingleton_iff]
    intro j
    exact unitOnes_norm hr
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = Fintype.card (Fin r))
  exact ⟨b, hb i (Set.mem_singleton i)⟩

noncomputable def denseProjection (r : ℕ) : Space r r :=
  WithLp.toLp 2 (fun _ => (r : ℝ)⁻¹)

noncomputable def quietProjection (r : ℕ) : Space r r :=
  WithLp.toLp 2 (fun ij => (if ij.1 = ij.2 then 1 else 0) - (r : ℝ)⁻¹)

lemma denseProjection_apply {r : ℕ} (hr : 0 < r)
    (v : EuclideanSpace ℝ (Fin r)) :
    operatorEquiv r r (denseProjection r) v = (inner ℝ (unitOnes r) v) • unitOnes r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr'.le
  ext i
  rw [operatorEquiv_apply_coordinate]
  simp only [denseProjection, unitOnes, PiLp.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [mul_assoc]
  have hh : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = (r : ℝ)⁻¹ := by
    rw [← mul_inv, ← sq, hs]
  simp_rw [hh]
  ring

lemma quietProjection_apply {r : ℕ} (v : EuclideanSpace ℝ (Fin r)) :
    operatorEquiv r r (quietProjection r) v = v - operatorEquiv r r (denseProjection r) v := by
  ext i
  simp only [operatorEquiv_apply_coordinate, quietProjection, denseProjection,
    PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp

lemma denseProjection_apply_basis {r : ℕ} (hr : 0 < r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (i₀ : Fin r)
    (hb : b i₀ = unitOnes r) (i : Fin r) :
    operatorEquiv r r (denseProjection r) (b i) = (if i = i₀ then 1 else 0 : ℝ) • b i := by
  rw [denseProjection_apply hr, ← hb, b.inner_eq_ite]
  by_cases hi : i = i₀
  · subst i
    simp
  · simp [hi, Ne.symm hi]

lemma quietProjection_apply_basis {r : ℕ} (hr : 0 < r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (i₀ : Fin r)
    (hb : b i₀ = unitOnes r) (i : Fin r) :
    operatorEquiv r r (quietProjection r) (b i) = (if i = i₀ then 0 else 1 : ℝ) • b i := by
  rw [quietProjection_apply, denseProjection_apply_basis hr b i₀ hb]
  by_cases hi : i = i₀ <;> simp [hi]

lemma nuclearNorm_of_basis_eigen {r : ℕ} (X : Space r r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (coeff : Fin r → ℝ)
    (hcoeff : ∀ i, operatorEquiv r r X (b i) = coeff i • b i) :
    nuclearNorm X = ∑ i, |coeff i| := by
  have ho : ∀ i j, i ≠ j →
      inner ℝ (operatorEquiv r r X (b i)) (operatorEquiv r r X (b j)) = 0 := by
    intro i j hij
    rw [hcoeff, hcoeff, real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite]
    simp [hij]
  rw [← polar_pairing_eq_nuclear, inner_eq_sum_columns X (polar X) b]
  apply Finset.sum_congr rfl
  intro i _
  rw [polar_apply_of_orthogonal_images X b ho, normalized_inner, hcoeff]
  simp [norm_smul, b.norm_eq_one, Real.norm_eq_abs]

lemma spectralNorm_le_one_of_basis_eigen {r : ℕ} (X : Space r r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (coeff : Fin r → ℝ)
    (hcoeff : ∀ i, operatorEquiv r r X (b i) = coeff i • b i)
    (hcoeff₁ : ∀ i, |coeff i| ≤ 1) : spectralNorm X ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  have heq : operatorEquiv r r X z = ∑ i, (inner ℝ (b i) z * coeff i) • b i := by
    nth_rw 1 [← b.sum_repr' z]
    simp only [map_sum, map_smul, hcoeff, smul_smul]
  have ho : ∀ i j, i ≠ j → inner ℝ (b i) (b j) = 0 := by
    intro i j hij
    simp [b.inner_eq_ite, hij]
  have hs := orthogonal_synthesis_norm_sq (fun i => b i)
    (fun i => inner ℝ (b i) z * coeff i) ho
  have hz := b.sum_sq_norm_inner_right z
  simp only [Real.norm_eq_abs, sq_abs] at hz
  have hsum : (∑ i, (inner ℝ (b i) z * coeff i) ^ 2 * ‖b i‖ ^ 2) ≤
      ∑ i, (inner ℝ (b i) z) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    simp only [b.norm_eq_one, one_pow, mul_one, mul_pow]
    have hsq : (coeff i) ^ 2 ≤ 1 := by nlinarith [sq_abs (coeff i), hcoeff₁ i, abs_nonneg (coeff i)]
    exact mul_le_of_le_one_right (sq_nonneg _) hsq
  rw [heq, one_mul]
  nlinarith [norm_nonneg z, norm_nonneg (∑ i, (inner ℝ (b i) z * coeff i) • b i)]

noncomputable def mixedProjection (r : ℕ) (a b : ℝ) : Space r r :=
  a • denseProjection r + b • quietProjection r

lemma mixedProjection_apply_basis {r : ℕ} (hr : 0 < r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (i₀ : Fin r)
    (hb : b i₀ = unitOnes r) (a c : ℝ) (i : Fin r) :
    operatorEquiv r r (mixedProjection r a c) (b i) =
      (if i = i₀ then a else c) • b i := by
  simp only [mixedProjection, map_add, map_smul, add_apply,
    smul_apply, denseProjection_apply_basis hr b i₀ hb,
    quietProjection_apply_basis hr b i₀ hb, smul_smul]
  by_cases hi : i = i₀ <;> simp [hi]

lemma sum_single_other {r : ℕ} (i₀ : Fin r) (a b : ℝ) :
    (∑ i : Fin r, if i = i₀ then a else b) = a + ((r : ℝ) - 1) * b := by
  have h (i : Fin r) : (if i = i₀ then a else b) =
      b + (if i = i₀ then a - b else 0) := by
    by_cases hi : i = i₀ <;> simp [hi]
  simp_rw [h]
  simp [Finset.sum_add_distrib]
  ring

lemma nuclearNorm_mixedProjection {r : ℕ} (hr : 0 < r) (a c : ℝ) :
    nuclearNorm (mixedProjection r a c) = |a| + ((r : ℝ) - 1) * |c| := by
  obtain ⟨b, hb⟩ := exists_basis_unitOnes hr
  rw [nuclearNorm_of_basis_eigen _ b _ (mixedProjection_apply_basis hr b ⟨0, hr⟩ hb a c)]
  simp_rw [apply_ite abs]
  exact sum_single_other ⟨0, hr⟩ |a| |c|

lemma spectralNorm_mixedProjection_le_one {r : ℕ} (hr : 0 < r) (a c : ℝ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) : spectralNorm (mixedProjection r a c) ≤ 1 := by
  obtain ⟨b, hb⟩ := exists_basis_unitOnes hr
  apply spectralNorm_le_one_of_basis_eigen _ b _
    (mixedProjection_apply_basis hr b ⟨0, hr⟩ hb a c)
  intro i
  split_ifs <;> assumption

lemma inner_of_basis_eigen {r : ℕ} (X Y : Space r r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (a c : Fin r → ℝ)
    (ha : ∀ i, operatorEquiv r r X (b i) = a i • b i)
    (hc : ∀ i, operatorEquiv r r Y (b i) = c i • b i) :
    inner ℝ X Y = ∑ i, a i * c i := by
  rw [inner_eq_sum_columns X Y b]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha, hc, real_inner_smul_left, real_inner_smul_right]
  simp [mul_comm]

lemma inner_mixedProjection {r : ℕ} (hr : 0 < r) (a c d e : ℝ) :
    inner ℝ (mixedProjection r a c) (mixedProjection r d e) =
      a * d + ((r : ℝ) - 1) * (c * e) := by
  obtain ⟨b, hb⟩ := exists_basis_unitOnes hr
  rw [inner_of_basis_eigen _ _ b _ _
    (mixedProjection_apply_basis hr b ⟨0, hr⟩ hb a c)
    (mixedProjection_apply_basis hr b ⟨0, hr⟩ hb d e)]
  calc
    _ = ∑ i : Fin r, if i = ⟨0, hr⟩ then a * d else c * e := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    _ = _ := sum_single_other ⟨0, hr⟩ (a * d) (c * e)

lemma mixedProjection_apply {r : ℕ} (a b : ℝ) (i j : Fin r) :
    mixedProjection r a b (i, j) =
      if i = j then (a + ((r : ℝ) - 1) * b) / r else (a - b) / r := by
  simp only [mixedProjection, denseProjection, quietProjection, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  by_cases hi : i = j
  · have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
    simp only [hi, ↓reduceIte]
    field_simp
  · simp only [hi, ↓reduceIte]
    ring

lemma denseProjection_adjoint {r : ℕ} (hr : 0 < r) :
    (operatorEquiv r r (denseProjection r)).adjoint = operatorEquiv r r (denseProjection r) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, denseProjection_apply hr,
    denseProjection_apply hr, real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_comm x (unitOnes r)]
  ring

lemma norm_adjoint_dense_basis {r : ℕ} (hr : 0 < r)
    (b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) (i₀ : Fin r)
    (hb : b i₀ = unitOnes r) (z : ℝ) (i : Fin r) :
    ‖(operatorEquiv r r (z • denseProjection r)).adjoint (b i)‖ =
      if i = i₀ then |z| else 0 := by
  rw [map_smul]
  simp only [map_smulₛₗ, conj_trivial, denseProjection_adjoint hr,
    smul_apply, denseProjection_apply_basis hr b i₀ hb, smul_smul]
  by_cases hi : i = i₀ <;> simp [hi, norm_smul, b.norm_eq_one, Real.norm_eq_abs]

end LongTails.Proofs.AdamMatrixGeometry
