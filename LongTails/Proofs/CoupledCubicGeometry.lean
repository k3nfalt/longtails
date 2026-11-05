import LongTails.Proofs.TemporalSpectralResponse
import LongTails.Proofs.SpectralMirrorGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledCubicGeometry

open OracleTemplate.TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma relative_form_of_normalization (A D S : E →L[ℝ] E) (η : ℝ) (hη : 0 ≤ η)
    (hD : D.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hinj : Function.Injective S) (hsurj : Function.Surjective S)
    (hAS : ∀ x : E, S (A (S x)) = x)
    (hrelative : ∀ x : E, ‖D x‖ ≤ η * ‖A x‖) (v : E) :
    |⟪v, D v⟫| ≤ η * ⟪v, A v⟫ := by
  have hSs : ∀ x y : E, ⟪S x, y⟫ = ⟪x, S y⟫ := hS
  have hDs : ∀ x y : E, ⟪D x, y⟫ = ⟪x, D y⟫ := hD
  let B := S.comp (D.comp S)
  have hB : B.toLinearMap.IsSymmetric := by
    intro x y
    change ⟪S (D (S x)), y⟫ = ⟪x, S (D (S y))⟫
    rw [hSs, hDs, hSs]
  have heig (i : Fin (Module.finrank ℝ E)) : |hB.eigenvalues rfl i| ≤ η := by
    let w := hB.eigenvectorBasis rfl i
    let eig :=  hB.eigenvalues rfl i
    have hw : w ≠ 0 := by
      intro hz
      have hn : ‖w‖ = 1 := OrthonormalBasis.norm_eq_one _ _
      rw [hz, norm_zero] at hn
      norm_num at hn
    have hAw : A (S w) ≠ 0 := by
      intro hz
      have hh := hAS w
      rw [hz, map_zero] at hh
      exact hw hh.symm
    have hDw : D (S w) = eig • A (S w) := by
      apply hinj
      rw [map_smul, hAS]
      exact hB.apply_eigenvectorBasis rfl i
    have hh := hrelative (S w)
    rw [hDw, norm_smul, Real.norm_eq_abs] at hh
    exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hAw)).mp hh
  have hnorm (x : E) : ‖B x‖ ≤ η * ‖x‖ := by
    rw [spectral_diagonalization B hB]
    exact diagonalMap_bound _ _ hη heig x
  obtain ⟨x, rfl⟩ := hsurj v
  have hform : ⟪S x, D (S x)⟫ = ⟪x, B x⟫ := hSs x (D (S x))
  have hmetric : ⟪S x, A (S x)⟫ = ‖x‖ ^ 2 := by
    rw [hSs, hAS, real_inner_self_eq_norm_sq]
  rw [hform, hmetric]
  calc
    |⟪x, B x⟫| ≤ ‖x‖ * ‖B x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (η * ‖x‖) := mul_le_mul_of_nonneg_left (hnorm x) (norm_nonneg x)
    _ = η * ‖x‖ ^ 2 := by ring


lemma relative_form_positive (A D : E →L[ℝ] E) (η : ℝ) (hη : 0 ≤ η)
    (hA : A.toLinearMap.IsSymmetric) (hD : D.toLinearMap.IsSymmetric)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪A x, x⟫)
    (hrelative : ∀ x : E, ‖D x‖ ≤ η * ‖A x‖) (v : E) :
    |⟪v, D v⟫| ≤ η * ⟪v, A v⟫ := by
  let b := hA.eigenvectorBasis rfl
  let c := hA.eigenvalues rfl
  have hc (i : Fin (Module.finrank ℝ E)) : 0 < c i := by
    have hbi : b i ≠ 0 := by
      intro hz
      have hn : ‖b i‖ = 1 := OrthonormalBasis.norm_eq_one _ _
      rw [hz, norm_zero] at hn
      norm_num at hn
    have hh := hpos (b i) hbi
    change 0 < ⟪A.toLinearMap (hA.eigenvectorBasis rfl i), hA.eigenvectorBasis rfl i⟫ at hh
    simpa [b, c, hA.apply_eigenvectorBasis, real_inner_smul_left,
      real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one] using hh
  let S := diagonalMap b (fun i => (Real.sqrt (c i))⁻¹)
  let T := diagonalMap b (fun i => Real.sqrt (c i))
  have hsqrt (i : Fin (Module.finrank ℝ E)) : Real.sqrt (c i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hc i))
  have hST (x : E) : S (T x) = x := by
    apply b.repr.injective
    ext i
    simp only [S, T, diagonalMap_coordinate]
    field_simp [hsqrt i]
  have hTS (x : E) : T (S x) = x := by
    apply b.repr.injective
    ext i
    simp only [S, T, diagonalMap_coordinate]
    field_simp [hsqrt i]
  have hAS (x : E) : S (A (S x)) = x := by
    rw [spectral_diagonalization A hA]
    apply b.repr.injective
    ext i
    change b.repr (S (diagonalMap b c (S x))) i = b.repr x i
    simp only [S, diagonalMap_coordinate]
    have he := Real.sq_sqrt (hc i).le
    field_simp [hsqrt i]
    rw [he]
  apply relative_form_of_normalization A D S η hη hD (diagonalMap_inner _ _)
    (fun x y hxy => by simpa only [hTS] using congrArg T hxy)
    (fun x => ⟨T x, hST x⟩) hAS hrelative


lemma relative_form_nonnegative (A D : E →L[ℝ] E) (η : ℝ) (hη : 0 ≤ η)
    (hA : A.toLinearMap.IsSymmetric) (hD : D.toLinearMap.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪A x, x⟫)
    (hrelative : ∀ x : E, ‖D x‖ ≤ η * ‖A x‖) (v : E) :
    |⟪v, D v⟫| ≤ η * ⟪v, A v⟫ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (η * ‖v‖ ^ 2 + 1)
  have hden : 0 < η * ‖v‖ ^ 2 + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let C := A + δ • ContinuousLinearMap.id ℝ E
  have hC (x : E) : C x = A x + δ • x := rfl
  have hsym : C.toLinearMap.IsSymmetric := by
    intro x y
    change ⟪C x, y⟫ = ⟪x, C y⟫
    simp only [hC, inner_add_left, inner_add_right, real_inner_smul_left,
      inner_smul_right]
    have hh : ⟪A x, y⟫ = ⟪x, A y⟫ := hA x y
    rw [hh]
  have hstrict (x : E) (hx : x ≠ 0) : 0 < ⟪C x, x⟫ := by
    rw [hC, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hn := norm_pos_iff.mpr hx
    have hp := hpos x
    positivity
  have hnorm (x : E) : ‖A x‖ ≤ ‖C x‖ := by
    have he := norm_add_sq_real (A x) (δ • x)
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at he
    have hp := mul_nonneg hδ.le (hpos x)
    rw [hC]
    nlinarith [norm_nonneg (A x), norm_nonneg (A x + δ • x), sq_nonneg (δ * ‖x‖)]
  have hh := relative_form_positive C D η hη hsym hD hstrict
    (fun x => (hrelative x).trans (mul_le_mul_of_nonneg_left (hnorm x) hη)) v
  simp only [hC, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  have hδeq : δ * (η * ‖v‖ ^ 2 + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  nlinarith


lemma diagonal_absolute_norm {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x : E) :
    ‖diagonalMap b (fun i => |c i|) x‖ = ‖diagonalMap b c x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [basis_norm_sq b, basis_norm_sq b]
  apply Finset.sum_congr rfl
  intro i _
  simp only [diagonalMap_coordinate, mul_pow, sq_abs]

lemma diagonal_quadratic {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x : E) :
    ⟪x, diagonalMap b c x⟫ = ∑ i, c i * (b.repr x i) ^ 2 := by
  rw [diagonalMap_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inner_smul_right, OrthonormalBasis.repr_apply_apply]
  rw [real_inner_comm x (b i)]
  ring

lemma shifted_absolute_norm {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (a : ℝ) (ha : 0 ≤ a) (x : E) :
    ‖diagonalMap b (fun i => |c i| + a) x‖ ≤ ‖diagonalMap b c x‖ + a * ‖x‖ := by
  have he : diagonalMap b (fun i => |c i| + a) x =
      diagonalMap b (fun i => |c i|) x + a • x := by
    apply b.repr.injective
    ext i
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, diagonalMap_coordinate]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [diagonal_absolute_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]

lemma shifted_absolute_dominates {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (a : ℝ) (ha : 0 ≤ a) (x : E) :
    ‖diagonalMap b c x‖ ≤ ‖diagonalMap b (fun i => |c i| + a) x‖ ∧
      a * ‖x‖ ≤ ‖diagonalMap b (fun i => |c i| + a) x‖ := by
  have hfirst : ‖diagonalMap b c x‖ ^ 2 ≤
      ‖diagonalMap b (fun i => |c i| + a) x‖ ^ 2 := by
    rw [basis_norm_sq b, basis_norm_sq b]
    apply Finset.sum_le_sum
    intro i _
    simp only [diagonalMap_coordinate, mul_pow]
    have hh : (c i) ^ 2 ≤ (|c i| + a) ^ 2 := by
      nlinarith [abs_nonneg (c i), sq_abs (c i)]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have hsecond : (a * ‖x‖) ^ 2 ≤
      ‖diagonalMap b (fun i => |c i| + a) x‖ ^ 2 := by
    rw [mul_pow, basis_norm_sq b x, basis_norm_sq b, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [diagonalMap_coordinate, mul_pow]
    have hh : a ^ 2 ≤ (|c i| + a) ^ 2 := by
      nlinarith [abs_nonneg (c i)]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  constructor
  · nlinarith [norm_nonneg (diagonalMap b c x),
      norm_nonneg (diagonalMap b (fun i => |c i| + a) x)]
  · nlinarith [norm_nonneg x,
      norm_nonneg (diagonalMap b (fun i => |c i| + a) x)]

lemma shifted_absolute_form {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hc : ∀ i, -a / 2 ≤ c i) (x : E) :
    ⟪x, diagonalMap b (fun i => |c i| + a) x⟫ ≤
      ⟪x, diagonalMap b c x⟫ + 2 * a * ‖x‖ ^ 2 := by
  rw [diagonal_quadratic, diagonal_quadratic, basis_norm_sq b,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hb : |c i| + a ≤ c i + 2 * a := by
    have hh := hc i
    rcases le_total 0 (c i) with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_nonpos h]
      linarith
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg (b.repr x i))
  nlinarith


lemma shifted_absolute_lower {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (a : ℝ) (x : E) :
    a * ‖x‖ ^ 2 ≤ ⟪x, diagonalMap b (fun i => |c i| + a) x⟫ := by
  rw [diagonal_quadratic, basis_norm_sq b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_nonneg (abs_nonneg (c i)) (sq_nonneg (b.repr x i))
  nlinarith

lemma cubic_relative_form (H D : E →L[ℝ] E) (a η : ℝ) (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hH : H.toLinearMap.IsSymmetric) (hD : D.toLinearMap.IsSymmetric)
    (hshift : ∀ x : E, -a / 2 * ‖x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hrelative : ∀ x : E, ‖D x‖ ≤ η *
      ‖diagonalMap (hH.eigenvectorBasis rfl) (fun i => |hH.eigenvalues rfl i| + a) x‖)
    (v : E) : |⟪v, D v⟫| ≤ η * (⟪v, H v⟫ + 2 * a * ‖v‖ ^ 2) := by
  let b := hH.eigenvectorBasis rfl
  let c := hH.eigenvalues rfl
  let A := diagonalMap b (fun i => |c i| + a)
  have hA : A.toLinearMap.IsSymmetric := diagonalMap_inner _ _
  have hpos (x : E) : 0 ≤ ⟪A x, x⟫ := by
    rw [real_inner_comm]
    exact (mul_nonneg ha (sq_nonneg _)).trans (shifted_absolute_lower b c a x)
  have hc (i : Fin (Module.finrank ℝ E)) : -a / 2 ≤ c i := by
    have hh := hshift (b i)
    rw [real_inner_comm] at hh
    change -a / 2 * ‖hH.eigenvectorBasis rfl i‖ ^ 2 ≤
      ⟪H.toLinearMap (hH.eigenvectorBasis rfl i), hH.eigenvectorBasis rfl i⟫ at hh
    simpa [c, hH.apply_eigenvectorBasis, real_inner_smul_left,
      real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one] using hh
  have hr := relative_form_nonnegative A D η hη hA hD hpos hrelative v
  have hf := shifted_absolute_form b c a ha hc v
  have hdiag : diagonalMap b c = H := (spectral_diagonalization H hH).symm
  rw [hdiag] at hf
  exact hr.trans (mul_le_mul_of_nonneg_left hf hη)


lemma relative_norm_of_weighted_columns {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (D : E →L[ℝ] E) (η : ℝ) (hη : 0 ≤ η)
    (hker : ∀ i, c i = 0 → D (b i) = 0)
    (hcolumns : ∑ i, (c i)⁻¹ ^ 2 * ‖D (b i)‖ ^ 2 ≤ η ^ 2) (x : E) :
    ‖D x‖ ≤ η * ‖diagonalMap b c x‖ := by
  let B := D.comp (diagonalMap b (fun i => (c i)⁻¹))
  have hfactor : B (diagonalMap b c x) = D x := by
    change D ((diagonalMap b (fun i => (c i)⁻¹)).comp (diagonalMap b c) x) = D x
    rw [diagonalMap_comp, diagonalMap_apply, map_sum]
    nth_rw 2 [← b.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul]
    by_cases hi : c i = 0
    · rw [hker i hi]
      simp
    · rw [inv_mul_cancel₀ hi, one_mul]
  have hBi (i : ι) : B (b i) = (c i)⁻¹ • D (b i) := by
    change D (diagonalMap b (fun j => (c j)⁻¹) (b i)) = _
    have he : diagonalMap b (fun j => (c j)⁻¹) (b i) = (c i)⁻¹ • b i := by
      apply b.repr.injective
      ext j
      simp only [diagonalMap_coordinate, map_smul, PiLp.smul_apply, smul_eq_mul]
      by_cases hj : i = j
      · subst j
        rfl
      · have hz : b.repr (b i) j = 0 := by
          rw [b.repr_apply_apply]
          exact b.orthonormal.inner_eq_zero (Ne.symm hj)
        rw [hz]
        simp
    rw [he, map_smul]
  have hBsq := SpectralMirrorGeometry.opNorm_sq_le_columns b B
  simp_rw [hBi, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hBsq
  have hBnorm : ‖B‖ ≤ η := (sq_le_sq₀ (norm_nonneg B) hη).mp (hBsq.trans hcolumns)
  rw [← hfactor]
  exact (B.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg _))


lemma relative_perturbation_nonnegative (H D : E →L[ℝ] E) (η : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hH : H.toLinearMap.IsSymmetric) (hD : D.toLinearMap.IsSymmetric)
    (hpsd : ∀ v : E, 0 ≤ ⟪v, H v⟫)
    (hrelative : ∀ v : E, ‖D v‖ ≤ η * ‖H v‖) (v : E) :
    0 ≤ ⟪v, (H + D) v⟫ := by
  have hh := relative_form_nonnegative H D η hη hH hD
    (fun x => by rw [real_inner_comm]; exact hpsd x) hrelative v
  have hlo := neg_abs_le ⟪v, D v⟫
  have hp := mul_nonneg (show 0 ≤ 1 - η by linarith) (hpsd v)
  simp only [add_apply, inner_add_right]
  nlinarith [hh, hlo, hp]

end LongTails.Proofs.CoupledCubicGeometry
