import LongTails.Proofs.RelativeCurvatureRecurrence
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace LongTails.Proofs.RelativeCurvatureSpectrum

open scoped RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma quadratic_decomposition (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) (v : E) :
    ⟪v, C v⟫ = ∑ i, eig i * ⟪b i, v⟫ ^ 2 := by
  rw [← b.sum_inner_mul_inner v (C v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]
  have hi : ⟪v, b i⟫ = ⟪b i, v⟫ := real_inner_comm _ _
  rw [hi]
  ring

lemma norm_bound (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ i, |eig i| ≤ M)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) : ‖C‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  have hs : ‖C v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
    rw [← b.sum_sq_inner_right (C v), mul_pow, ← b.sum_sq_inner_right v, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hc, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h := he i
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (eig i)) hM).mpr h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hs

noncomputable def transformed (C : E →L[ℝ] E) (a : ℝ) : E →L[ℝ] E :=
  (1 + a)⁻¹ • ((1 - a) • ContinuousLinearMap.id ℝ E - (2 : ℝ) • C)

omit [Fintype ι] in
lemma transformed_norm (C : E →L[ℝ] E) {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hC : ‖C‖ ≤ 2) : ‖transformed C a‖ ≤ 5 := by
  have hd : 0 < 1 + a := by positivity
  have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hsub := norm_sub_le ((1 - a) • ContinuousLinearMap.id ℝ E) ((2 : ℝ) • C)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha₁),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsub
  have hi := mul_le_mul_of_nonneg_left hid (sub_nonneg.mpr ha₁)
  have hb : ‖(1 - a) • ContinuousLinearMap.id ℝ E - (2 : ℝ) • C‖ ≤ 5 := by linarith
  rw [transformed, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  have hi' : (1 + a)⁻¹ ≤ 1 := (inv_le_one₀ hd).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
  nlinarith

lemma transformed_coordinate (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) (a : ℝ) (i : ι) (v : E) :
    ⟪b i, transformed C a v⟫ = (((1 - a) - 2 * eig i) / (1 + a)) * ⟪b i, v⟫ := by
  simp only [transformed, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, inner_smul_right, inner_sub_right, hc]
  ring

lemma filter_coordinate (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) (a : ℝ) (u : E) (n : ℕ) (i : ι) :
    ⟪b i, RelativeCurvatureRecurrence.exactFilter (transformed C a) u n⟫ =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (((1 - a) - 2 * eig i) / (1 + a)) * ⟪b i, u⟫ := by
  exact RelativeCurvatureRecurrence.coordinate_filter (transformed C a) (innerSL ℝ (b i)).toLinearMap
    (((1 - a) - 2 * eig i) / (1 + a)) (transformed_coordinate C b eig hc a i) u n

lemma filter_shifted_quadratic (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (he : ∀ i, eig i ≤ 1) (u : E) (hu : ‖u‖ ≤ 1) (n : ℕ) :
    let w := RelativeCurvatureRecurrence.exactFilter (transformed C a) u n
    ⟪w, C w⟫ + a * ‖w‖ ^ 2 ≤ 2 := by
  dsimp only
  rw [quadratic_decomposition C b eig hc, ← b.sum_sq_inner_right, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [filter_coordinate C b eig hc]
  have hcoeff : ∑ i, ⟪b i, u⟫ ^ 2 ≤ 1 := by
    rw [b.sum_sq_inner_right]
    nlinarith [norm_nonneg u]
  convert RelativeCurvaturePolynomial.filter_quadratic_bound eig (fun i => ⟪b i, u⟫) ha ha₁ he hcoeff n using 1
  congr 1
  funext i
  ring

lemma filter_norm_growth (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (u : E) (n : ℕ) (i : ι)
    (hi : eig i ≤ -2 * a) :
    Real.exp ((n : ℝ) * Real.sqrt a / 2) / 2 * |⟪b i, u⟫| ≤
      ‖RelativeCurvatureRecurrence.exactFilter (transformed C a) u n‖ := by
  have hg := RelativeCurvaturePolynomial.chebyshev_growth n ha ha₁
    (RelativeCurvaturePolynomial.transformed_gap ha ha₁ hi)
  have ht : 0 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
      (((1 - a) - 2 * eig i) / (1 + a)) := (by positivity : 0 ≤
        Real.exp ((n : ℝ) * Real.sqrt a / 2) / 2).trans hg
  have hp := abs_real_inner_le_norm (b i)
    (RelativeCurvatureRecurrence.exactFilter (transformed C a) u n)
  rw [b.norm_eq_one, one_mul, filter_coordinate C b eig hc, abs_mul, abs_of_nonneg ht] at hp
  exact (mul_le_mul_of_nonneg_right hg (abs_nonneg _)).trans hp

lemma amplified_filter (C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫) {a d : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) (hd : 1 ≤ d) (u : E) (n : ℕ) (i : ι)
    (hi : eig i ≤ -2 * a) (hu : 1 / (2 * d) ≤ ⟪b i, u⟫ ^ 2)
    (hn : 2 * Real.log (16 * d / a) / Real.sqrt a ≤ n) :
    16 ≤ a * ‖RelativeCurvatureRecurrence.exactFilter (transformed C a) u n‖ ^ 2 := by
  have hd0 : 0 < d := by linarith
  have he := RelativeCurvaturePolynomial.sufficient_filter_degree ha ha₁ hd n hn
  have hg := filter_norm_growth C b eig hc ha.le ha₁ u n i hi
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤
    Real.exp ((n : ℝ) * Real.sqrt a / 2) / 2 * |⟪b i, u⟫|) hg 2
  rw [mul_pow, sq_abs] at hs
  have heq : (Real.exp ((n : ℝ) * Real.sqrt a / 2) / 2) ^ 2 =
      Real.exp ((n : ℝ) * Real.sqrt a) / 4 := by
    rw [div_pow, ← Real.exp_nat_mul]
    norm_num
    ring
  rw [heq] at hs
  have hm := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ Real.exp ((n : ℝ) * Real.sqrt a) / 4 by positivity)
  have he' := (div_le_iff₀ ha).mp he
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 * d by positivity)
  have hcanc : 8 * d * (Real.exp ((n : ℝ) * Real.sqrt a) / 4 * (1 / (2 * d))) =
      Real.exp ((n : ℝ) * Real.sqrt a) := by field_simp; ring
  rw [hcanc] at hm'
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8 * d by positivity)
  have hh' := mul_le_mul_of_nonneg_left (hm'.trans hh) ha.le
  nlinarith

section
variable [FiniteDimensional ℝ E]

omit [Fintype ι] in
lemma symmetric_coordinates (C : E →L[ℝ] E) (hC : C.toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (v : E) :
    ⟪hC.eigenvectorBasis rfl i, C v⟫ = hC.eigenvalues rfl i * ⟪hC.eigenvectorBasis rfl i, v⟫ := by
  simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq, ContinuousLinearMap.coe_coe] using
    hC.eigenvectorBasis_apply_self_apply rfl v i

omit [Fintype ι] in
lemma negative_eigenvalue (C : E →L[ℝ] E) (hC : C.toLinearMap.IsSymmetric) {a : ℝ}
    (v : E) (hv : ⟪v, C v⟫ < -a * ‖v‖ ^ 2) :
    ∃ i : Fin (Module.finrank ℝ E), hC.eigenvalues rfl i < -a := by
  by_contra h
  push Not at h
  have he := quadratic_decomposition C (hC.eigenvectorBasis rfl) (hC.eigenvalues rfl)
    (symmetric_coordinates C hC) v
  have hh : -a * ‖v‖ ^ 2 ≤ ⟪v, C v⟫ := by
    rw [he, ← (hC.eigenvectorBasis rfl).sum_sq_inner_right, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _))
  linarith

end

end LongTails.Proofs.RelativeCurvatureSpectrum
