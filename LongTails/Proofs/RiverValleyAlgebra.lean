import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def Smap (J : E →L[ℝ] E) : E →L[ℝ] E := 1 + J.comp (ContinuousLinearMap.adjoint J)

lemma Smap_inner (J : E →L[ℝ] E) (z : E) :
    ⟪Smap J z, z⟫ = ‖z‖ ^ 2 + ‖ContinuousLinearMap.adjoint J z‖ ^ 2 := by
  simp only [Smap, add_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, inner_add_left, real_inner_self_eq_norm_sq]
  rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma Smap_symm (J : E →L[ℝ] E) (x y : E) : ⟪Smap J x, y⟫ = ⟪x, Smap J y⟫ := by
  simp only [Smap, add_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_add_right]
  rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]

lemma Smap_lower (J : E →L[ℝ] E) (z : E) : ‖z‖ ≤ ‖Smap J z‖ := by
  have h1 := Smap_inner J z
  have h2 := real_inner_le_norm (Smap J z) z
  by_cases hz : ‖z‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint J z‖]

lemma Smap_injective (J : E →L[ℝ] E) : Function.Injective (Smap J) := by
  intro x y hxy
  have h := Smap_lower J (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

noncomputable def Sinv (J : E →L[ℝ] E) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo ((Smap J : E →L[ℝ] E) : E →ₗ[ℝ] E) (Smap_injective J)

lemma Smap_Sinv (J : E →L[ℝ] E) (y : E) : Smap J ((Sinv J).symm y) = y :=
  (Sinv J).apply_symm_apply y

lemma Sinv_Smap (J : E →L[ℝ] E) (z : E) : (Sinv J).symm (Smap J z) = z :=
  (Sinv J).symm_apply_apply z

lemma Sinv_norm (J : E →L[ℝ] E) (y : E) : ‖(Sinv J).symm y‖ ≤ ‖y‖ := by
  have h := Smap_lower J ((Sinv J).symm y)
  rwa [Smap_Sinv] at h

lemma adjoint_norm (J : E →L[ℝ] E) : ‖ContinuousLinearMap.adjoint J‖ = ‖J‖ :=
  LinearIsometryEquiv.norm_map _ _

lemma Smap_sub_norm (J J' : E →L[ℝ] E) :
    ‖Smap J - Smap J'‖ ≤ ‖J - J'‖ * (‖J‖ + ‖J'‖) := by
  have e : Smap J - Smap J' = (J - J').comp (ContinuousLinearMap.adjoint J) +
      J'.comp (ContinuousLinearMap.adjoint (J - J')) := by
    simp only [Smap, map_sub]
    ext z
    simp only [sub_apply, add_apply,
      one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [e]
  calc _ ≤ ‖(J - J').comp (ContinuousLinearMap.adjoint J)‖ +
        ‖J'.comp (ContinuousLinearMap.adjoint (J - J'))‖ := norm_add_le _ _
    _ ≤ ‖J - J'‖ * ‖J‖ + ‖J'‖ * ‖J - J'‖ := by
        gcongr
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [adjoint_norm])
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [adjoint_norm])
    _ = ‖J - J'‖ * (‖J‖ + ‖J'‖) := by ring

lemma Sinv_sub (J J' : E →L[ℝ] E) (y : E) :
    ‖(Sinv J).symm y - (Sinv J').symm y‖ ≤ ‖Smap J - Smap J'‖ * ‖y‖ := by
  set z := (Sinv J').symm y
  have e : (Sinv J).symm y - z = (Sinv J).symm ((Smap J' - Smap J) z) := by
    apply Smap_injective J
    rw [Smap_Sinv, map_sub, Smap_Sinv, sub_apply, Smap_Sinv]
  rw [e]
  calc _ ≤ ‖(Smap J' - Smap J) z‖ := Sinv_norm J _
    _ ≤ ‖Smap J' - Smap J‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Smap J - Smap J'‖ * ‖y‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (Sinv_norm J' y) (norm_nonneg _)

noncomputable def mvec (J : E →L[ℝ] E) (a : E) : E := (Sinv J).symm (J a)

lemma mvec_bounds (J : E →L[ℝ] E) {Γ : ℝ} (hΓ : 0 ≤ Γ) (hJ : ‖J‖ ≤ Γ) (a : E) :
    ‖mvec J a‖ ≤ Γ * ‖a‖ ∧ (1 + Γ ^ 2) * ⟪mvec J a, J a⟫ ≤ Γ ^ 2 * ‖a‖ ^ 2 := by
  set m := mvec J a
  set s := ‖ContinuousLinearMap.adjoint J m‖
  have hSm : Smap J m = J a := Smap_Sinv J _
  have h1 : ‖m‖ ^ 2 + s ^ 2 = ⟪m, J a⟫ := by
    rw [← Smap_inner, real_inner_comm, ← hSm]
  have h2 : ⟪m, J a⟫ = ⟪ContinuousLinearMap.adjoint J m, a⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have h3 : ⟪ContinuousLinearMap.adjoint J m, a⟫ ≤ s * ‖a‖ := real_inner_le_norm _ _
  have hs : s ≤ Γ * ‖m‖ := by
    calc s ≤ ‖ContinuousLinearMap.adjoint J‖ * ‖m‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Γ * ‖m‖ := by rw [adjoint_norm]; exact mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hmain : ‖m‖ ^ 2 + s ^ 2 ≤ s * ‖a‖ := by linarith
  constructor
  · by_cases hm : ‖m‖ = 0
    · rw [hm]; positivity
    · have hmp : 0 < ‖m‖ := lt_of_le_of_ne hm0 (Ne.symm hm)
      have : ‖m‖ ^ 2 ≤ Γ * ‖m‖ * ‖a‖ := by nlinarith [mul_le_mul_of_nonneg_right hs ha0]
      nlinarith
  · have key : (1 + Γ ^ 2) * s ≤ Γ ^ 2 * ‖a‖ := by
      by_cases hs' : s = 0
      · rw [hs']; simp; positivity
      · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs')
        have : s ^ 2 ≤ Γ ^ 2 * ‖m‖ ^ 2 := by nlinarith
        have : (1 + Γ ^ 2) * s ^ 2 ≤ Γ ^ 2 * (s * ‖a‖) := by nlinarith
        nlinarith
    have : ⟪m, J a⟫ ≤ s * ‖a‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right key ha0]

end OracleTemplate.RiverValley
