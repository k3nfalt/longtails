import LongTails.Setups.ThirdDerivativeSmoothNonconvex
import LongTails.Proofs.GradientDependentLocal
import LongTails.Proofs.ThirdOrderTaylorBounds
import LongTails.Proofs.QuarticCoefficientBounds

namespace LongTails.Proofs.ThirdOrderObjectiveGeometry

open scoped RealInnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma directional_cubic_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (x v : E) (t : ℝ) :
    |f (x + t • v) - f x - ⟪gradient f x, v⟫ * t -
      ⟪fderiv ℝ (gradient f) x v, v⟫ * t ^ 2 / 2 -
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ * t ^ 3 / 6| ≤
      (L * ‖v‖ ^ 4) * |t| ^ 4 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let path := fun s : ℝ => x + s • v
  have hp (s : ℝ) : HasDerivAt path v s := by
    convert (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const v) using 1
    · funext r
      rfl
    · simp
  obtain ⟨hf₀, hf₁, hf₂⟩ := GradientDependentLocal.derivative_chain hf
  have h₀ (s : ℝ) : HasDerivAt (fun r => f (path r)) ⟪gradient f (path s), v⟫ s := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (hf₀ (path s)).comp_hasDerivAt s (hp s)
  have h₁ (s : ℝ) : HasDerivAt (fun r => ⟪gradient f (path r), v⟫) ⟪H (path s) v, v⟫ s := by
    simpa [H] using HasDerivAt.inner ℝ ((hf₁ (path s)).comp_hasDerivAt s (hp s)) (hasDerivAt_const s v)
  have h₂ (s : ℝ) : HasDerivAt (fun r => ⟪H (path r) v, v⟫) ⟪T (path s) v v, v⟫ s := by
    simpa [H, T] using HasDerivAt.inner ℝ (((hf₂ (path s)).comp_hasDerivAt s (hp s)).clm_apply
      (hasDerivAt_const s v)) (hasDerivAt_const s v)
  have h₃ (s : ℝ) : |⟪T (path s) v v, v⟫ - ⟪T (path 0) v v, v⟫| ≤
      (L * ‖v‖ ^ 4) * |s| := by
    have hi : ⟪T (path s) v v, v⟫ - ⟪T (path 0) v v, v⟫ =
        ⟪(T (path s) - T (path 0)) v v, v⟫ := by
      simp only [sub_apply, inner_sub_left]
    rw [hi]
    calc
      _ ≤ ‖(T (path s) - T (path 0)) v v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T (path s) - T (path 0)‖ * ‖v‖ * ‖v‖) * ‖v‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ (L * ‖path s - path 0‖ * ‖v‖ * ‖v‖) * ‖v‖ := by
        gcongr
        exact hT _ _
      _ = (L * ‖v‖ ^ 4) * |s| := by
        simp only [path, zero_smul, add_zero, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        ring
  have hm := ThirdOrderTaylorBounds.cubic_taylor_bound (by positivity : 0 ≤ L * ‖v‖ ^ 4)
    h₀ h₁ h₂ h₃ t
  simpa [path, H, T] using hm

lemma directional_quartic_nonneg_general {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hgap : ∀ y, f x - f y ≤ Δ) (t : ℝ) :
    0 ≤ Δ + ⟪gradient f x, v⟫ * t + ⟪fderiv ℝ (gradient f) x v, v⟫ * t ^ 2 / 2 +
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ * t ^ 3 / 6 + (L * ‖v‖ ^ 4) * t ^ 4 := by
  have ht := directional_cubic_remainder hf hL hT x v t
  have habs : |t| ^ 4 = t ^ 4 := by
    calc
      _ = (|t| ^ 2) ^ 2 := by ring
      _ = (t ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  rw [habs] at ht
  have hu := (le_abs_self _).trans ht
  have hg := hgap (x + t • v)
  linarith

lemma directional_quartic_nonneg {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hv : ‖v‖ = 1) (hgap : ∀ y, f x - f y ≤ Δ) (t : ℝ) :
    0 ≤ Δ + ⟪gradient f x, v⟫ * t + ⟪fderiv ℝ (gradient f) x v, v⟫ * t ^ 2 / 2 +
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ * t ^ 3 / 6 + L * t ^ 4 := by
  simpa only [hv, one_pow, mul_one] using directional_quartic_nonneg_general hf hL hT x v hgap t

lemma third_directional_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hv : ‖v‖ = 1) (hgap : ∀ y, f x - f y ≤ Δ) :
    ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ ^ 2 ≤
      72 * L * (⟪fderiv ℝ (gradient f) x v, v⟫ + 4 * L * σ) :=
  QuarticCoefficientBounds.third_coefficient_bound
    (directional_quartic_nonneg hf hL.le hT x v hv hgap) hL hσ hΔ

lemma second_directional_lower {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hv : ‖v‖ = 1) (hgap : ∀ y, f x - f y ≤ Δ) :
    -(4 * L * σ) ≤ ⟪fderiv ℝ (gradient f) x v, v⟫ :=
  QuarticCoefficientBounds.second_coefficient_lower
    (directional_quartic_nonneg hf hL.le hT x v hv hgap) hL hσ hΔ

lemma third_diagonal_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hgap : ∀ y, f x - f y ≤ Δ) :
    ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ ^ 2 ≤
      72 * L * ‖v‖ ^ 4 * (⟪fderiv ℝ (gradient f) x v, v⟫ + 4 * L * σ * ‖v‖ ^ 2) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hc : 0 < L * ‖v‖ ^ 4 := by positivity
  have hs : 0 < σ / ‖v‖ ^ 2 := by positivity
  have he : Δ = (L * ‖v‖ ^ 4) * (σ / ‖v‖ ^ 2) ^ 2 := by
    rw [hΔ]
    field_simp
  have hh := QuarticCoefficientBounds.third_coefficient_bound
    (directional_quartic_nonneg_general hf hL.le hT x v hgap) hc hs he
  have hi : 72 * (L * ‖v‖ ^ 4) *
      (⟪fderiv ℝ (gradient f) x v, v⟫ + 4 * (L * ‖v‖ ^ 4) * (σ / ‖v‖ ^ 2)) =
      72 * L * ‖v‖ ^ 4 * (⟪fderiv ℝ (gradient f) x v, v⟫ + 4 * L * σ * ‖v‖ ^ 2) := by
    field_simp
  exact hh.trans_eq hi

lemma hessian_quadratic_lower {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x v : E) (hgap : ∀ y, f x - f y ≤ Δ) :
    -(4 * L * σ) * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫ := by
  by_cases hv : v = 0
  · subst v
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := third_diagonal_bound hf hL hσ hΔ hT x v hgap
  have hp : 0 < 72 * L * ‖v‖ ^ 4 := by positivity
  have hh' := nonneg_of_mul_nonneg_right ((sq_nonneg _).trans hh) hp
  nlinarith

lemma hessian_taylor_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x -
      fderiv ℝ (fderiv ℝ (gradient f)) x (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let h : E → E →L[ℝ] E := fun z => H z - T x z
  have hd := (GradientDependentLocal.derivative_chain hf).2.2
  have hder : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt h (T z - T x) (segment ℝ x y) z :=
    fun z _ => ((hd z).sub (T x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ segment ℝ x y, ‖T z - T x‖ ≤ L * ‖y - x‖ := fun z hz =>
    (hT z x).trans (mul_le_mul_of_nonneg_left
      (OracleTemplate.LocalHiddenConvex.norm_sub_le_of_mem_segment' hz) hL)
  have hm := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hb (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : h y - h x = H y - H x - T x (y - x) := by
    simp only [h, map_sub]
    abel
  rw [he] at hm
  simpa only [pow_two, mul_assoc] using hm

lemma third_swap_first {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x a b : E) :
    fderiv ℝ (fderiv ℝ (gradient f)) x a b =
      fderiv ℝ (fderiv ℝ (gradient f)) x b a := by
  exact ((GradientDependentLocal.gradient_contDiff_two hf).contDiffAt.isSymmSndFDerivAt
    (by norm_num)).eq a b

lemma third_swap_last {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x a b c : E) :
    ⟪fderiv ℝ (fderiv ℝ (gradient f)) x a b, c⟫ =
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x a c, b⟫ := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let path := fun s : ℝ => x + s • a
  have hp : HasDerivAt path a 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const a) using 1
    · funext r
      rfl
    · simp
  have hd := (GradientDependentLocal.derivative_chain hf).2.2
  have hh : HasDerivAt (fun s => H (path s)) (T x a) 0 := by
    simpa [path, H, T, Function.comp_def] using (hd (path 0)).comp_hasDerivAt 0 hp
  have hb := HasDerivAt.inner ℝ (hh.clm_apply (hasDerivAt_const 0 b)) (hasDerivAt_const 0 c)
  have hc := HasDerivAt.inner ℝ (hh.clm_apply (hasDerivAt_const 0 c)) (hasDerivAt_const 0 b)
  have he : (fun s => ⟪H (path s) b, c⟫) = fun s => ⟪H (path s) c, b⟫ := by
    funext s
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) (path s) b c).trans (real_inner_comm _ _)
  rw [he] at hb
  simpa [H, T] using hb.unique hc

lemma third_polarization {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x a b : E) :
    ⟪fderiv ℝ (fderiv ℝ (gradient f)) x (a + b) (a + b), a + b⟫ +
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) x (a - b) (a - b), a - b⟫ -
      2 * ⟪fderiv ℝ (fderiv ℝ (gradient f)) x a a, a⟫ =
      6 * ⟪fderiv ℝ (fderiv ℝ (gradient f)) x a b, b⟫ := by
  simp only [map_add, map_sub, add_apply,
    sub_apply, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [third_swap_first hf x b a, third_swap_last hf x b b a,
    third_swap_first hf x b a]
  ring

lemma third_mixed_unit {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E)
    (S : E ≃L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, |⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫| ≤ C * ‖S v‖ ^ 3)
    {a b : E} (ha : ‖S a‖ ≤ 1) (hb' : ‖S b‖ ≤ 1) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) x a b, b⟫| ≤ 3 * C := by
  have hp : ‖S (a + b)‖ ≤ 2 := by
    rw [map_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hm : ‖S (a - b)‖ ≤ 2 := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hbp := (hb (a + b)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hp 3) hC)
  have hbm := (hb (a - b)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hm 3) hC)
  have hba := (hb a).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) ha 3) hC)
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hbp
  obtain ⟨hm₁, hm₂⟩ := abs_le.mp hbm
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp hba
  have hid := third_polarization hf x a b
  apply abs_le.mpr
  constructor <;> linarith

lemma third_mixed_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E)
    (S : E ≃L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, |⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫| ≤ C * ‖S v‖ ^ 3)
    (a b : E) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) x a b, b⟫| ≤ 3 * C * ‖S a‖ * ‖S b‖ ^ 2 := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hc : b = 0
  · subst b
    simp
  have hna : 0 < ‖S a‖ := norm_pos_iff.mpr (by simpa using ha)
  have hnb : 0 < ‖S b‖ := norm_pos_iff.mpr (by simpa using hc)
  have hunit (v : E) (hv : 0 < ‖S v‖) : ‖S (‖S v‖⁻¹ • v)‖ ≤ 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ hv.ne']
  have hh := third_mixed_unit hf x S hC hb (hunit a hna) (hunit b hnb)
  simp only [map_smul, smul_apply, real_inner_smul_left, real_inner_smul_right,
    abs_mul, abs_of_pos (inv_pos.mpr hna), abs_of_pos (inv_pos.mpr hnb)] at hh
  have hm := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ ‖S a‖ * ‖S b‖ ^ 2)
  field_simp at hm
  nlinarith

end LongTails.Proofs.ThirdOrderObjectiveGeometry
