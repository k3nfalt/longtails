import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.AuxiliaryCertificates

open scoped RealInnerProductSpace
open Set OracleTemplate.NonlinearTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def breg (q : E → ℝ) (dq : E → E) (u v : E) : ℝ := q u - q v - ⟪dq v, u - v⟫

lemma sq_breg (c : ℝ) (p u w : E) :
    c * ‖u - p‖ ^ 2 - c * ‖w - p‖ ^ 2 - ⟪(2 * c) • (w - p), u - w⟫ = c * ‖u - w‖ ^ 2 := by
  have h1 : u - p = (w - p) + (u - w) := by abel
  rw [h1, norm_add_sq_real, real_inner_smul_left]
  ring

lemma breg_two_quad (F : E → ℝ) (G : E → E) (c₁ c₂ : ℝ) (p₁ p₂ u w : E) :
    (F u + c₁ * ‖u - p₁‖ ^ 2 + c₂ * ‖u - p₂‖ ^ 2) - (F w + c₁ * ‖w - p₁‖ ^ 2 + c₂ * ‖w - p₂‖ ^ 2) -
      ⟪G w + (2 * c₁) • (w - p₁) + (2 * c₂) • (w - p₂), u - w⟫ =
      breg F G u w + (c₁ + c₂) * ‖u - w‖ ^ 2 := by
  have h1 := sq_breg c₁ p₁ u w
  have h2 := sq_breg c₂ p₂ u w
  simp only [breg, inner_add_left]
  linarith

lemma breg_three_quad (F : E → ℝ) (G : E → E) (c₁ c₂ c₃ : ℝ) (p₁ p₂ u w : E) :
    (F u + c₁ * ‖u - p₁‖ ^ 2 + c₂ * ‖u - p₂‖ ^ 2 + c₃ * ‖u‖ ^ 2) -
      (F w + c₁ * ‖w - p₁‖ ^ 2 + c₂ * ‖w - p₂‖ ^ 2 + c₃ * ‖w‖ ^ 2) -
      ⟪G w + (2 * c₁) • (w - p₁) + (2 * c₂) • (w - p₂) + (2 * c₃) • w, u - w⟫ =
      breg F G u w + (c₁ + c₂ + c₃) * ‖u - w‖ ^ 2 := by
  have h1 := sq_breg c₁ p₁ u w
  have h2 := sq_breg c₂ p₂ u w
  have h3 := sq_breg c₃ 0 u w
  simp only [sub_zero] at h3
  simp only [breg, inner_add_left]
  linarith

lemma breg_one_quad (F : E → ℝ) (G : E → E) (c₁ : ℝ) (p₁ u w : E) :
    (F u + c₁ * ‖u - p₁‖ ^ 2) - (F w + c₁ * ‖w - p₁‖ ^ 2) - ⟪G w + (2 * c₁) • (w - p₁), u - w⟫ =
      breg F G u w + c₁ * ‖u - w‖ ^ 2 := by
  have h1 := sq_breg c₁ p₁ u w
  simp only [breg, inner_add_left]
  linarith

lemma breg_abs_le [CompleteSpace E] {q : E → ℝ} {dq : E → E} {ℓ : ℝ}
    (hq : ∀ x, HasGradientAt q (dq x) x) (hl : ∀ x y, ‖dq x - dq y‖ ≤ ℓ * ‖x - y‖) (u v : E) :
    |breg q dq u v| ≤ ℓ / 2 * ‖u - v‖ ^ 2 := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound hq hl v u
  have hq' : ∀ x, HasGradientAt (fun x => -q x) (-dq x) x := by
    intro x
    have h := (hq x).hasFDerivAt.neg
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact h
  have hl' : ∀ x y, ‖-dq x - -dq y‖ ≤ ℓ * ‖x - y‖ := by
    intro x y
    rw [show -dq x - -dq y = -(dq x - dq y) by abel, norm_neg]
    exact hl x y
  have hlo := OracleTemplate.Gradient.smooth_upper_bound hq' hl' v u
  rw [abs_le]
  simp only [breg, inner_neg_left] at hup hlo ⊢
  constructor <;> linarith

lemma breg_sub_eq (f h : E → ℝ) (df dh : E → E) (u v : E) :
    breg (fun x => f x - h x) (fun x => df x - dh x) u v = breg f df u v - breg h dh u v := by
  simp only [breg, inner_sub_left]
  ring

lemma transfer_g {Df Dg α n : ℝ} (h : Dg = Df + α * n) (hfail : Dg < α / 2 * n) :
    Df < -(α / 2) * n := by
  linarith

lemma transfer_T {Df Dphi DT Dpsi α db δ n : ℝ} (hT : DT = Df + (α + db) * n)
    (hpsi : Dpsi = Df - Dphi + (α + db + db) * n) (hphi : |Dphi| ≤ δ / 2 * n) (hδ : δ ≤ db)
    (hα : 0 ≤ α) (hn : 0 ≤ n) (hfail : DT < 2 / 5 * Dpsi) : Df < -(α / 2) * n := by
  by_contra hc
  push Not at hc
  have h1 := (abs_le.mp hphi).1
  have h2 := mul_le_mul_of_nonneg_right hδ hn
  have h3 := mul_nonneg hα hn
  nlinarith

lemma transfer_psi {Df Dphi Dpsi α db δ n : ℝ}
    (hpsi : Dpsi = Df - Dphi + (α + db + db) * n) (hphi : |Dphi| ≤ δ / 2 * n) (hδ : δ ≤ db)
    (hα : 0 ≤ α) (hn : 0 ≤ n) (hfail : Dpsi < 3 * db / 2 * n) : Df < -(α / 2) * n := by
  have h1 := (abs_le.mp hphi).2
  have h2 := mul_le_mul_of_nonneg_right hδ hn
  have h3 := mul_nonneg hα hn
  nlinarith

lemma T_le_psi {Df Dphi DT Dpsi α db δ n : ℝ} (hT : DT = Df + (α + db) * n)
    (hpsi : Dpsi = Df - Dphi + (α + db + db) * n) (hphi : |Dphi| ≤ δ / 2 * n) (hδ : δ ≤ db)
    (hn : 0 ≤ n) (hdb : 0 ≤ db) : DT ≤ Dpsi := by
  have h1 := (abs_le.mp hphi).2
  have h2 := mul_le_mul_of_nonneg_right hδ hn
  have h3 := mul_nonneg hdb hn
  nlinarith

section Hessian

variable [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma line_deriv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (H : E →L[ℝ] E) (w d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (w + s • d) - s * ⟪gradient f w, d⟫ - s ^ 2 / 2 * ⟪H d, d⟫)
      ⟪gradient f (w + t • d) - gradient f w - H (t • d), d⟫ t := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h1 := (hfd (w + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const d |>.const_add w)
  simp only [id_eq, one_smul, InnerProductSpace.toDual_apply_apply] at h1
  have h2 := (hasDerivAt_id t).mul_const ⟪gradient f w, d⟫
  have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const ⟪H d, d⟫
  refine ((h1.sub h2).sub h3).congr_deriv ?_
  simp only [map_smul, inner_sub_left, real_inner_smul_left]
  norm_num

lemma one_dim_bound {F F' : ℝ → ℝ} {C : ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, |F' t| ≤ C) : |F 1 - F 0| ≤ C := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := F) (f' := F')
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using hC t (Ico_subset_Icc_self ht))
  simpa [Real.norm_eq_abs] using h

lemma line_taylor {f : E → ℝ} {ρ : ℝ} (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖) (v D : E) :
    |f (v + D) - f v - ⟪gradient f v, D⟫ - ⟪fderiv ℝ (gradient f) v D, D⟫ / 2| ≤
      ρ * ‖D‖ ^ 3 := by
  set H := fderiv ℝ (gradient f) v
  have hgd : Differentiable ℝ (gradient f) := (gradient_contDiff_one hf).differentiable (by norm_num)
  have hb := one_dim_bound (C := ρ * ‖D‖ ^ 3) (line_deriv hf H v D) (by
    intro t ht
    have hl := gradient_linearization_bound hρ hgd hH v (v + t • D)
    rw [add_sub_cancel_left] at hl
    have hn : ‖t • D‖ ≤ ‖D‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg D) ht.2
    calc
      _ ≤ ‖gradient f (v + t • D) - gradient f v - H (t • D)‖ * ‖D‖ := abs_real_inner_le_norm _ _
      _ ≤ ρ * ‖t • D‖ ^ 2 * ‖D‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg D)
      _ ≤ ρ * ‖D‖ ^ 2 * ‖D‖ := by gcongr
      _ = ρ * ‖D‖ ^ 3 := by ring)
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hb
  convert hb using 2
  ring

lemma curvature_transfer {f : E → ℝ} {ρ R : ℝ} (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (y u w : E) (hu : ‖u - y‖ ≤ R) (hw : ‖w - y‖ ≤ R) :
    |breg f (gradient f) u w - ⟪fderiv ℝ (gradient f) y (u - w), u - w⟫ / 2| ≤
      ρ * R * ‖u - w‖ ^ 2 := by
  set H := fderiv ℝ (gradient f) y
  set d := u - w
  have hgd : Differentiable ℝ (gradient f) := (gradient_contDiff_one hf).differentiable (by norm_num)
  let e : E → E := fun x => gradient f x - H x
  have he (x : E) : HasFDerivAt e (fderiv ℝ (gradient f) x - H) x :=
    (hgd x).hasFDerivAt.sub H.hasFDerivAt
  have hbd (x : E) (hx : x ∈ Metric.closedBall y R) : ‖fderiv ℝ (gradient f) x - H‖ ≤ ρ * R :=
    (hH x y).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx) hρ)
  have hlip (a b : E) (ha : a ∈ Metric.closedBall y R) (hb : b ∈ Metric.closedBall y R) :
      ‖e a - e b‖ ≤ ρ * R * ‖a - b‖ :=
    (convex_closedBall y R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (he x).hasFDerivWithinAt) hbd hb ha
  have hwB : w ∈ Metric.closedBall y R := by simpa [dist_eq_norm] using hw
  have huB : u ∈ Metric.closedBall y R := by simpa [dist_eq_norm] using hu
  have hb := one_dim_bound (C := ρ * R * ‖d‖ ^ 2) (line_deriv hf H w d) (by
    intro t ht
    have hmem : w + t • d ∈ Metric.closedBall y R :=
      (convex_closedBall y R).add_smul_sub_mem hwB huB ht
    have hk := hlip _ _ hmem hwB
    have hid : gradient f (w + t • d) - gradient f w - H (t • d) = e (w + t • d) - e w := by
      simp only [e, map_add]
      abel
    rw [hid]
    have hn : ‖w + t • d - w‖ ≤ ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg d) ht.2
    have hR : 0 ≤ ρ * R := mul_nonneg hρ ((norm_nonneg _).trans hu)
    calc
      _ ≤ ‖e (w + t • d) - e w‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ ρ * R * ‖w + t • d - w‖ * ‖d‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg d)
      _ ≤ ρ * R * ‖d‖ * ‖d‖ := by gcongr
      _ = ρ * R * ‖d‖ ^ 2 := by ring)
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hb
  have hwd : w + d = u := by simp [d]
  rw [hwd] at hb
  convert hb using 2
  simp only [breg, d]
  ring

lemma exploit_step {f : E → ℝ} {ρ α η : ℝ} (hf : ContDiff ℝ 2 f) (hρ : 0 < ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (y d : E) (hd : ‖d‖ = 1) (hcurv : ⟪fderiv ℝ (gradient f) y d, d⟫ ≤ -(α / 2))
    (hη : η = α / (8 * ρ)) (hα : 0 ≤ α) :
    f (y + η • d) ≤ f y - α ^ 3 / (512 * ρ ^ 2) ∨ f (y - η • d) ≤ f y - α ^ 3 / (512 * ρ ^ 2) := by
  set H := fderiv ℝ (gradient f) y
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hnorm : ‖η • d‖ = η := by rw [norm_smul, hd, Real.norm_eq_abs, abs_of_nonneg hη0, mul_one]
  have hnorm' : ‖-(η • d)‖ = η := by rw [norm_neg, hnorm]
  have hp := (abs_le.mp (line_taylor hf hρ.le hH y (η • d))).2
  have hm := (abs_le.mp (line_taylor hf hρ.le hH y (-(η • d)))).2
  rw [hnorm] at hp
  rw [hnorm'] at hm
  have hq1 : ⟪H (η • d), η • d⟫ = η ^ 2 * ⟪H d, d⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  have hq2 : ⟪H (-(η • d)), -(η • d)⟫ = η ^ 2 * ⟪H d, d⟫ := by
    rw [map_neg, inner_neg_left, inner_neg_right, neg_neg, hq1]
  have hl1 : ⟪gradient f y, -(η • d)⟫ = -(η * ⟪gradient f y, d⟫) := by
    rw [inner_neg_right, real_inner_smul_right]
  have hl2 : ⟪gradient f y, η • d⟫ = η * ⟪gradient f y, d⟫ := real_inner_smul_right _ _ _
  rw [hq1, hl2] at hp
  rw [hq2, hl1, ← sub_eq_add_neg] at hm
  have hcube : ρ * η ^ 3 = α ^ 3 / (512 * ρ ^ 2) := by
    rw [hη]; field_simp; ring
  have hsq : η ^ 2 * (α / 2) / 2 = 2 * (α ^ 3 / (512 * ρ ^ 2)) := by
    rw [hη]; field_simp; ring
  have hc2 : η ^ 2 * ⟪H d, d⟫ ≤ η ^ 2 * (-(α / 2)) := mul_le_mul_of_nonneg_left hcurv (sq_nonneg η)
  rcases le_total (η * ⟪gradient f y, d⟫) 0 with hs | hs
  · left; nlinarith
  · right; nlinarith

lemma certificate_progress {f : E → ℝ} {ρ α η : ℝ} (hf : ContDiff ℝ 2 f) (hρ : 0 < ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hα : 0 ≤ α) (hη : η = α / (8 * ρ)) (y u w : E) (hne : u ≠ w)
    (hu : ‖u - y‖ ≤ α / (4 * ρ)) (hw : ‖w - y‖ ≤ α / (4 * ρ))
    (hcert : breg f (gradient f) u w < -(α / 2) * ‖u - w‖ ^ 2) :
    f (y + η • (‖u - w‖⁻¹ • (u - w))) ≤ f y - α ^ 3 / (512 * ρ ^ 2) ∨
      f (y - η • (‖u - w‖⁻¹ • (u - w))) ≤ f y - α ^ 3 / (512 * ρ ^ 2) := by
  set H := fderiv ℝ (gradient f) y
  have hct := (abs_le.mp (curvature_transfer hf hρ.le hH y u w hu hw)).1
  have hR : ρ * (α / (4 * ρ)) = α / 4 := by field_simp
  rw [hR] at hct
  have hpos : 0 < ‖u - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hq : ⟪H (u - w), u - w⟫ < -(α / 2) * ‖u - w‖ ^ 2 := by nlinarith
  apply exploit_step hf hρ hH y _ _ _ hη hα
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    have hn2 : ‖u - w‖⁻¹ * (‖u - w‖⁻¹ * ⟪H (u - w), u - w⟫) =
        ⟪H (u - w), u - w⟫ / ‖u - w‖ ^ 2 := by field_simp
    rw [hn2, div_le_iff₀ (by positivity)]
    linarith

end Hessian

end LongTails.Proofs.AuxiliaryCertificates
