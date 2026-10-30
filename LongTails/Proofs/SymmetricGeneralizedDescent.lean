import LongTails.Proofs.SymmetricGeneralizedSmooth
import LongTails.Proofs.GdConvex

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SymmetricGeneralizedDescent

open SymmetricGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma objective_ray_deriv {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (y v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • v)) ⟪g (y + t • v), v⟫ t := by
  have h := (hgrad _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const v |>.const_add y)
  simp only [id_eq, one_smul, toDual_apply_apply] at h
  exact h

lemma objective_ray_growth {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    {L0 L1 : ℝ} (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (y v : E) (hy : g y = 0) (hv : ‖v‖ = 1) {T : ℝ} (hT : 0 ≤ T) :
    f (y + T • v) ≤ f y + L0 / L1 ^ 2 * (Real.exp (L1 * T) - 1 - L1 * T) := by
  let B : ℝ → ℝ := fun t => f y + L0 / L1 ^ 2 * (Real.exp (L1 * t) - 1 - L1 * t)
  have hB (t : ℝ) : HasDerivAt B (L0 / L1 * (Real.exp (L1 * t) - 1)) t := by
    have h := ((((hasDerivAt_id t).const_mul L1).exp.sub_const 1).sub
      ((hasDerivAt_id t).const_mul L1)).const_mul (L0 / L1 ^ 2) |>.const_add (f y)
    simp only [id_eq, mul_one] at h
    convert h using 1
    field_simp
  have hderiv (t : ℝ) (ht : t ∈ Ico 0 T) :
      ⟪g (y + t • v), v⟫ ≤ L0 / L1 * (Real.exp (L1 * t) - 1) := by
    have h := gradient_ray_growth hg hL1 hgs y v ht.1
    simp only [hy, norm_zero, mul_zero, add_zero, hv, mul_one] at h
    have hi := real_inner_le_norm (g (y + t • v)) v
    rw [hv, mul_one] at hi
    have he : L1 * (L0 / L1 * (Real.exp (L1 * t) - 1)) =
        L0 * (Real.exp (L1 * t) - 1) := by field_simp
    apply hi.trans
    apply (mul_le_mul_iff_right₀ hL1).mp
    rw [he]
    linarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (objective_ray_deriv hgrad y v t).continuousAt.continuousWithinAt)
    (fun t _ => (objective_ray_deriv hgrad y v t).hasDerivWithinAt)
    (show f (y + (0 : ℝ) • v) ≤ B 0 by simp [B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv ⟨hT, le_rfl⟩
  exact h

lemma warmup_root_cut {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hconv : ConvexOn ℝ univ f) {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar p : E) (hmin : IsMinOn f univ xstar) {h : ℝ} (hh : 1 ≤ h)
    (hG : 2 * L0 * Real.exp h / L1 ≤ ‖g p‖) :
    f p + ⟪g p, xstar - p⟫ + h / (2 * L1) * ‖g p‖ ≤ f xstar := by
  have hzero : g xstar = 0 := by
    apply (toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hgrad xstar).hasFDerivAt
  have hGp : 0 < ‖g p‖ := lt_of_lt_of_le (by positivity) hG
  let v : E := ‖g p‖⁻¹ • g p
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hGp.ne']
  have hi : ⟪g p, v⟫ = ‖g p‖ := by
    dsimp [v]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hb := objective_ray_growth hgrad hg hL1 hgs xstar v hzero hv
    (T := h / L1) (div_nonneg (by linarith) hL1.le)
  have hLh : L1 * (h / L1) = h := by field_simp
  rw [hLh] at hb
  have hc := OracleTemplate.Gradient.convex_support hconv hgrad p (xstar + (h / L1) • v)
  have he : xstar + (h / L1) • v - p = (xstar - p) + (h / L1) • v := by module
  rw [he, inner_add_right, real_inner_smul_right, hi] at hc
  have hN : L0 / L1 ^ 2 * (Real.exp h - 1 - h) ≤ L0 / L1 ^ 2 * Real.exp h := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hN' : L0 / L1 ^ 2 * Real.exp h ≤ ‖g p‖ / (2 * L1) := by
    apply (le_div_iff₀ (show 0 < 2 * L1 by positivity)).mpr
    have heq : L0 / L1 ^ 2 * Real.exp h * (2 * L1) = 2 * L0 * Real.exp h / L1 := by
      field_simp
    rw [heq]
    exact hG
  have hNh : ‖g p‖ / (2 * L1) ≤ h / (2 * L1) * ‖g p‖ := by
    have := mul_le_mul_of_nonneg_right hh (div_nonneg hGp.le (by positivity : 0 ≤ 2 * L1))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
  have hcoef : h / L1 * ‖g p‖ = 2 * (h / (2 * L1) * ‖g p‖) := by field_simp
  linarith

lemma objective_segment_upper {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (y v : E) {M : ℝ}
    (hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖g (y + t • v) - g y‖ ≤ M * t * ‖v‖) :
    f (y + v) ≤ f y + ⟪g y, v⟫ + M / 2 * ‖v‖ ^ 2 := by
  let B : ℝ → ℝ := fun t => f y + t * ⟪g y, v⟫ + t ^ 2 * (M / 2 * ‖v‖ ^ 2)
  have hB (t : ℝ) : HasDerivAt B (⟪g y, v⟫ + M * ‖v‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).mul_const ⟪g y, v⟫ |>.const_add (f y)).add
      (((hasDerivAt_id t).pow 2).mul_const (M / 2 * ‖v‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ⟪g (y + t • v), v⟫ ≤ ⟪g y, v⟫ + M * ‖v‖ ^ 2 * t := by
    have h := (real_inner_le_norm (g (y + t • v) - g y) v).trans
      (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg v))
    rw [inner_sub_left] at h
    nlinarith only [h]
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (objective_ray_deriv hgrad y v t).continuousAt.continuousWithinAt)
    (fun t _ => (objective_ray_deriv hgrad y v t).hasDerivWithinAt)
    (show f (y + (0 : ℝ) • v) ≤ B 0 by simp [B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa [B] using h

lemma objective_upper {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (y v : E) :
    f (y + v) ≤ f y + ⟪g y, v⟫ +
      (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖v‖) / 2 * ‖v‖ ^ 2 := by
  apply objective_segment_upper hgrad y v
  intro t ht
  have h := gradient_difference_bound hg hL0 hL1 hgs (y + t • v) y
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
  calc
    _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * (t * ‖v‖)) * (t * ‖v‖) := h
    _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖v‖) * (t * ‖v‖) := by
      gcongr <;> nlinarith [norm_nonneg v, ht.1, ht.2]
    _ = _ := by ring

lemma normalized_descent {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (p : E) :
    f (p - (1 / (4 * (L0 + L1 * ‖g p‖))) • g p) ≤
      f p - 5 * ‖g p‖ ^ 2 / (24 * (L0 + L1 * ‖g p‖)) := by
  let H := L0 + L1 * ‖g p‖
  let v : E := -(1 / (4 * H)) • g p
  have hH : 0 < H := by dsimp [H]; positivity
  have hv : ‖v‖ = ‖g p‖ / (4 * H) := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    ring
  have hi : ⟪g p, v⟫ = -‖g p‖ ^ 2 / (4 * H) := by
    dsimp [v]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hscale : L1 * ‖v‖ ≤ 1 / 4 := by
    rw [hv, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 4 * H by positivity)).mpr
    dsimp [H]
    linarith
  have hexp : Real.exp (L1 * ‖v‖) ≤ 4 / 3 := by
    apply (Real.exp_le_exp.mpr hscale).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have h := objective_upper hgrad hg hL0.le hL1 hgs p v
  change f (p + v) ≤ f p + ⟪g p, v⟫ + H * Real.exp (L1 * ‖v‖) / 2 * ‖v‖ ^ 2 at h
  have he : p + v = p - (1 / (4 * H)) • g p := by dsimp [v]; module
  rw [he, hi] at h
  calc
    _ ≤ f p + -‖g p‖ ^ 2 / (4 * H) + H * Real.exp (L1 * ‖v‖) / 2 * ‖v‖ ^ 2 := h
    _ ≤ f p + -‖g p‖ ^ 2 / (4 * H) + H * (4 / 3) / 2 * ‖v‖ ^ 2 := by gcongr
    _ = _ := by rw [hv]; dsimp only [H]; field_simp; ring

lemma normalized_distance_le {f : E → ℝ} {g : E → E}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hconv : ConvexOn ℝ univ f) {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar p : E) (hmin : IsMinOn f univ xstar) :
    ‖p - (1 / (4 * (L0 + L1 * ‖g p‖))) • g p - xstar‖ ≤ ‖p - xstar‖ := by
  let H := L0 + L1 * ‖g p‖
  have hH : 0 < H := by dsimp [H]; positivity
  have hd := normalized_descent hgrad hg hL0 hL1 hgs p
  have hm := hmin (mem_univ (p - (1 / (4 * H)) • g p))
  change f xstar ≤ f (p - (1 / (4 * H)) • g p) at hm
  change f (p - (1 / (4 * H)) • g p) ≤ f p - 5 * ‖g p‖ ^ 2 / (24 * H) at hd
  have hc := OracleTemplate.Gradient.convex_support hconv hgrad p xstar
  have hi : ⟪g p, xstar - p⟫ = -⟪g p, p - xstar⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hi] at hc
  have hD : 5 * ‖g p‖ ^ 2 / (24 * H) ≤ ⟪g p, p - xstar⟫ := by linarith
  have hD' := (div_le_iff₀ (show 0 < 24 * H by positivity)).mp hD
  have hinner : ‖g p‖ ^ 2 ≤ 8 * H * ⟪g p, p - xstar⟫ := by
    nlinarith [sq_nonneg ‖g p‖]
  have he : p - (1 / (4 * H)) • g p - xstar =
      (p - xstar) - (1 / (4 * H)) • g p := by module
  have heq : ‖p - (1 / (4 * H)) • g p - xstar‖ ^ 2 = ‖p - xstar‖ ^ 2 -
      (8 * H * ⟪g p, p - xstar⟫ - ‖g p‖ ^ 2) / (16 * H ^ 2) := by
    rw [he, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity), real_inner_comm (p - xstar) (g p)]
    field_simp
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖p - (1 / (4 * H)) • g p - xstar‖ ^ 2 ≤ ‖p - xstar‖ ^ 2
  rw [heq]
  exact sub_le_self _ (div_nonneg (sub_nonneg.mpr hinner) (by positivity))

end LongTails.Proofs.SymmetricGeneralizedDescent
