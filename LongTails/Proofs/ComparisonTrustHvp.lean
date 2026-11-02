import LongTails.Proofs.ComparisonTrustTaylor

namespace LongTails.Proofs.ComparisonTrustHvp

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def proj (u w : E) : E := w - ⟪u, w⟫ • u

omit [FiniteDimensional ℝ E] in
lemma norm_proj_le {u : E} (hu : ‖u‖ = 1) (w : E) : ‖proj u w‖ ≤ ‖w‖ := by
  have h : ‖proj u w‖ ^ 2 = ‖w‖ ^ 2 - ⟪u, w⟫ ^ 2 := by
    unfold proj
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
      real_inner_smul_right, real_inner_comm w u]
    ring
  have : ‖proj u w‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ⟪u, w⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

omit [FiniteDimensional ℝ E] in
lemma proj_self {u : E} (hu : ‖u‖ = 1) : proj u u = 0 := by
  unfold proj
  rw [real_inner_self_eq_norm_sq, hu]
  simp

omit [FiniteDimensional ℝ E] in
lemma proj_sub (u a b : E) : proj u (a - b) = proj u a - proj u b := by
  unfold proj
  rw [inner_sub_right, sub_smul]
  abel

omit [FiniteDimensional ℝ E] in
lemma proj_add (u a b : E) : proj u (a + b) = proj u a + proj u b := by
  unfold proj
  rw [inner_add_right, add_smul]
  abel

omit [FiniteDimensional ℝ E] in
lemma proj_smul (u a : E) (s : ℝ) : proj u (s • a) = s • proj u a := by
  unfold proj
  rw [real_inner_smul_right, smul_sub, smul_smul]

variable {f : E → ℝ} {L ρ : ℝ}

lemma tangential_bound (h : Smooth f L ρ) (hL : 0 ≤ L) (t : Tuning) {x u d v : E} {c δ0 δ : ℝ}
    (hc : ‖gradient f x‖ = c) (hcpos : 0 < c) (hu : ‖u‖ = 1)
    (hδ0 : ‖u - c⁻¹ • gradient f x‖ ≤ δ0) (hv : v ≠ 0) (hτ0 : 0 < t.τ0)
    (hLτ : L * t.τ0 ≤ c / 2)
    (hd : ‖d - ‖gradient f (x + probeStep t v • v)‖⁻¹ •
      gradient f (x + probeStep t v • v)‖ ≤ δ) :
    ‖c • tangential t x u v d - proj u (fderiv ℝ (gradient f) x v)‖ ≤
      (2 * L ^ 2 * t.τ0 / c + 2 * c * δ0 / t.τ0 + ρ * t.τ0 + c * δ / t.τ0) * ‖v‖ := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set τv := probeStep t v with hτvdef
  have hτv : τv = t.τ0 / ‖v‖ := by simp [hτvdef, probeStep, hv]
  have hτvpos : 0 < τv := by rw [hτv]; positivity
  have hτvv : τv * ‖v‖ = t.τ0 := by rw [hτv]; field_simp
  set g := gradient f x
  set H := fderiv ℝ (gradient f) x
  set y := x + τv • v
  set gy := gradient f y
  set N := ‖gy‖
  have hmove : ‖gy - g‖ ≤ L * t.τ0 := by
    have := h.lip y x
    rw [show y - x = τv • v by simp [y], norm_smul, Real.norm_eq_abs, abs_of_pos hτvpos,
      hτvv] at this
    exact this
  have hNc : |N - c| ≤ L * t.τ0 := by
    rw [← hc]
    exact (abs_norm_sub_norm_le gy g).trans hmove
  have hN : c / 2 ≤ N := by
    have := (abs_le.mp hNc).1
    linarith
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  set e2 := gy - g - τv • H v
  have he2 : ‖e2‖ ≤ ρ * t.τ0 ^ 2 / 2 := by
    have := h.grad_taylor x (τv • v)
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hτvpos, hτvv] at this
    exact this
  have hHv : ‖H v‖ ≤ L * ‖v‖ := (H.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h.hess_norm hL x) (norm_nonneg v))
  have hPg : ‖proj u g‖ ≤ c * δ0 := by
    have hpg : proj u g = proj u (g - c • u) := by
      rw [proj_sub, proj_smul, proj_self hu, smul_zero, sub_zero]
    rw [hpg]
    have : g - c • u = (-c) • (u - c⁻¹ • g) := by
      rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hcpos.ne', neg_smul, neg_smul, one_smul]
      abel
    rw [this] at hpg ⊢
    refine (norm_proj_le hu _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hcpos]
    exact mul_le_mul_of_nonneg_left hδ0 hcpos.le
  have htan : tangential t x u v d = τv⁻¹ • proj u d := by
    simp [tangential, hv, proj, hτvdef]
  have hgy : gy = g + τv • H v + e2 := by simp [e2]
  have hdecomp : c • tangential t x u v d - proj u (H v) =
      (c * τv⁻¹) • proj u (d - N⁻¹ • gy) + (c / N - 1) • proj u (H v) +
        (c / (N * τv)) • (proj u g + proj u e2) := by
    rw [htan, proj_sub, proj_smul, hgy, proj_add, proj_add, proj_smul]
    have hτ' : τv ≠ 0 := hτvpos.ne'
    have hN' : N ≠ 0 := hNpos.ne'
    simp only [smul_sub, smul_add, smul_smul]
    have e1 : c * τv⁻¹ * N⁻¹ = c / (N * τv) := by field_simp
    have e3 : c * τv⁻¹ * (N⁻¹ * τv) = c / N := by field_simp
    have e4 : c / (N * τv) * τv = c / N := by field_simp
    rw [e1, e3]
    module
  rw [hdecomp]
  have hd' : ‖proj u (d - N⁻¹ • gy)‖ ≤ δ := (norm_proj_le hu _).trans hd
  have hc1 : |c / N - 1| ≤ 2 * L * t.τ0 / c := by
    rw [show c / N - 1 = (c - N) / N by field_simp, abs_div, abs_of_pos hNpos, abs_sub_comm,
      div_le_div_iff₀ hNpos hcpos]
    have h1 := mul_le_mul_of_nonneg_right hNc hcpos.le
    have h2 : L * t.τ0 * c ≤ L * t.τ0 * (2 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hL hτ0.le)
    linarith
  have hcN : c / (N * τv) ≤ 2 / τv := by
    rw [div_le_div_iff₀ (by positivity) hτvpos]
    nlinarith
  have hP3 : ‖proj u g + proj u e2‖ ≤ c * δ0 + ρ * t.τ0 ^ 2 / 2 :=
    (norm_add_le _ _).trans (add_le_add hPg ((norm_proj_le hu _).trans he2))
  have hinvτ : τv⁻¹ = ‖v‖ / t.τ0 := by rw [hτv, inv_div]
  calc ‖(c * τv⁻¹) • proj u (d - N⁻¹ • gy) + (c / N - 1) • proj u (H v) +
        (c / (N * τv)) • (proj u g + proj u e2)‖
      ≤ ‖(c * τv⁻¹) • proj u (d - N⁻¹ • gy)‖ + ‖(c / N - 1) • proj u (H v)‖ +
        ‖(c / (N * τv)) • (proj u g + proj u e2)‖ := norm_add₃_le
    _ ≤ (c * τv⁻¹) * δ + (2 * L * t.τ0 / c) * (L * ‖v‖) +
        (2 / τv) * (c * δ0 + ρ * t.τ0 ^ 2 / 2) := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < c * τv⁻¹), abs_of_pos (by positivity : 0 < c / (N * τv))]
      gcongr
      exact (norm_proj_le hu _).trans hHv
    _ = (2 * L ^ 2 * t.τ0 / c + 2 * c * δ0 / t.τ0 + ρ * t.τ0 + c * δ / t.τ0) * ‖v‖ := by
      rw [hinvτ, show (2 : ℝ) / τv = 2 * τv⁻¹ by ring, hinvτ]
      field_simp
      ring

def model (H : E →L[ℝ] E) (u : E) (β : ℝ) : E →L[ℝ] E :=
  H + β • (innerSL ℝ u).smulRight u

omit [FiniteDimensional ℝ E] in
lemma model_apply (H : E →L[ℝ] E) (u : E) (β : ℝ) (v : E) :
    model H u β v = H v + (β * ⟪u, v⟫) • u := by
  simp [model, mul_smul]

omit [FiniteDimensional ℝ E] in
lemma model_symmetric {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (u : E) (β : ℝ) :
    (model H u β).toLinearMap.IsSymmetric := by
  intro a b
  simp only [ContinuousLinearMap.coe_coe, model_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  have hab := hH a b
  simp only [ContinuousLinearMap.coe_coe] at hab
  rw [hab, real_inner_comm a u]
  ring

def hvpValue (t : Tuning) (F : Frame E) (v d : E) : E :=
  tangential t F.x F.u v d + (⟪F.Tu, v⟫ + F.κ * ⟪F.u, v⟫) • F.u

lemma hvp_bound (h : Smooth f L ρ) (t : Tuning) (F : Frame E) {c δ K : ℝ}
    {v d du : E} (hu : ‖F.u‖ = 1)
    (hTu : F.Tu = tangential t F.x F.u F.u du)
    (hK : ∀ w dd : E, w ≠ 0 →
      ‖dd - ‖gradient f (F.x + probeStep t w • w)‖⁻¹ • gradient f (F.x + probeStep t w • w)‖ ≤
        δ → ‖c • tangential t F.x F.u w dd - proj F.u (fderiv ℝ (gradient f) F.x w)‖ ≤ K * ‖w‖)
    (hdu : ‖du - ‖gradient f (F.x + probeStep t F.u • F.u)‖⁻¹ •
      gradient f (F.x + probeStep t F.u • F.u)‖ ≤ δ)
    (hd : v ≠ 0 → ‖d - ‖gradient f (F.x + probeStep t v • v)‖⁻¹ •
      gradient f (F.x + probeStep t v • v)‖ ≤ δ):
    ‖c • hvpValue t F v d -
      model (fderiv ℝ (gradient f) F.x) F.u
        (c * F.κ - ⟪F.u, fderiv ℝ (gradient f) F.x F.u⟫) v‖ ≤ 2 * K * ‖v‖ := by
  set H := fderiv ℝ (gradient f) F.x
  set u := F.u
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    norm_num at hu
  have hsym : ⟪u, H v⟫ = ⟪H u, v⟫ := (h.sym F.x u v).symm
  have hHv : H v = proj u (H v) + ⟪u, H v⟫ • u := by simp [proj]
  have hHu : ⟪H u, v⟫ = ⟪proj u (H u), v⟫ + ⟪u, H u⟫ * ⟪u, v⟫ := by
    simp only [proj, inner_sub_left, real_inner_smul_left]
    ring
  have hmodel : model H u (c * F.κ - ⟪u, H u⟫) v =
      proj u (H v) + (⟪proj u (H u), v⟫ + c * F.κ * ⟪u, v⟫) • u := by
    rw [model_apply]
    conv_lhs => rw [hHv]
    rw [hsym, hHu, add_assoc, ← add_smul]
    congr 2
    ring
  have hdiff : c • hvpValue t F v d - model H u (c * F.κ - ⟪u, H u⟫) v =
      (c • tangential t F.x u v d - proj u (H v)) +
        ⟪c • F.Tu - proj u (H u), v⟫ • u := by
    rw [hmodel]
    simp only [hvpValue, smul_add, inner_sub_left, real_inner_smul_left, smul_smul]
    rw [show u = F.u from rfl]
    module
  rw [hdiff]
  have h1 : ‖c • tangential t F.x u v d - proj u (H v)‖ ≤ K * ‖v‖ := by
    by_cases hv : v = 0
    · subst hv
      simp [tangential, proj]
    · exact hK v d hv (hd hv)
  have h2 : ‖c • F.Tu - proj u (H u)‖ ≤ K * ‖u‖ := by
    rw [hTu]
    exact hK u du hune hdu
  rw [hu, mul_one] at h2
  calc _ ≤ ‖c • tangential t F.x u v d - proj u (H v)‖ +
        ‖⟪c • F.Tu - proj u (H u), v⟫ • u‖ := norm_add_le _ _
    _ ≤ K * ‖v‖ + K * ‖v‖ := by
      refine add_le_add h1 ?_
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg v))
    _ = 2 * K * ‖v‖ := by ring

end

end LongTails.Proofs.ComparisonTrustHvp
