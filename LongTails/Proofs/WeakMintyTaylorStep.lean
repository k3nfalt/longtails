import LongTails.Proofs.ClippedExtragradientStability

open scoped RealInnerProductSpace

namespace OracleTemplate.WeakMintyTaylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma correction_bound (x z s v : E) {η ρ : ℝ} (hη : 0 < η)
    (hm : -(ρ / 2) * ‖v‖ ^ 2 ≤ ⟪v, x + s - z⟫) :
    ‖x - η • v - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 - ‖s‖ ^ 2 +
      ‖s + η • v‖ ^ 2 + ρ * η * ‖v‖ ^ 2 := by
  have hid := ClippedExtragradient.extragradient_identity x z (-(η⁻¹) • s) v 0 η
  have hs : η • (-(η⁻¹) • s) = -s := by
    rw [smul_smul, mul_neg, mul_inv_cancel₀ hη.ne', neg_one_smul]
  have he : η ^ 2 * ‖v - -(η⁻¹) • s‖ ^ 2 = ‖s + η • v‖ ^ 2 := by
    calc
      η ^ 2 * ‖v - -(η⁻¹) • s‖ ^ 2 = ‖η • (v - -(η⁻¹) • s)‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = ‖s + η • v‖ ^ 2 := by
        congr 2
        rw [smul_sub, hs]
        abel
  simp only [add_zero, hs, sub_neg_eq_add, norm_neg, inner_zero_left, mul_zero,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at hid
  rw [he] at hid
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * η)
  nlinarith

lemma threshold_product {g ε cap : ℝ} (hε : 0 ≤ ε) (hcap : 0 ≤ cap)
    (he : ε ≤ g) (hc : cap ≤ g) : ε * cap ≤ g ^ 2 := by
  nlinarith [mul_le_mul he hc hcap (le_trans hε he)]

lemma relaxed_correction_bound (x z s v : E) {η ρ τ θ : ℝ} (hη : 0 < η)
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hm : -(ρ / 2) * ‖v‖ ^ 2 ≤ ⟪v, x + s - z⟫)
    (he : ‖s + η • v‖ ≤ θ * ‖s‖) :
    ‖x - (τ * η) • v - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 -
      τ * (2 * (1 - θ) - (τ + ρ / η) * (1 + θ) ^ 2) * ‖s‖ ^ 2 := by
  have hi : ‖x - (τ * η) • v - z‖ ^ 2 = ‖x - z‖ ^ 2 -
      2 * τ * η * ⟪v, x + s - z⟫ + 2 * τ * ⟪s + η • v, s⟫ -
      2 * τ * ‖s‖ ^ 2 + τ ^ 2 * η ^ 2 * ‖v‖ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm z x, real_inner_comm v x, real_inner_comm z v]
    ring
  have hs : ⟪s + η • v, s⟫ ≤ θ * ‖s‖ ^ 2 := by
    calc
      _ ≤ ‖s + η • v‖ * ‖s‖ := real_inner_le_norm _ _
      _ ≤ (θ * ‖s‖) * ‖s‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by ring
  have hv : η * ‖v‖ ≤ (1 + θ) * ‖s‖ := by
    have hn := norm_sub_le (s + η • v) s
    rw [show s + η • v - s = η • v by abel, norm_smul,
      Real.norm_of_nonneg hη.le] at hn
    nlinarith
  have hv2 : η ^ 2 * ‖v‖ ^ 2 ≤ (1 + θ) ^ 2 * ‖s‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ η * ‖v‖) hv 2
    simpa only [mul_pow] using hh
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * τ * η)
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * τ)
  have hv' := mul_le_mul_of_nonneg_left hv2
    (by positivity : 0 ≤ τ * (τ + ρ / η))
  have hr : τ * (τ + ρ / η) * (η ^ 2 * ‖v‖ ^ 2) =
      (τ ^ 2 * η ^ 2 + τ * ρ * η) * ‖v‖ ^ 2 := by
    field_simp
  rw [hr] at hv'
  rw [hi]
  linear_combination hm' + hs' + hv'

lemma margin_bracket {δ a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : a ≤ 2 - δ) :
    δ / 4 ≤ 2 * (1 - δ / 16) - (δ / 4 + a) * (1 + δ / 16) ^ 2 := by
  have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (1 + δ / 16))
  have h2 : δ ^ 2 ≤ δ := by nlinarith
  have h3 : 0 ≤ δ ^ 3 := by positivity
  nlinarith

lemma relaxed_progress (x z s v : E) {η ρ δ : ℝ} (hη : 0 < η)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : ρ / η ≤ 2 - δ)
    (hm : -(ρ / 2) * ‖v‖ ^ 2 ≤ ⟪v, x + s - z⟫)
    (he : ‖s + η • v‖ ≤ (δ / 16) * ‖s‖) :
    ‖x - (δ / 4 * η) • v - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 -
      δ ^ 2 / 16 * ‖s‖ ^ 2 := by
  have hb := relaxed_correction_bound x z s v hη hρ (by positivity : 0 ≤ δ / 4) hm he
  have hc := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (margin_bracket hδ hδ1 hr)
      (by positivity : 0 ≤ δ / 4)) (sq_nonneg ‖s‖)
  nlinarith

lemma model_root_norm (J : E →L[ℝ] E) (g s : E) {k : ℝ} (hk : 0 ≤ k)
    (hs : g + J s + (k * ‖s‖) • s = 0) :
    (k * ‖s‖) * (k * ‖s‖ - ‖J‖) ≤ k * ‖g‖ := by
  have heq : (k * ‖s‖) • s = -(g + J s) := by
    exact eq_neg_of_add_eq_zero_right hs
  have hn := norm_add_le g (J s)
  have hj := J.le_opNorm s
  have hh := congrArg norm heq
  rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_neg] at hh
  have hbound : (k * ‖s‖) * ‖s‖ ≤ ‖g‖ + ‖J‖ * ‖s‖ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound hk
  nlinarith

lemma model_root_cap {α L δ k g : ℝ} (hα : 0 ≤ α) (hL : 0 < L)
    (hδ : 0 < δ) (hroot : α * (α - L) ≤ k * g)
    (hcap : k * g ≤ δ * L ^ 2 / 4) : α ≤ (1 + δ / 4) * L := by
  by_contra! h
  have hp : 0 < α - (1 + δ / 4) * L := by linarith
  have hm : 0 < (α - (1 + δ / 4) * L) * (α + δ / 4 * L) := by positivity
  nlinarith [sq_nonneg δ]

lemma model_residual (J : E →L[ℝ] E) (g s v : E) {k M : ℝ} (hk : 0 < k)
    (hg : g ≠ 0) (hmodel : g + J s + (k * ‖s‖) • s = 0)
    (herror : ‖v - g - J s‖ ≤ M * ‖s‖ ^ 2) :
    0 < ‖s‖ ∧ ‖s + (1 / (k * ‖s‖)) • v‖ ≤ (M / k) * ‖s‖ ∧
      ‖v‖ ≤ (k + M) * ‖s‖ ^ 2 := by
  have hs : s ≠ 0 := by intro h; subst s; exact hg (by simpa using hmodel)
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hid : v - g - J s = v + (k * ‖s‖) • s := by
    have he : g + J s = -((k * ‖s‖) • s) := eq_neg_of_add_eq_zero_left hmodel
    calc
      v - g - J s = v - (g + J s) := by abel
      _ = v + (k * ‖s‖) • s := by rw [he, sub_neg_eq_add]
  have heq : s + (1 / (k * ‖s‖)) • v =
      (1 / (k * ‖s‖)) • (v - g - J s) := by
    rw [hid, smul_add, smul_smul, one_div_mul_cancel (mul_ne_zero hk.ne' hr.ne'), one_smul]
    abel
  have hb : ‖s + (1 / (k * ‖s‖)) • v‖ ≤ (M / k) * ‖s‖ := by
    rw [heq, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (1 / (k * ‖s‖)) * (M * ‖s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herror (by positivity)
      _ = _ := by field_simp
  have hn : ‖v‖ ≤ ‖v + (k * ‖s‖) • s‖ + ‖(k * ‖s‖) • s‖ := by
    have := norm_sub_le (v + (k * ‖s‖) • s) ((k * ‖s‖) • s)
    simpa using this
  rw [← hid, norm_smul, Real.norm_of_nonneg (by positivity)] at hn
  exact ⟨hr, hb, by nlinarith⟩

lemma cubic_certificate (J : E →L[ℝ] E) (g s v : E) {L M ρ δ : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrel : ρ * L = 2 * (1 - δ)) (hJ : ‖J‖ ≤ L) (hg : g ≠ 0)
    (hcap : ‖g‖ ≤ δ ^ 2 * L ^ 2 / (64 * M))
    (hmodel : g + J s + ((16 * M / δ) * ‖s‖) • s = 0)
    (herror : ‖v - g - J s‖ ≤ M * ‖s‖ ^ 2) :
    let η := 1 / ((16 * M / δ) * ‖s‖)
    0 < η ∧ ρ / η ≤ 2 - δ ∧ ‖s + η • v‖ ≤ (δ / 16) * ‖s‖ ∧
      ‖v‖ ≤ (17 * M / δ) * ‖s‖ ^ 2 := by
  dsimp only
  have hk : 0 < 16 * M / δ := by positivity
  obtain ⟨hr, he, hv⟩ := model_residual J g s v hk hg hmodel herror
  have hroot := model_root_norm J g s hk.le hmodel
  have hJ' := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ (16 * M / δ) * ‖s‖)
  have hroot' : ((16 * M / δ) * ‖s‖) * ((16 * M / δ) * ‖s‖ - L) ≤
      (16 * M / δ) * ‖g‖ := by nlinarith
  have hcap' := mul_le_mul_of_nonneg_left hcap hk.le
  have heq : (16 * M / δ) * (δ ^ 2 * L ^ 2 / (64 * M)) = δ * L ^ 2 / 4 := by
    field_simp
    ring
  rw [heq] at hcap'
  have hα := model_root_cap (by positivity) hL hδ hroot' hcap'
  have hρα := mul_le_mul_of_nonneg_left hα hρ
  have hmargin : ρ * ((16 * M / δ) * ‖s‖) ≤ 2 - δ := by
    have heq' : ρ * ((1 + δ / 4) * L) = (1 + δ / 4) * (ρ * L) := by ring
    rw [heq', hrel] at hρα
    nlinarith [sq_nonneg δ]
  have hratio : M / (16 * M / δ) = δ / 16 := by field_simp
  rw [hratio] at he
  refine ⟨by positivity, ?_, he, hv.trans ?_⟩
  · simpa only [one_div, div_inv_eq_mul] using hmargin
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖s‖)
    rw [le_div_iff₀ hδ]
    have hid : (16 * M / δ + M) * δ = 16 * M + M * δ := by
      field_simp
    rw [hid]
    have hMδ := mul_le_mul_of_nonneg_left hδ1 hM.le
    nlinarith

lemma fallback_margin {L ρ δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrel : ρ * L = 2 * (1 - δ)) :
    0 < (1 - δ / 4) / L ∧ ρ / ((1 - δ / 4) / L) ≤ 2 - δ := by
  have hpos : 0 < 1 - δ / 4 := by linarith
  refine ⟨div_pos hpos hL, ?_⟩
  rw [div_div_eq_mul_div, div_le_iff₀ hpos, hrel]
  nlinarith [sq_nonneg δ]

lemma fallback_anchor_bound (s g v : E) {L η θ : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hθ : θ ≤ 1) (hηL : η * L ≤ 1) (hηL' : 3 / 4 ≤ η * L)
    (he : ‖s + η • v‖ ≤ θ * ‖s‖) (hlip : ‖g - v‖ ≤ L * ‖s‖) :
    ‖g‖ ≤ 4 * L * ‖s‖ := by
  have hv : η * ‖v‖ ≤ (1 + θ) * ‖s‖ := by
    have hn := norm_sub_le (s + η • v) s
    rw [show s + η • v - s = η • v by abel, norm_smul,
      Real.norm_of_nonneg hη.le] at hn
    nlinarith
  have hg : ‖g‖ ≤ ‖g - v‖ + ‖v‖ := by
    have hh := norm_add_le (g - v) v
    simpa using hh
  have h1 := mul_le_mul_of_nonneg_left hg hη.le
  have h2 := mul_le_mul_of_nonneg_left hlip hη.le
  have h3 := mul_le_mul_of_nonneg_right hηL (norm_nonneg s)
  have h4 := mul_le_mul_of_nonneg_right hθ (norm_nonneg s)
  have hηg : η * ‖g‖ ≤ 3 * ‖s‖ := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hηg hL.le
  have h6 := mul_le_mul_of_nonneg_right hηL' (norm_nonneg g)
  nlinarith

lemma cubic_charge {δ M ε r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 < M)
    (hbound : ε ≤ (17 * M / δ) * r ^ 2) :
    δ ^ 4 * ε / (16384 * M) ≤ δ ^ 2 / 16 * r ^ 2 := by
  have hb : δ * ε ≤ 17 * M * r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hbound hδ.le
    have he : δ * ((17 * M / δ) * r ^ 2) = 17 * M * r ^ 2 := by field_simp
    rw [he] at hh
    exact hh
  have h3 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  have h4 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ δ ^ 3)
  have h5 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ 17 * M * r ^ 2)
  rw [div_le_iff₀ (by positivity : 0 < 16384 * M)]
  nlinarith only [h4, h5, mul_nonneg hM.le (sq_nonneg (δ * r))]

lemma fallback_charge {δ L M ε g r : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (hM : 0 < M) (hε : 0 ≤ ε)
    (he : ε ≤ g) (hcap : δ ^ 2 * L ^ 2 / (64 * M) ≤ g)
    (hbound : g ≤ 4 * L * r) :
    δ ^ 4 * ε / (16384 * M) ≤ δ ^ 2 / 16 * r ^ 2 := by
  have hg : 0 ≤ g := hε.trans he
  have hp := threshold_product hε (by positivity) he hcap
  have hb := pow_le_pow_left₀ hg hbound 2
  have hprod : ε * δ ^ 2 * L ^ 2 ≤ 1024 * M * L ^ 2 * r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hp.trans hb) (by positivity : 0 ≤ 64 * M)
    have heq : 64 * M * (ε * (δ ^ 2 * L ^ 2 / (64 * M))) = ε * δ ^ 2 * L ^ 2 := by field_simp
    rw [heq] at hh
    nlinarith only [hh]
  have hcancel : ε * δ ^ 2 ≤ 1024 * M * r ^ 2 := by
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp (by nlinarith only [hprod])
  have hh := mul_le_mul_of_nonneg_left hcancel (sq_nonneg δ)
  rw [div_le_iff₀ (by positivity : 0 < 16384 * M)]
  nlinarith only [hh]

end OracleTemplate.WeakMintyTaylor
