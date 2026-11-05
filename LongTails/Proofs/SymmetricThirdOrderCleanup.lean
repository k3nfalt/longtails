import LongTails.Proofs.ThirdOrderBregmanGeometry

namespace LongTails.Proofs.SymmetricThirdOrderCleanup

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma scaled_quadratic_descent {g s : E} {B : E →L[ℝ] E} {δ θ : ℝ}
    (hδ : 0 ≤ δ) (hB : 0 ≤ ⟪B s, s⟫) (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hs : ⟪g, s⟫ + ⟪B s, s⟫ + δ * ‖s‖ ^ 2 ≤ 0) :
    ⟪g, θ • s⟫ + ⟪B (θ • s), θ • s⟫ + δ * ‖θ • s‖ ^ 2 ≤ 0 := by
  simp only [real_inner_smul_right, map_smul, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
  have hq := mul_nonneg hδ (sq_nonneg ‖s‖)
  have hh := mul_le_mul_of_nonneg_left hs hθ
  have hc := mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hθ₁)) (add_nonneg hB hq)
  nlinarith

lemma cleanup_descent {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L a δ : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (y s g : E) (B : E →L[ℝ] E)
    (hg : ‖g - gradient f y‖ ≤ a)
    (hB : ‖B - fderiv ℝ (gradient f) y‖ ≤ δ / 8)
    (hsmall : 2 * L * ‖s‖ ^ 2 ≤ δ / 8)
    (hs : ⟪g, s⟫ + ⟪B s, s⟫ + δ * ‖s‖ ^ 2 ≤ 0) :
    (1 / 4) * ⟪fderiv ℝ (gradient f) y s, s⟫ +
      (3 / 4) * δ * ‖s‖ ^ 2 - a * ‖s‖ ≤ f y - f (y + s) := by
  have hv := ThirdOrderBregmanGeometry.convex_value_upper hf hc hL hT y s
  have he : |⟪g - gradient f y, s⟫| ≤ a * ‖s‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hb : |⟪(B - fderiv ℝ (gradient f) y) s, s⟫| ≤ δ / 8 * ‖s‖ ^ 2 := by
    calc
      _ ≤ ‖(B - fderiv ℝ (gradient f) y) s‖ * ‖s‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B - fderiv ℝ (gradient f) y‖ * ‖s‖) * ‖s‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (δ / 8 * ‖s‖) * ‖s‖ := by gcongr
      _ = _ := by ring
  have hq := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖s‖)
  simp only [sub_apply, inner_sub_left] at he hb
  have heg := (abs_le.mp he).1
  have heb := (abs_le.mp hb).1
  nlinarith

lemma radius_contradiction {a δ t h gap : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (ht : δ * t = 16 * a) (hh : 0 ≤ h) (hgap : δ * gap ≤ 16 * a ^ 2)
    (hdescent : h / 4 + (3 / 4) * δ * t ^ 2 - a * t ≤ gap) : False := by
  have hd := mul_le_mul_of_nonneg_left hdescent hδ.le
  have he := congrArg (fun x : ℝ => x ^ 2) ht
  have hn := mul_nonneg hδ.le hh
  have he₁ := congrArg (fun x : ℝ => a * x) ht
  nlinarith [sq_pos_of_pos ha]

lemma cleanup_curvature {a δ t h gap : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (ht : δ * t ≤ 16 * a) (hgap : δ * gap ≤ 16 * a ^ 2)
    (hdescent : h / 4 + (3 / 4) * δ * t ^ 2 - a * t ≤ gap) :
    δ * h ≤ 128 * a ^ 2 := by
  have hd := mul_le_mul_of_nonneg_left hdescent hδ.le
  have he := mul_le_mul_of_nonneg_left ht ha
  nlinarith [sq_nonneg (δ * t)]

lemma cleanup_bregman {a δ L t h D : ℝ} (hδ : 0 < δ)
    (ht₀ : 0 ≤ t) (ht : δ * t ≤ 16 * a)
    (hsmall : 2 * L * t ^ 2 ≤ δ / 8) (hh : δ * h ≤ 128 * a ^ 2)
    (hD : D ≤ (3 / 4) * h + 2 * L * t ^ 4) :
    δ * D ≤ 128 * a ^ 2 := by
  have ht₂ : (δ * t) ^ 2 ≤ (16 * a) ^ 2 := by gcongr
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
  have hsδ := mul_le_mul_of_nonneg_left hs hδ.le
  have hd := mul_le_mul_of_nonneg_left hD hδ.le
  nlinarith

lemma radius_small {a δ L r : ℝ} (hδ : 0 < δ)
    (hr : δ * r = 16 * a) (htune : 4096 * L * a ^ 2 ≤ δ ^ 3) :
    2 * L * r ^ 2 ≤ δ / 8 := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hδ)).mp
  have he := congrArg (fun x : ℝ => L * x ^ 2) hr
  nlinarith

lemma cleanup_short_step {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L a δ : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    {C : Set E} (hC : Convex ℝ C) (y s g : E) (B : E →L[ℝ] E)
    (hy : y ∈ C) (hz : y + s ∈ C)
    (hgap : ∀ v ∈ C, δ * (f y - f v) ≤ 16 * a ^ 2)
    (hg : ‖g - gradient f y‖ ≤ a)
    (hB : ‖B - fderiv ℝ (gradient f) y‖ ≤ δ / 8)
    (hpos : 0 ≤ ⟪B s, s⟫)
    (htune : 4096 * L * a ^ 2 ≤ δ ^ 3)
    (hs : ⟪g, s⟫ + ⟪B s, s⟫ + δ * ‖s‖ ^ 2 ≤ 0) :
    ‖s‖ < 16 * a / δ := by
  by_contra hshort
  have hlong : 16 * a / δ ≤ ‖s‖ := le_of_not_gt hshort
  have hn : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) hlong
  let θ := (16 * a / δ) / ‖s‖
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ₁ : θ ≤ 1 := (div_le_one hn).mpr hlong
  have he : δ * ‖θ • s‖ = 16 * a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    dsimp [θ]
    field_simp
  have hmem : y + θ • s ∈ C := by
    have hm := hC hy hz (sub_nonneg.mpr hθ₁) hθ (by ring : 1 - θ + θ = 1)
    convert hm using 1
    module
  have hscaled := scaled_quadratic_descent hδ.le hpos hθ hθ₁ hs
  have hsmall := radius_small hδ he htune
  have hdes := cleanup_descent hf hc hL hT y (θ • s) g B hg hB hsmall hscaled
  exact radius_contradiction ha hδ he
    (ThirdOrderBregmanGeometry.convex_hessian_nonneg hf hc y (θ • s))
    (hgap _ hmem) (by linarith)

lemma step_small {a δ L t : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (ht₀ : 0 ≤ t) (ht : δ * t ≤ 16 * a) (htune : 4096 * L * a ^ 2 ≤ δ ^ 3) :
    2 * L * t ^ 2 ≤ δ / 8 := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hδ)).mp
  have he : (δ * t) ^ 2 ≤ (16 * a) ^ 2 := by gcongr
  have hm := mul_le_mul_of_nonneg_left he hL
  nlinarith

lemma cleanup_residual {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L a δ : ℝ} (hL : 0 < L)
    (ha : 0 ≤ a) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (y s g : E) (B : E →L[ℝ] E)
    (hgap : δ * (f y - f (y + s)) ≤ 16 * a ^ 2)
    (hg : ‖g - gradient f y‖ ≤ a)
    (hB : ‖B - fderiv ℝ (gradient f) y‖ ≤ δ / 8)
    (htune : 4096 * L * a ^ 2 ≤ δ ^ 3)
    (hshort : δ * ‖s‖ ≤ 16 * a)
    (hs : ⟪g, s⟫ + ⟪B s, s⟫ + δ * ‖s‖ ^ 2 ≤ 0) :
    ‖gradient f (y + s) - g - B s - δ • s‖ ≤ 35 * a := by
  have hsmall := step_small hδ hL.le (norm_nonneg s) hshort htune
  have hdes := cleanup_descent hf hc hL.le hT y s g B hg hB hsmall hs
  have hh := cleanup_curvature ha hδ hshort hgap (by linarith :
    ⟪fderiv ℝ (gradient f) y s, s⟫ / 4 + (3 / 4) * δ * ‖s‖ ^ 2 -
      a * ‖s‖ ≤ f y - f (y + s))
  have hv := ThirdOrderBregmanGeometry.convex_value_upper hf hc hL.le hT y s
  have hD := cleanup_bregman hδ (norm_nonneg s) hshort hsmall hh
    (by dsimp [ThirdOrderBregmanGeometry.translatedGap]; linarith :
      ThirdOrderBregmanGeometry.translatedGap f s y ≤
        (3 / 4) * ⟪fderiv ℝ (gradient f) y s, s⟫ + 2 * L * ‖s‖ ^ 4)
  have hr := ThirdOrderBregmanGeometry.residual_self_bound hf hc hL hT s y
  have hDn := ThirdOrderBregmanGeometry.translatedGap_nonneg hf hc s y
  have hm := mul_le_mul_of_nonneg_right hsmall hDn
  have hrn : ‖ThirdOrderBregmanGeometry.residual f s y‖ ≤ 4 * a := by
    nlinarith [norm_nonneg (ThirdOrderBregmanGeometry.residual f s y)]
  have hgn : ‖gradient f y - g‖ ≤ a := by rwa [norm_sub_rev]
  have hbn : ‖(fderiv ℝ (gradient f) y - B) s‖ ≤ 2 * a := by
    calc
      _ ≤ ‖fderiv ℝ (gradient f) y - B‖ * ‖s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ / 8 * ‖s‖ := by rw [norm_sub_rev]; gcongr
      _ ≤ 2 * a := by linarith
  have he : gradient f (y + s) - g - B s - δ • s =
      ThirdOrderBregmanGeometry.residual f s y + (gradient f y - g) +
        (fderiv ℝ (gradient f) y - B) s - δ • s := by
    simp only [ThirdOrderBregmanGeometry.residual, sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖ThirdOrderBregmanGeometry.residual f s y + (gradient f y - g) +
        (fderiv ℝ (gradient f) y - B) s‖ + ‖δ • s‖ := norm_sub_le _ _
    _ ≤ ‖ThirdOrderBregmanGeometry.residual f s y‖ + ‖gradient f y - g‖ +
        ‖(fderiv ℝ (gradient f) y - B) s‖ + ‖δ • s‖ := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 35 * a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      linarith

omit [FiniteDimensional ℝ E] in
lemma quadratic_variational_descent {C : Set E} {y s g : E}
    {B : E →L[ℝ] E} {δ : ℝ} (hy : y ∈ C)
    (hvi : ∀ v ∈ C, 0 ≤ ⟪g + B s + δ • s, v - (y + s)⟫) :
    ⟪g, s⟫ + ⟪B s, s⟫ + δ * ‖s‖ ^ 2 ≤ 0 := by
  have hh := hvi y hy
  have he : y - (y + s) = -s := by abel
  rw [he] at hh
  simp only [inner_neg_right, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hh
  linarith

omit [FiniteDimensional ℝ E] in
lemma quadratic_variational_normal {C : Set E} {y s g : E}
    {B : E →L[ℝ] E} {δ : ℝ}
    (hvi : ∀ v ∈ C, 0 ≤ ⟪g + B s + δ • s, v - (y + s)⟫) :
    ∀ v ∈ C, ⟪-g - B s - δ • s, v - (y + s)⟫ ≤ 0 := by
  intro v hv
  have hh := hvi v hv
  simp only [inner_add_left, inner_sub_left, inner_neg_left] at hh ⊢
  linarith

end LongTails.Proofs.SymmetricThirdOrderCleanup
