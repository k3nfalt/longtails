import LongTails.Proofs.InterpolatedFiniteSumExponential
import LongTails.Proofs.InterpolatedFiniteSumShield

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InterpolatedFiniteSumLinks

open InterpolatedFiniteSumProfiles InterpolatedFiniteSumShield

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def potential (w : E) (a c : ℝ) (x : E) : ℝ := c * profile (⟪w, x⟫ - a)

noncomputable def field (w : E) (a c : ℝ) (x : E) : E := (c * profileSlope (⟪w, x⟫ - a)) • w

lemma potential_gradient (w : E) (a c : ℝ) (x : E) :
    HasGradientAt (potential w a c) (field w a c x) x := by
  have hd := (((profile_hasDerivAt (⟪w, x⟫ - a)).comp_hasFDerivAt x
    ((InnerProductSpace.toDual ℝ E w).hasFDerivAt.sub_const a)).const_mul c)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext y
    simp only [field, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul]
    ring

lemma field_hasFDerivAt (w : E) (a c : ℝ) (x : E) :
    HasFDerivAt (field w a c)
      (((c * profileCurvature (⟪w, x⟫ - a)) • (InnerProductSpace.toDual ℝ E w)).smulRight w) x := by
  have hd := (((profileSlope_hasDerivAt (⟪w, x⟫ - a)).comp_hasFDerivAt x
    ((InnerProductSpace.toDual ℝ E w).hasFDerivAt.sub_const a)).const_mul c).smul_const w
  convert hd using 1
  · rfl
  · simp only [smul_smul]

lemma field_differentiable (w : E) (a c : ℝ) : Differentiable ℝ (field w a c) :=
  fun x => (field_hasFDerivAt w a c x).differentiableAt

omit [CompleteSpace E] in
lemma potential_convex (w : E) (a c : ℝ) (hc : 0 ≤ c) : ConvexOn ℝ Set.univ (potential w a c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hh := profile_convex.2 (Set.mem_univ (⟪w, x⟫ - a))
    (Set.mem_univ (⟪w, y⟫ - a)) hu hv huv
  have harg : ⟪w, u • x + v • y⟫ - a = u * (⟪w, x⟫ - a) + v * (⟪w, y⟫ - a) := by
    simp only [inner_add_right, inner_smul_right]
    nlinarith only [congrArg (fun z : ℝ => z * a) huv]
  have hm := mul_le_mul_of_nonneg_left hh hc
  simp only [potential, harg, smul_eq_mul] at *
  nlinarith only [hm]

omit [CompleteSpace E] in
lemma potential_nonnegative (w : E) (a c : ℝ) (hc : 0 ≤ c) (x : E) : 0 ≤ potential w a c x :=
  mul_nonneg hc (profile_nonnegative _)

omit [CompleteSpace E] in
lemma field_norm (w : E) (a c : ℝ) (hc : 0 ≤ c) (x : E) : ‖field w a c x‖ ≤ c * ‖w‖ := by
  rw [field, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
  have hh := mul_le_mul_of_nonneg_left (profileSlope_bound (⟪w, x⟫ - a)) hc
  have hm := mul_le_mul_of_nonneg_right hh (norm_nonneg w)
  simpa only [mul_one] using hm

lemma field_curvature (w : E) (a c : ℝ) (hc : 0 ≤ c) (x : E) :
    ‖fderiv ℝ (field w a c) x‖ ≤ 3 * c * ‖w‖ ^ 2 := by
  rw [(field_hasFDerivAt w a c x).fderiv, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (profileCurvature_nonnegative _)),
    (InnerProductSpace.toDual ℝ E).norm_map]
  have hh := mul_le_mul_of_nonneg_left (profileCurvature_bound (⟪w, x⟫ - a)) hc
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖w‖)
  nlinarith only [hm]

omit [CompleteSpace E] in
lemma potential_flat (w : E) (a c : ℝ) (x : E) (hx : |⟪w, x⟫ - a| ≤ 1 / 4) :
    potential w a c x = 0 ∧ field w a c x = 0 := by
  obtain ⟨hv, hg⟩ := profile_flat (⟪w, x⟫ - a) hx
  simp only [potential, field, hv, hg, mul_zero, zero_smul, and_self]

noncomputable def shielded (w : E) (a c r G W : ℝ) : E → ℝ :=
  envelope (potential w a c) (radialWall r G 0 W) W

noncomputable def shieldedField (w : E) (a c r G W : ℝ) : E → E :=
  envelopeField (potential w a c) (radialWall r G 0 W) (field w a c) (radialField r G) W

lemma shielded_gradient (w : E) (a c r G W : ℝ) (hr : 0 < r) (hW : 0 < W) (x : E) :
    HasGradientAt (shielded w a c r G W) (shieldedField w a c r G W x) x :=
  envelope_hasGradientAt _ _ _ _ W hW x (potential_gradient w a c x)
    (radialWall_hasGradientAt r G 0 W hr x)

lemma shielded_differentiable (w : E) (a c r G W : ℝ) (hr : 0 < r) :
    Differentiable ℝ (shieldedField w a c r G W) :=
  envelopeField_differentiable _ _ _ _ W (potential_gradient w a c)
    (radialWall_hasGradientAt r G 0 W hr) (field_differentiable w a c)
    (radialField_differentiable r G hr)

lemma shielded_convex (w : E) (a c r G W : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hG : 0 ≤ G) (hW : 0 < W) : ConvexOn ℝ Set.univ (shielded w a c r G W) :=
  envelope_convex _ _ _ _ W hW (potential_convex w a c hc) (radialWall_convex r G 0 W hr hG)
    (potential_gradient w a c) (radialWall_hasGradientAt r G 0 W hr)

omit [CompleteSpace E] in
lemma shielded_nonnegative (w : E) (a c r G W : ℝ) (hc : 0 ≤ c) (hW : 0 < W) (x : E) :
    0 ≤ shielded w a c r G W x :=
  (potential_nonnegative w a c hc x).trans (smoothMax_above W _ _ hW).1

omit [CompleteSpace E] in
lemma shielded_minimizer_value (w : E) (a c r G W : ℝ) (hc : 0 ≤ c)
    (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (z : E) (hz : ‖z‖ ≤ r) (hw : ⟪w, z⟫ = a) :
    shielded w a c r G W z = 0 := by
  rw [shielded, envelope_radial_interior _ r G 0 W hr hG hW (potential_nonnegative w a c hc) z hz]
  exact (potential_flat w a c z (by rw [hw]; norm_num)).1

omit [CompleteSpace E] in
lemma shieldedField_norm (w : E) (a c r G W : ℝ) (hc : 0 ≤ c) (hr : 0 < r) (hG : 0 ≤ G)
    (hg : c * ‖w‖ ≤ G) (x : E) : ‖shieldedField w a c r G W x‖ ≤ 2 * G := by
  apply envelopeField_norm
  · exact ((field_norm w a c hc x).trans hg).trans (by linarith)
  · exact radialField_norm r G hr hG x

lemma shieldedField_curvature (w : E) (a c r G W L : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hG : 0 ≤ G) (hW : 0 < W) (hL : 0 ≤ L) (hwidth : 64 * G ^ 2 ≤ W * L)
    (hrad : 4 * G / r ≤ L / 3) (hg : c * ‖w‖ ≤ G) (hcurv : 3 * c * ‖w‖ ^ 2 ≤ L / 3) (x : E) :
    ‖fderiv ℝ (shieldedField w a c r G W) x‖ ≤ L :=
  envelope_radial_curvature _ _ r G 0 W L hr hG hW hL hwidth hrad x
    (potential_gradient w a c x) (field_differentiable w a c x)
    ((field_norm w a c hc x).trans hg) ((field_curvature w a c hc x).trans hcurv)

lemma potential_growth (w : E) (a c G : ℝ) (hc : 0 ≤ c) (hg : c * ‖w‖ ≤ G) (x : E) :
    potential w a c x ≤ potential w a c 0 + G * ‖x‖ := by
  have hh := OracleTemplate.Gradient.convex_support (potential_convex w a c hc)
    (potential_gradient w a c) x 0
  have hi := real_inner_le_norm (field w a c x) x
  have hm := mul_le_mul_of_nonneg_right ((field_norm w a c hc x).trans hg) (norm_nonneg x)
  simp only [zero_sub, inner_neg_right] at hh
  linarith only [hh, hi, hm]

lemma shielded_far (w : E) (a c r G W η B : ℝ) (hc : 0 ≤ c) (hG : 0 < G) (hW : 0 < W)
    (hg : c * ‖w‖ ≤ G) (hinit : potential w a c 0 ≤ η)
    (hB : 4 * r + (η + W) / G ≤ B) (x : E) (hx : B ≤ ‖x‖) :
    shielded w a c r G W x = radialWall r G 0 W x ∧
      shieldedField w a c r G W x = radialField r G x := by
  have houter : 4 * r + (potential w a c 0 - 0 + W) / G ≤ ‖x‖ := by
    have hh := div_le_div_of_nonneg_right (add_le_add_right hinit W) hG.le
    have hh' : (potential w a c 0 + W) / G ≤ (η + W) / G := by simpa only [add_comm] using hh
    simp only [sub_zero]
    linarith only [hh', hB, hx]
  exact ⟨envelope_radial_exterior _ r G 0 W hG hW x (potential_growth w a c G hc hg x) houter,
    envelopeField_radial_exterior _ _ r G 0 W hG hW x (potential_growth w a c G hc hg x) houter⟩

omit [CompleteSpace E] in
lemma shielded_far_lower (w : E) (a c r G W η B : ℝ) (hr : 0 ≤ r) (hG : 0 < G)
    (hW : 0 < W) (hη : 0 ≤ η) (hB : 4 * r + (η + W) / G ≤ B) (x : E) (hx : B ≤ ‖x‖) :
    η ≤ shielded w a c r G W x := by
  have hh : η + W ≤ (B - 4 * r) * G := by
    apply (div_le_iff₀ hG).mp
    linarith only [hB]
  have hs := (radiusNorm_ge r x).2
  have hw := (smoothMax_above W (potential w a c x) (radialWall r G 0 W x) hW).2
  change radialWall r G 0 W x ≤ shielded w a c r G W x at hw
  dsimp [radialWall] at hw
  have hGr := mul_nonneg hG.le hr
  have hnorm := mul_le_mul_of_nonneg_left (hx.trans hs) hG.le
  nlinarith only [hh, hw, hGr, hη, hW, hnorm]

omit [CompleteSpace E] in
lemma shielded_flat (w : E) (a c r G W : ℝ) (x : E) (hx : |⟪w, x⟫ - a| ≤ 1 / 4) :
    shielded w a c r G W x = shielded (0 : E) 0 0 r G W x ∧
      shieldedField w a c r G W x = shieldedField (0 : E) 0 0 r G W x := by
  obtain ⟨hv, hg⟩ := potential_flat w a c x hx
  simp only [shielded, shieldedField, envelope, envelopeField, envelopeMix]
  rw [hv, hg]
  simp only [potential, field, zero_mul, zero_smul, and_self]

end LongTails.Proofs.InterpolatedFiniteSumLinks
