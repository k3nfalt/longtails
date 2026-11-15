import LongTails.Proofs.InterpolatedFiniteSumCentering
import LongTails.Proofs.InterpolatedFiniteSumProfiles
import LongTails.Proofs.AdaptivePolynomialLocalization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InterpolatedFiniteSumShield

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable def radiusNorm (r : ℝ) (x : E) : ℝ := Real.sqrt (‖x‖ ^ 2 + r ^ 2)

noncomputable def radiusField (r : ℝ) (x : E) : E := (radiusNorm r x)⁻¹ • x

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma radiusNorm_pos (r : ℝ) (hr : 0 < r) (x : E) : 0 < radiusNorm r x := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg ‖x‖]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma radiusNorm_ge (r : ℝ) (x : E) :
    r ≤ radiusNorm r x ∧ ‖x‖ ≤ radiusNorm r x := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])
  · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma radiusNorm_sq (r : ℝ) (x : E) : (radiusNorm r x) ^ 2 = ‖x‖ ^ 2 + r ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma radiusNorm_hasGradientAt (r : ℝ) (hr : 0 < r) (x : E) :
    HasGradientAt (radiusNorm r) (radiusField r x) x := by
  have hp : ‖x‖ ^ 2 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg ‖x‖]
  have hd := (Real.hasDerivAt_sqrt hp).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (r ^ 2))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext y
    simp only [radiusField, radiusNorm, InnerProductSpace.toDual_apply_apply,
      real_inner_smul_left, smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring

omit [CompleteSpace E] in
lemma radiusField_norm (r : ℝ) (hr : 0 < r) (x : E) : ‖radiusField r x‖ ≤ 1 := by
  rw [radiusField, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radiusNorm_pos r hr x).le)]
  have h := (radiusNorm_ge r x).2
  have hp := radiusNorm_pos r hr x
  calc
    (radiusNorm r x)⁻¹ * ‖x‖ ≤ (radiusNorm r x)⁻¹ * radiusNorm r x :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma radiusField_hasFDerivAt (r : ℝ) (hr : 0 < r) (x : E) :
    HasFDerivAt (radiusField r)
      ((radiusNorm r x)⁻¹ • ContinuousLinearMap.id ℝ E -
        ((radiusNorm r x)⁻¹ ^ 3 • (InnerProductSpace.toDual ℝ E x)).smulRight x) x := by
  have hd := (hasDerivAt_inv (radiusNorm_pos r hr x).ne').comp_hasFDerivAt x
    (radiusNorm_hasGradientAt r hr x).hasFDerivAt
  have hi := hd.smul (hasFDerivAt_id x)
  convert hi using 1
  · rfl
  · ext y
    simp only [radiusField, InnerProductSpace.toDual_apply_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      sub_apply, add_apply, real_inner_smul_left, inv_pow,
      Function.comp_apply, id_eq]
    module

lemma radiusField_curvature (r : ℝ) (hr : 0 < r) (x : E) :
    ‖fderiv ℝ (radiusField r) x‖ ≤ 2 / r := by
  let s := radiusNorm r x
  have hs : 0 < s := radiusNorm_pos r hr x
  have hx : ‖x‖ ^ 2 ≤ s ^ 2 := by
    dsimp [s]
    rw [radiusNorm_sq]
    nlinarith [sq_nonneg r]
  have ht : s⁻¹ ^ 3 * ‖x‖ ^ 2 ≤ s⁻¹ := by
    calc
      _ ≤ s⁻¹ ^ 3 * s ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = _ := by field_simp
  have hi : ‖s⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ s⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)).trans_eq
      (mul_one _)
  have hn : ‖(s⁻¹ ^ 3 • (InnerProductSpace.toDual ℝ E x)).smulRight x‖ =
      s⁻¹ ^ 3 * ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
      Real.norm_of_nonneg (by positivity), (InnerProductSpace.toDual ℝ E).norm_map]
    ring
  rw [(radiusField_hasFDerivAt r hr x).fderiv]
  have hb := norm_sub_le (s⁻¹ • ContinuousLinearMap.id ℝ E)
    ((s⁻¹ ^ 3 • (InnerProductSpace.toDual ℝ E x)).smulRight x)
  rw [hn] at hb
  have hr' : r ≤ s := (radiusNorm_ge r x).1
  have hinv : s⁻¹ ≤ r⁻¹ := inv_anti₀ hr hr'
  change ‖s⁻¹ • ContinuousLinearMap.id ℝ E -
    (s⁻¹ ^ 3 • (InnerProductSpace.toDual ℝ E x)).smulRight x‖ ≤ 2 / r
  rw [div_eq_mul_inv]
  linarith

omit [CompleteSpace E] in
lemma radiusNorm_support (r : ℝ) (hr : 0 < r) (x y : E) :
    ⟪radiusField r x, y - x⟫ ≤ radiusNorm r y - radiusNorm r x := by
  have hx := radiusNorm_sq r x
  have hy := radiusNorm_sq r y
  have hp := radiusNorm_pos r hr x
  have hq := radiusNorm_pos r hr y
  have he : (radiusNorm r x * radiusNorm r y) ^ 2 =
      (‖x‖ ^ 2 + r ^ 2) * (‖y‖ ^ 2 + r ^ 2) := by rw [mul_pow, hx, hy]
  have hcs : ‖x‖ * ‖y‖ + r ^ 2 ≤ radiusNorm r x * radiusNorm r y := by
    have hsq := mul_nonneg (sq_nonneg r) (sq_nonneg (‖x‖ - ‖y‖))
    have hnonneg := mul_nonneg (norm_nonneg x) (norm_nonneg y)
    have hprod := mul_pos hp hq
    nlinarith
  have hi := real_inner_le_norm x y
  simp only [radiusField, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq, inv_mul_eq_div]
  rw [← sub_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith

omit [CompleteSpace E] in
lemma radiusNorm_convex (r : ℝ) (hr : 0 < r) :
    ConvexOn ℝ Set.univ (radiusNorm r : E → ℝ) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support
    (G := radiusField r)
  intro x y
  have h := radiusNorm_support r hr x y
  linarith

noncomputable def envelope (f h : E → ℝ) (W : ℝ) (x : E) : ℝ :=
  InterpolatedFiniteSumProfiles.smoothMax W (f x) (h x)

noncomputable def envelopeMix (f h : E → ℝ) (W : ℝ) (x : E) : ℝ :=
  AdaptivePolynomialHinge.mixing 2 ((h x - f x) / W + 1 / 2)

noncomputable def envelopeField (f h : E → ℝ) (g k : E → E) (W : ℝ) (x : E) : E :=
  g x + envelopeMix f h W x • (k x - g x)

lemma envelope_hasGradientAt (f h : E → ℝ) (g k : E → E) (W : ℝ) (hW : 0 < W)
    (x : E) (hf : HasGradientAt f (g x) x) (hh : HasGradientAt h (k x) x) :
    HasGradientAt (envelope f h W) (envelopeField f h g k W x) x := by
  have hd := ((AdaptivePolynomialHinge.ramp_hasDerivAt 2 (by omega) _).comp_hasFDerivAt x
    ((((hasDerivAt_id _).div_const W).comp_hasFDerivAt x
      (hh.hasFDerivAt.sub hf.hasFDerivAt)).add_const (1 / 2))).const_mul W
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf.hasFDerivAt.add hd using 1
  · rfl
  · ext y
    simp only [envelopeField, envelopeMix, InnerProductSpace.toDual_apply_apply,
      inner_add_left, inner_sub_left, real_inner_smul_left, add_apply, smul_apply,
      sub_apply, smul_eq_mul, Function.comp_apply, Pi.sub_apply, id_eq]
    field_simp

omit [CompleteSpace E] in
lemma envelopeField_combination (f h : E → ℝ) (g k : E → E) (W : ℝ) (x : E) :
    envelopeField f h g k W x =
      (1 - envelopeMix f h W x) • g x + envelopeMix f h W x • k x := by
  simp only [envelopeField, smul_sub, sub_smul, one_smul]
  abel

lemma envelope_convex (f h : E → ℝ) (g k : E → E) (W : ℝ) (hW : 0 < W)
    (hf : ConvexOn ℝ Set.univ f) (hh : ConvexOn ℝ Set.univ h)
    (hg : ∀ x, HasGradientAt f (g x) x) (hk : ∀ x, HasGradientAt h (k x) x) :
    ConvexOn ℝ Set.univ (envelope f h W) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support
    (G := envelopeField f h g k W)
  intro x y
  have hm := AdaptivePolynomialHinge.mixing_bounds 2 ((h x - f x) / W + 1 / 2)
  change 0 ≤ envelopeMix f h W x ∧ envelopeMix f h W x ≤ 1 at hm
  have h₁ := mul_le_mul_of_nonneg_left (OracleTemplate.Gradient.convex_support hf hg x y)
    (sub_nonneg.mpr hm.2)
  have h₂ := mul_le_mul_of_nonneg_left (OracleTemplate.Gradient.convex_support hh hk x y) hm.1
  have h₃ := mul_le_mul_of_nonneg_left (AdaptivePolynomialLocalization.ramp_support 2
    (by omega) ((h x - f x) / W + 1 / 2) ((h y - f y) / W + 1 / 2)) hW.le
  have he : W * (AdaptivePolynomialHinge.mixing 2 ((h x - f x) / W + 1 / 2) *
      (((h y - f y) / W + 1 / 2) - ((h x - f x) / W + 1 / 2))) =
      envelopeMix f h W x * ((h y - f y) - (h x - f x)) := by
    unfold envelopeMix
    field_simp
    ring
  rw [he] at h₃
  rw [envelopeField_combination]
  simp only [envelope, InterpolatedFiniteSumProfiles.smoothMax, inner_add_left,
    real_inner_smul_left]
  linarith only [h₁, h₂, h₃]

omit [CompleteSpace E] in
lemma envelopeField_norm (f h : E → ℝ) (g k : E → E) (W G : ℝ) (x : E)
    (hg : ‖g x‖ ≤ G) (hk : ‖k x‖ ≤ G) : ‖envelopeField f h g k W x‖ ≤ G := by
  have hm := AdaptivePolynomialHinge.mixing_bounds 2 ((h x - f x) / W + 1 / 2)
  change 0 ≤ envelopeMix f h W x ∧ envelopeMix f h W x ≤ 1 at hm
  rw [envelopeField_combination]
  have hb := norm_add_le ((1 - envelopeMix f h W x) • g x) (envelopeMix f h W x • k x)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hm.2),
    Real.norm_of_nonneg hm.1] at hb
  have h₁ := mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hm.2)
  have h₂ := mul_le_mul_of_nonneg_left hk hm.1
  nlinarith

noncomputable def envelopeCurvature (f h : E → ℝ) (W : ℝ) (x : E) : ℝ :=
  AdaptivePolynomialHinge.curvature 2 ((h x - f x) / W + 1 / 2) / W

lemma envelopeMix_hasFDerivAt (f h : E → ℝ) (g k : E → E) (W : ℝ) (x : E)
    (hf : HasGradientAt f (g x) x) (hh : HasGradientAt h (k x) x) :
    HasFDerivAt (envelopeMix f h W)
      (envelopeCurvature f h W x • (InnerProductSpace.toDual ℝ E (k x - g x))) x := by
  have hd := (AdaptivePolynomialHinge.mixing_hasDerivAt 2 (by omega) _).comp_hasFDerivAt x
    ((((hasDerivAt_id _).div_const W).comp_hasFDerivAt x
      (hh.hasFDerivAt.sub hf.hasFDerivAt)).add_const (1 / 2))
  convert hd using 1
  · rfl
  · ext y
    simp only [envelopeCurvature, smul_apply, sub_apply,
      InnerProductSpace.toDual_apply_apply, inner_sub_left, smul_eq_mul,
      Function.comp_apply, Pi.sub_apply, id_eq]
    ring

lemma envelopeField_hasFDerivAt (f h : E → ℝ) (g k : E → E) (W : ℝ) (x : E)
    (A B : E →L[ℝ] E) (hf : HasGradientAt f (g x) x) (hh : HasGradientAt h (k x) x)
    (hg : HasFDerivAt g A x) (hk : HasFDerivAt k B x) :
    HasFDerivAt (envelopeField f h g k W)
      ((1 - envelopeMix f h W x) • A + envelopeMix f h W x • B +
        (envelopeCurvature f h W x • (InnerProductSpace.toDual ℝ E (k x - g x))).smulRight
          (k x - g x)) x := by
  have hd := hg.add ((envelopeMix_hasFDerivAt f h g k W x hf hh).smul (hk.sub hg))
  convert hd using 1
  · rfl
  · simp only [smul_sub, sub_smul, one_smul]
    abel

lemma envelopeField_curvature (f h : E → ℝ) (g k : E → E) (W : ℝ) (hW : 0 < W)
    (x : E) (A B : E →L[ℝ] E) (hf : HasGradientAt f (g x) x)
    (hh : HasGradientAt h (k x) x) (hg : HasFDerivAt g A x) (hk : HasFDerivAt k B x) :
    ‖fderiv ℝ (envelopeField f h g k W) x‖ ≤
      (1 - envelopeMix f h W x) * ‖A‖ + envelopeMix f h W x * ‖B‖ +
        (3 / (2 * W)) * ‖k x - g x‖ ^ 2 := by
  have hm := AdaptivePolynomialHinge.mixing_bounds 2 ((h x - f x) / W + 1 / 2)
  change 0 ≤ envelopeMix f h W x ∧ envelopeMix f h W x ≤ 1 at hm
  have hc : 0 ≤ envelopeCurvature f h W x :=
    div_nonneg (AdaptivePolynomialHinge.curvature_bounds 2 (by omega) _).1 hW.le
  have hc' : envelopeCurvature f h W x ≤ 3 / (2 * W) := by
    change AdaptivePolynomialHinge.curvature 2 ((h x - f x) / W + 1 / 2) / W ≤ _
    have ht := div_le_div_of_nonneg_right
      (InterpolatedFiniteSumProfiles.curvature_two_bound ((h x - f x) / W + 1 / 2)) hW.le
    convert ht using 1
    ring
  have hn : ‖(envelopeCurvature f h W x • (InnerProductSpace.toDual ℝ E (k x - g x))).smulRight
      (k x - g x)‖ = envelopeCurvature f h W x * ‖k x - g x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_of_nonneg hc,
      (InnerProductSpace.toDual ℝ E).norm_map]
    ring
  rw [(envelopeField_hasFDerivAt f h g k W x A B hf hh hg hk).fderiv]
  calc
    _ ≤ ‖(1 - envelopeMix f h W x) • A‖ + ‖envelopeMix f h W x • B‖ +
        ‖(envelopeCurvature f h W x • (InnerProductSpace.toDual ℝ E (k x - g x))).smulRight
          (k x - g x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hm.2),
        Real.norm_of_nonneg hm.1, hn]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc' (sq_nonneg _))

noncomputable def radialWall (r G c W : ℝ) (x : E) : ℝ :=
  2 * G * radiusNorm r x - 4 * G * r + c - W / 2

noncomputable def radialField (r G : ℝ) (x : E) : E := (2 * G) • radiusField r x

lemma radialWall_hasGradientAt (r G c W : ℝ) (hr : 0 < r) (x : E) :
    HasGradientAt (radialWall r G c W) (radialField r G x) x := by
  have hd := ((((radiusNorm_hasGradientAt r hr x).hasFDerivAt.const_mul (2 * G)).sub_const
    (4 * G * r)).add_const c).sub_const (W / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext y
    simp only [radialField, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul]

omit [CompleteSpace E] in
lemma radialWall_convex (r G c W : ℝ) (hr : 0 < r) (hG : 0 ≤ G) :
    ConvexOn ℝ Set.univ (radialWall r G c W : E → ℝ) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support
    (G := radialField r G)
  intro x y
  have hh := mul_le_mul_of_nonneg_left (radiusNorm_support r hr x y)
    (show 0 ≤ 2 * G by positivity)
  simp only [radialWall, radialField, real_inner_smul_left]
  linarith

omit [CompleteSpace E] in
lemma radialField_norm (r G : ℝ) (hr : 0 < r) (hG : 0 ≤ G) (x : E) :
    ‖radialField r G x‖ ≤ 2 * G := by
  rw [radialField, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (radiusField_norm r hr x) (by positivity)).trans_eq
    (mul_one _)

lemma radialField_differentiable (r G : ℝ) (hr : 0 < r) :
    Differentiable ℝ (radialField r G : E → E) := by
  intro x
  exact ((radiusField_hasFDerivAt r hr x).const_smul (2 * G)).differentiableAt

lemma radialField_curvature (r G : ℝ) (hr : 0 < r) (hG : 0 ≤ G) (x : E) :
    ‖fderiv ℝ (radialField r G) x‖ ≤ 4 * G / r := by
  change ‖fderiv ℝ ((2 * G) • radiusField r) x‖ ≤ _
  rw [fderiv_const_smul (radiusField_hasFDerivAt r hr x).differentiableAt,
    norm_smul, Real.norm_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (radiusField_curvature r hr x)
    (show 0 ≤ 2 * G by positivity)
  convert hh using 1
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma radialWall_interior (r G c W : ℝ) (hr : 0 < r) (hG : 0 ≤ G) (x : E)
    (hx : ‖x‖ ≤ r) : radialWall r G c W x ≤ c - W / 2 := by
  have hrad : radiusNorm r x ≤ 2 * r := by
    have hs := radiusNorm_sq r x
    have hp := radiusNorm_pos r hr x
    have hn := norm_nonneg x
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2 * G by positivity)
  dsimp [radialWall]
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma envelope_radial_interior (f : E → ℝ) (r G c W : ℝ)
    (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (hc : ∀ x, c ≤ f x)
    (x : E) (hx : ‖x‖ ≤ r) : envelope f (radialWall r G c W) W x = f x := by
  apply InterpolatedFiniteSumProfiles.smoothMax_left W (f x) _ hW
  have hh := radialWall_interior r G c W hr hG x hx
  have hm := hc x
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma envelope_radial_exterior (f : E → ℝ) (r G c W : ℝ)
    (hG : 0 < G) (hW : 0 < W) (x : E) (hf : f x ≤ f 0 + G * ‖x‖)
    (hx : 4 * r + (f 0 - c + W) / G ≤ ‖x‖) :
    envelope f (radialWall r G c W) W x = radialWall r G c W x := by
  apply InterpolatedFiniteSumProfiles.smoothMax_right W (f x) _ hW
  have hs := (radiusNorm_ge r x).2
  have hh : f 0 - c + W ≤ (‖x‖ - 4 * r) * G := by
    apply (div_le_iff₀ hG).mp
    linarith
  dsimp [radialWall]
  nlinarith

lemma envelope_radial_curvature (f : E → ℝ) (g : E → E) (r G c W L : ℝ)
    (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (hL : 0 ≤ L)
    (hwidth : 64 * G ^ 2 ≤ W * L) (hrad : 4 * G / r ≤ L / 3)
    (x : E) (hf : HasGradientAt f (g x) x) (hg : DifferentiableAt ℝ g x)
    (hn : ‖g x‖ ≤ G) (hc : ‖fderiv ℝ g x‖ ≤ L / 3) :
    ‖fderiv ℝ (envelopeField f (radialWall r G c W) g (radialField r G) W) x‖ ≤ L := by
  have hw := radialWall_hasGradientAt r G c W hr x
  have hk := (radialField_differentiable r G hr).differentiableAt (x := x)
  have hb := envelopeField_curvature f (radialWall r G c W) g (radialField r G) W hW x
    (fderiv ℝ g x) (fderiv ℝ (radialField r G) x) hf hw hg.hasFDerivAt hk.hasFDerivAt
  have hc' := (radialField_curvature r G hr hG x).trans hrad
  have hm := AdaptivePolynomialHinge.mixing_bounds 2
    ((radialWall r G c W x - f x) / W + 1 / 2)
  change 0 ≤ envelopeMix f (radialWall r G c W) W x ∧
    envelopeMix f (radialWall r G c W) W x ≤ 1 at hm
  have ha := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hm.2)
  have hb' := mul_le_mul_of_nonneg_left hc' hm.1
  have hd : ‖radialField r G x - g x‖ ≤ 3 * G := by
    have h := norm_sub_le (radialField r G x) (g x)
    have h' := radialField_norm r G hr hG x
    linarith
  have hd' : ‖radialField r G x - g x‖ ^ 2 ≤ 9 * G ^ 2 := by
    nlinarith [norm_nonneg (radialField r G x - g x)]
  have hcross : (3 / (2 * W)) * ‖radialField r G x - g x‖ ^ 2 ≤ L / 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * W)).mpr
    nlinarith
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma envelope_radial_minimizer (f : E → ℝ) (r G c W : ℝ)
    (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (hc : ∀ x, c ≤ f x)
    (z : E) (hz : ‖z‖ ≤ r) (hf : f z = c) :
    IsMinOn (envelope f (radialWall r G c W) W) Set.univ z := by
  intro x _
  change envelope f (radialWall r G c W) W z ≤ envelope f (radialWall r G c W) W x
  rw [envelope_radial_interior f r G c W hr hG hW hc z hz, hf]
  exact (hc x).trans (InterpolatedFiniteSumProfiles.smoothMax_above W (f x)
    (radialWall r G c W x) hW).1

lemma envelopeField_differentiable (f h : E → ℝ) (g k : E → E) (W : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hh : ∀ x, HasGradientAt h (k x) x)
    (hg : Differentiable ℝ g) (hk : Differentiable ℝ k) :
    Differentiable ℝ (envelopeField f h g k W) := by
  intro x
  exact (envelopeField_hasFDerivAt f h g k W x (fderiv ℝ g x) (fderiv ℝ k x)
    (hf x) (hh x) (hg x).hasFDerivAt (hk x).hasFDerivAt).differentiableAt

omit [CompleteSpace E] in
lemma envelopeField_right (f h : E → ℝ) (g k : E → E) (W : ℝ) (hW : 0 < W)
    (x : E) (hx : f x + W / 2 ≤ h x) : envelopeField f h g k W x = k x := by
  have ht : 1 ≤ (h x - f x) / W + 1 / 2 := by
    have he : W / 2 ≤ h x - f x := by linarith
    have hh := (le_div_iff₀ hW).mpr (show (1 / 2 : ℝ) * W ≤ h x - f x by linarith)
    linarith
  have hm : envelopeMix f h W x = 1 := by
    dsimp [envelopeMix]
    by_cases hle : (h x - f x) / W + 1 / 2 ≤ 1
    · have he : (h x - f x) / W + 1 / 2 = 1 := le_antisymm hle ht
      rw [he]
      norm_num [AdaptivePolynomialHinge.mixing, AdaptivePolynomialHinge.weight]
    · simp only [AdaptivePolynomialHinge.mixing,
        ite_eq_right (show ¬((h x - f x) / W + 1 / 2 ≤ 0) by linarith), ite_eq_right hle]
  simp only [envelopeField, hm, one_smul]
  abel

omit [CompleteSpace E] in
lemma envelopeField_radial_exterior (f : E → ℝ) (g : E → E) (r G c W : ℝ)
    (hG : 0 < G) (hW : 0 < W) (x : E) (hf : f x ≤ f 0 + G * ‖x‖)
    (hx : 4 * r + (f 0 - c + W) / G ≤ ‖x‖) :
    envelopeField f (radialWall r G c W) g (radialField r G) W x = radialField r G x := by
  apply envelopeField_right f (radialWall r G c W) g (radialField r G) W hW x
  have hs := (radiusNorm_ge r x).2
  have hh : f 0 - c + W ≤ (‖x‖ - 4 * r) * G := by
    apply (div_le_iff₀ hG).mp
    linarith
  dsimp [radialWall]
  nlinarith

end LongTails.Proofs.InterpolatedFiniteSumShield
