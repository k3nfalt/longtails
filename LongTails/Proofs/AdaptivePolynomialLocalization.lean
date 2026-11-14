import LongTails.Proofs.AdaptivePolynomialHinge
import LongTails.Proofs.HiddenDecompositionEnergy
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdaptivePolynomialLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def wall (a B : ℝ) (x : E) : ℝ := a / 2 * (‖x‖ ^ 2 - B ^ 2)

noncomputable def value (f : E → ℝ) (n : ℕ) (a B W : ℝ) (x : E) : ℝ :=
  f x + W * AdaptivePolynomialHinge.ramp n ((wall a B x - f x) / W)

noncomputable def mixing (f : E → ℝ) (n : ℕ) (a B W : ℝ) (x : E) : ℝ :=
  AdaptivePolynomialHinge.mixing n ((wall a B x - f x) / W)

noncomputable def field (f : E → ℝ) (g : E → E) (n : ℕ) (a B W : ℝ) (x : E) : E :=
  g x + mixing f n a B W x • (a • x - g x)

lemma wall_hasGradientAt (a B : ℝ) (x : E) : HasGradientAt (wall a B) (a • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).sub_const (B ^ 2)).const_mul (a / 2)
  convert hh using 1
  · rfl
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring

lemma value_hasGradientAt (f : E → ℝ) (g : E → E) (n : ℕ) (hn : 2 ≤ n)
    (a B W : ℝ) (hW : 0 < W) (x : E) (hf : HasGradientAt f (g x) x) :
    HasGradientAt (value f n a B W) (field f g n a B W x) x := by
  have hw := (wall_hasGradientAt a B x).hasFDerivAt
  have hd := ((AdaptivePolynomialHinge.ramp_hasDerivAt n hn _).comp_hasFDerivAt x
    (((hasDerivAt_id _).div_const W).comp_hasFDerivAt x (hw.sub hf.hasFDerivAt))).const_mul W
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf.hasFDerivAt.add hd using 1
  · rfl
  · ext y
    simp only [field, mixing, InnerProductSpace.toDual_apply_apply, inner_add_left,
      inner_sub_left, real_inner_smul_left, add_apply,
      smul_apply, sub_apply, smul_eq_mul, Function.comp_apply, Pi.sub_apply, id_eq]
    field_simp

omit [CompleteSpace E] in
lemma field_convex_combination (f : E → ℝ) (g : E → E) (n : ℕ)
    (a B W : ℝ) (x : E) : field f g n a B W x =
      (1 - mixing f n a B W x) • g x + mixing f n a B W x • (a • x) := by
  simp only [field, smul_sub, sub_smul, one_smul]
  abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_above (f : E → ℝ) (n : ℕ) (hn : 2 ≤ n) (a B W : ℝ)
    (hW : 0 ≤ W) (x : E) : f x ≤ value f n a B W x := by
  have h := mul_nonneg hW (AdaptivePolynomialHinge.ramp_nonnegative n hn
    ((wall a B x - f x) / W))
  unfold value
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_interior (f : E → ℝ) (n : ℕ) (a B W : ℝ)
    (hW : 0 < W) (x : E) (hx : wall a B x ≤ f x) : value f n a B W x = f x := by
  have h : (wall a B x - f x) / W ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hW.le
  simp [value, AdaptivePolynomialHinge.ramp, h]

omit [CompleteSpace E] in
lemma field_interior (f : E → ℝ) (g : E → E) (n : ℕ) (a B W : ℝ)
    (hW : 0 < W) (x : E) (hx : wall a B x ≤ f x) : field f g n a B W x = g x := by
  have h : (wall a B x - f x) / W ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hW.le
  simp [field, mixing, AdaptivePolynomialHinge.mixing, h]

omit [CompleteSpace E] in
lemma wall_support (a B : ℝ) (ha : 0 ≤ a) (x y : E) :
    ⟪a • x, y - x⟫ ≤ wall a B y - wall a B x := by
  have hn := norm_sub_sq_real y x
  have hp := mul_nonneg (show 0 ≤ a / 2 by positivity) (sq_nonneg ‖y - x‖)
  simp only [wall, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm] at hn
  nlinarith only [congrArg (fun t : ℝ => a / 2 * t) hn, hp]

lemma ramp_support (n : ℕ) (hn : 2 ≤ n) (x y : ℝ) :
    AdaptivePolynomialHinge.mixing n x * (y - x) ≤
      AdaptivePolynomialHinge.ramp n y - AdaptivePolynomialHinge.ramp n x := by
  have hg (u : ℝ) : HasGradientAt (AdaptivePolynomialHinge.ramp n)
      (AdaptivePolynomialHinge.mixing n u) u := by
    simpa using (AdaptivePolynomialHinge.ramp_hasDerivAt n hn u).hasGradientAt
  simpa only [Real.inner_apply] using OracleTemplate.Gradient.convex_support
    (AdaptivePolynomialHinge.ramp_convex n hn) hg x y

lemma value_convex (f : E → ℝ) (g : E → E) (n : ℕ) (hn : 2 ≤ n)
    (a B W : ℝ) (ha : 0 ≤ a) (hW : 0 < W)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) :
    ConvexOn ℝ univ (value f n a B W) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support (G := field f g n a B W)
  intro x y
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - f x) / W)
  change 0 ≤ mixing f n a B W x ∧ mixing f n a B W x ≤ 1 at hp
  have hf := mul_le_mul_of_nonneg_left (OracleTemplate.Gradient.convex_support hc hg x y)
    (sub_nonneg.mpr hp.2)
  have hw := mul_le_mul_of_nonneg_left (wall_support a B ha x y) hp.1
  simp only [real_inner_smul_left] at hw
  have hh := mul_le_mul_of_nonneg_left (ramp_support n hn
    ((wall a B x - f x) / W) ((wall a B y - f y) / W)) hW.le
  have he : W * (AdaptivePolynomialHinge.mixing n ((wall a B x - f x) / W) *
      ((wall a B y - f y) / W - (wall a B x - f x) / W)) =
      mixing f n a B W x * ((wall a B y - f y) - (wall a B x - f x)) := by
    unfold mixing
    field_simp
  rw [he] at hh
  rw [field_convex_combination]
  simp only [value, inner_add_left, real_inner_smul_left]
  linarith only [hf, hw, hh]

noncomputable def mixingDerivative (f : E → ℝ) (n : ℕ) (a B W : ℝ) (x : E) : ℝ :=
  AdaptivePolynomialHinge.curvature n ((wall a B x - f x) / W) / W

lemma mixing_hasFDerivAt (f : E → ℝ) (g : E → E) (n : ℕ) (hn : 2 ≤ n)
    (a B W : ℝ) (x : E) (hf : HasGradientAt f (g x) x) :
    HasFDerivAt (mixing f n a B W)
      (mixingDerivative f n a B W x • (InnerProductSpace.toDual ℝ E (a • x - g x))) x := by
  have hh := (AdaptivePolynomialHinge.mixing_hasDerivAt n hn _).comp_hasFDerivAt x
    (((hasDerivAt_id _).div_const W).comp_hasFDerivAt x
      ((wall_hasGradientAt a B x).hasFDerivAt.sub hf.hasFDerivAt))
  convert hh using 1
  · rfl
  · ext y
    simp only [mixingDerivative, smul_apply, sub_apply, InnerProductSpace.toDual_apply_apply,
      inner_sub_left, real_inner_smul_left, Function.comp_apply, Pi.sub_apply, id_eq]
    ring

lemma field_hasFDerivAt (f : E → ℝ) (g : E → E) (n : ℕ) (hn : 2 ≤ n)
    (a B W : ℝ) (x : E) (A : E →L[ℝ] E)
    (hf : HasGradientAt f (g x) x) (hg : HasFDerivAt g A x) :
    HasFDerivAt (field f g n a B W)
      ((1 - mixing f n a B W x) • A + mixing f n a B W x • (a • ContinuousLinearMap.id ℝ E) +
        (mixingDerivative f n a B W x • (InnerProductSpace.toDual ℝ E (a • x - g x))).smulRight
          (a • x - g x)) x := by
  have hw : HasFDerivAt (fun y : E => a • y) (a • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul a
  have h := hg.add ((mixing_hasFDerivAt f g n hn a B W x hf).smul (hw.sub hg))
  convert h using 1
  · rfl
  · simp only [smul_sub, sub_smul, one_smul]
    abel

lemma field_derivative_norm_bound (f : E → ℝ) (g : E → E) (n : ℕ) (hn : 2 ≤ n)
    (a B W : ℝ) (ha : 0 ≤ a) (hW : 0 < W) (x : E) (A : E →L[ℝ] E)
    (hf : HasGradientAt f (g x) x) (hg : HasFDerivAt g A x) :
    ‖fderiv ℝ (field f g n a B W) x‖ ≤
      (1 - mixing f n a B W x) * ‖A‖ + mixing f n a B W x * a +
        mixingDerivative f n a B W x * ‖a • x - g x‖ ^ 2 := by
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - f x) / W)
  change 0 ≤ mixing f n a B W x ∧ mixing f n a B W x ≤ 1 at hp
  have hχ : 0 ≤ mixingDerivative f n a B W x :=
    div_nonneg (AdaptivePolynomialHinge.curvature_bounds n hn _).1 hW.le
  have hi : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ a := by
    rw [norm_smul, Real.norm_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ha).trans_eq (mul_one _)
  have hd : ‖InnerProductSpace.toDual ℝ E (a • x - g x)‖ = ‖a • x - g x‖ :=
    (InnerProductSpace.toDual ℝ E).norm_map _
  have hr : ‖(mixingDerivative f n a B W x • (InnerProductSpace.toDual ℝ E (a • x - g x))).smulRight
      (a • x - g x)‖ = mixingDerivative f n a B W x * ‖a • x - g x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_of_nonneg hχ, hd]
    ring
  have hm : ‖mixing f n a B W x • (a • ContinuousLinearMap.id ℝ E)‖ ≤
      mixing f n a B W x * a := by
    rw [norm_smul, Real.norm_of_nonneg hp.1]
    exact mul_le_mul_of_nonneg_left hi hp.1
  rw [(field_hasFDerivAt f g n hn a B W x A hf hg).fderiv]
  calc
    _ ≤ ‖(1 - mixing f n a B W x) • A‖ +
        ‖mixing f n a B W x • (a • ContinuousLinearMap.id ℝ E)‖ +
        ‖(mixingDerivative f n a B W x • (InnerProductSpace.toDual ℝ E (a • x - g x))).smulRight
          (a • x - g x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hp.2), hr]
      linarith only [hm]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_interior (f : E → ℝ) (n : ℕ) (a B W : ℝ)
    (hW : 0 < W) (x : E) (hx : wall a B x ≤ f x) :
    mixing f n a B W x = 0 ∧ mixingDerivative f n a B W x = 0 := by
  have h : (wall a B x - f x) / W ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hW.le
  simp [mixing, mixingDerivative, AdaptivePolynomialHinge.mixing, AdaptivePolynomialHinge.curvature, h]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_exterior (f : E → ℝ) (n : ℕ) (a B W : ℝ)
    (hW : 0 < W) (x : E) (hx : W ≤ wall a B x - f x) :
    mixing f n a B W x = 1 ∧ mixingDerivative f n a B W x = 0 := by
  have h : 1 ≤ (wall a B x - f x) / W := (le_div_iff₀ hW).mpr (by simpa using hx)
  rcases eq_or_lt_of_le h with he | he
  · simp [mixing, mixingDerivative, ← he, AdaptivePolynomialHinge.mixing,
      AdaptivePolynomialHinge.curvature, AdaptivePolynomialHinge.weight_one, AdaptivePolynomialHinge.slope_one]
  · have hh : ¬ (wall a B x - f x) / W ≤ 0 := by linarith
    simp [mixing, mixingDerivative, AdaptivePolynomialHinge.mixing, AdaptivePolynomialHinge.curvature,
      hh, not_le.mpr he]

omit [CompleteSpace E] in
lemma field_exterior (f : E → ℝ) (g : E → E) (n : ℕ) (a B W : ℝ)
    (hW : 0 < W) (x : E) (hx : W ≤ wall a B x - f x) :
    field f g n a B W x = a • x := by
  rw [field, (mixing_exterior f n a B W hW x hx).1, one_smul]
  abel

lemma ramp_above_linear (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    t - 1 ≤ AdaptivePolynomialHinge.ramp n t := by
  have hh := ramp_support n hn 1 t
  have hz := AdaptivePolynomialHinge.ramp_nonnegative n hn 1
  have hm : AdaptivePolynomialHinge.mixing n 1 = 1 := by
    simp [AdaptivePolynomialHinge.mixing, AdaptivePolynomialHinge.weight_one]
  rw [hm, one_mul] at hh
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_above_wall (f : E → ℝ) (n : ℕ) (hn : 2 ≤ n) (a B W : ℝ)
    (hW : 0 < W) (x : E) : wall a B x - W ≤ value f n a B W x := by
  have hh := mul_le_mul_of_nonneg_left (ramp_above_linear n hn ((wall a B x - f x) / W)) hW.le
  have he : W * ((wall a B x - f x) / W - 1) = wall a B x - f x - W := by field_simp
  rw [he] at hh
  unfold value
  linarith only [hh]

end LongTails.Proofs.AdaptivePolynomialLocalization
