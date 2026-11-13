import LongTails.Proofs.HiddenDecompositionEnergy
import LongTails.Proofs.CompactSmoothMaximum
import LongTails.Proofs.GeneralizedSmoothShield
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothShieldCalculus

open CompactSmoothMaximum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def wall (a B : ℝ) (x : E) : ℝ := a / 2 * (‖x‖ ^ 2 - B ^ 2)

noncomputable def value (f : E → ℝ) (a B T : ℝ) (x : E) : ℝ :=
  wall a B x + smoothPositive T (f x - wall a B x)

noncomputable def mixing (f : E → ℝ) (a B T : ℝ) (x : E) : ℝ :=
  CompactSmoothMaximum.slope ((f x - wall a B x + T) / (2 * T))

noncomputable def field (f : E → ℝ) (g : E → E) (a B T : ℝ) (x : E) : E :=
  a • x + mixing f a B T x • (g x - a • x)

lemma wall_hasGradientAt (a B : ℝ) (x : E) : HasGradientAt (wall a B) (a • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).sub_const (B ^ 2)).const_mul (a / 2)
  convert hh using 1
  · rfl
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring

lemma value_hasGradientAt (f : E → ℝ) (g : E → E) (a B T : ℝ) (hT : 0 < T)
    (x : E) (hf : HasGradientAt f (g x) x) :
    HasGradientAt (value f a B T) (field f g a B T x) x := by
  have hw := (wall_hasGradientAt a B x).hasFDerivAt
  have hd := (smoothPositive_hasDerivAt hT (f x - wall a B x)).comp_hasFDerivAt x
    (hf.hasFDerivAt.sub hw)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hw.add hd using 1
  · rfl
  · ext y
    simp only [field, mixing, InnerProductSpace.toDual_apply_apply, inner_add_left,
      inner_sub_left, real_inner_smul_left, add_apply,
      smul_apply, sub_apply, smul_eq_mul]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_above (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E) :
    f x ≤ value f a B T x ∧ wall a B x ≤ value f a B T x := by
  have h1 := smoothPositive_above hT (f x - wall a B x)
  have h2 := smoothPositive_nonneg hT (f x - wall a B x)
  unfold value
  constructor <;> linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_eq_left (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E)
    (hx : T ≤ f x - wall a B x) : value f a B T x = f x := by
  rw [value, smoothPositive_right hT hx]
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma value_eq_wall (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E)
    (hx : f x - wall a B x ≤ -T) : value f a B T x = wall a B x := by
  rw [value, smoothPositive_left hT hx, add_zero]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_bounds (f : E → ℝ) (a B T : ℝ) (x : E) :
    0 ≤ mixing f a B T x ∧ mixing f a B T x ≤ 1 := slope_bounds _

omit [CompleteSpace E] in
lemma field_convex_combination (f : E → ℝ) (g : E → E) (a B T : ℝ) (x : E) :
    field f g a B T x = mixing f a B T x • g x + (1 - mixing f a B T x) • (a • x) := by
  simp only [field, smul_sub, sub_smul, one_smul]
  abel

lemma smoothPositive_support (T : ℝ) (hT : 0 < T) (x y : ℝ) :
    CompactSmoothMaximum.slope ((x + T) / (2 * T)) * (y - x) ≤ smoothPositive T y - smoothPositive T x := by
  have hg (u : ℝ) : HasGradientAt ramp (CompactSmoothMaximum.slope u) u := by
    simpa using (ramp_hasDerivAt u).hasGradientAt
  have hh := OracleTemplate.Gradient.convex_support ramp_convex hg
    ((x + T) / (2 * T)) ((y + T) / (2 * T))
  simp only [Real.inner_apply] at hh
  have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * T by positivity)
  have he : 2 * T * (CompactSmoothMaximum.slope ((x + T) / (2 * T)) *
      ((y + T) / (2 * T) - (x + T) / (2 * T))) = CompactSmoothMaximum.slope ((x + T) / (2 * T)) * (y - x) := by
    field_simp
    ring
  rw [he] at ht
  simpa only [smoothPositive, mul_sub] using ht

omit [CompleteSpace E] in
lemma wall_support (a B : ℝ) (ha : 0 ≤ a) (x y : E) :
    ⟪a • x, y - x⟫ ≤ wall a B y - wall a B x := by
  have hn := norm_sub_sq_real y x
  have hp := mul_nonneg (show 0 ≤ a / 2 by positivity) (sq_nonneg ‖y - x‖)
  simp only [wall, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm] at hn
  nlinarith only [congrArg (fun t : ℝ => a / 2 * t) hn, hp]

lemma value_convex (f : E → ℝ) (g : E → E) (a B T : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) :
    ConvexOn ℝ univ (value f a B T) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support (G := field f g a B T)
  intro x y
  have hθ := mixing_bounds f a B T x
  have hf := mul_le_mul_of_nonneg_left (OracleTemplate.Gradient.convex_support hc hg x y) hθ.1
  have hw := mul_le_mul_of_nonneg_left (wall_support a B ha x y) (sub_nonneg.mpr hθ.2)
  simp only [real_inner_smul_left] at hw
  have hh := smoothPositive_support T hT (f x - wall a B x) (f y - wall a B y)
  change mixing f a B T x * ((f y - wall a B y) - (f x - wall a B x)) ≤ _ at hh
  rw [field_convex_combination]
  simp only [value, inner_add_left, real_inner_smul_left]
  linarith only [hf, hw, hh]

noncomputable def mixingDerivative (f : E → ℝ) (a B T : ℝ) (x : E) : ℝ :=
  curvature ((f x - wall a B x + T) / (2 * T)) / (2 * T)

lemma mixing_hasFDerivAt (f : E → ℝ) (g : E → E) (a B T : ℝ)
    (x : E) (hf : HasGradientAt f (g x) x) :
    HasFDerivAt (mixing f a B T)
      (mixingDerivative f a B T x • (InnerProductSpace.toDual ℝ E (g x - a • x))) x := by
  have hh := (smoothPositive_second_hasDerivAt T (f x - wall a B x)).comp_hasFDerivAt x
    (hf.hasFDerivAt.sub (wall_hasGradientAt a B x).hasFDerivAt)
  convert hh using 1
  · rfl
  · ext y
    simp only [mixingDerivative, smul_apply, sub_apply, InnerProductSpace.toDual_apply_apply,
      inner_sub_left]

lemma field_hasFDerivAt (f : E → ℝ) (g : E → E) (a B T : ℝ)
    (x : E) (A : E →L[ℝ] E) (hf : HasGradientAt f (g x) x) (hg : HasFDerivAt g A x) :
    HasFDerivAt (field f g a B T)
      (a • ContinuousLinearMap.id ℝ E +
        (mixing f a B T x • (A - a • ContinuousLinearMap.id ℝ E) +
          (mixingDerivative f a B T x • (InnerProductSpace.toDual ℝ E (g x - a • x))).smulRight
            (g x - a • x))) x := by
  have hw : HasFDerivAt (fun y : E => a • y) (a • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul a
  exact hw.add ((mixing_hasFDerivAt f g a B T x hf).smul (hg.sub hw))

lemma field_derivative_norm_bound (f : E → ℝ) (g : E → E) (a B T : ℝ)
    (ha : 0 ≤ a) (hT : 0 < T) (x : E) (A : E →L[ℝ] E)
    (hf : HasGradientAt f (g x) x) (hg : HasFDerivAt g A x) :
    ‖fderiv ℝ (field f g a B T) x‖ ≤
      a + mixing f a B T x * (‖A‖ + a) + mixingDerivative f a B T x * ‖g x - a • x‖ ^ 2 := by
  have hθ := (mixing_bounds f a B T x).1
  have hχ := (smoothPositive_curvature_bound hT (f x - wall a B x)).1
  change 0 ≤ mixingDerivative f a B T x at hχ
  have hi : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ a := by
    rw [norm_smul, Real.norm_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ha).trans_eq (mul_one _)
  have hd : ‖InnerProductSpace.toDual ℝ E (g x - a • x)‖ = ‖g x - a • x‖ :=
    (InnerProductSpace.toDual ℝ E).norm_map _
  have hr : ‖(mixingDerivative f a B T x • (InnerProductSpace.toDual ℝ E (g x - a • x))).smulRight
      (g x - a • x)‖ = mixingDerivative f a B T x * ‖g x - a • x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_of_nonneg hχ, hd]
    ring
  have hm : ‖mixing f a B T x • (A - a • ContinuousLinearMap.id ℝ E)‖ ≤
      mixing f a B T x * (‖A‖ + a) := by
    rw [norm_smul, Real.norm_of_nonneg hθ]
    apply mul_le_mul_of_nonneg_left _ hθ
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hi)
  rw [(field_hasFDerivAt f g a B T x A hf hg).fderiv]
  have h1 := norm_add_le (a • ContinuousLinearMap.id ℝ E)
    (mixing f a B T x • (A - a • ContinuousLinearMap.id ℝ E) +
      (mixingDerivative f a B T x • (InnerProductSpace.toDual ℝ E (g x - a • x))).smulRight
        (g x - a • x))
  have h2 := norm_add_le (mixing f a B T x • (A - a • ContinuousLinearMap.id ℝ E))
    ((mixingDerivative f a B T x • (InnerProductSpace.toDual ℝ E (g x - a • x))).smulRight
      (g x - a • x))
  rw [hr] at h2
  linarith only [h1, h2, hi, hm]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_left (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E)
    (hx : f x - wall a B x ≤ -T) : mixing f a B T x = 0 ∧ mixingDerivative f a B T x = 0 := by
  have hh : (f x - wall a B x + T) / (2 * T) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp only [mixing, mixingDerivative, CompactSmoothMaximum.slope, curvature, hh, ↓reduceIte, zero_div,
    and_self]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_right (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E)
    (hx : T ≤ f x - wall a B x) : mixing f a B T x = 1 ∧ mixingDerivative f a B T x = 0 := by
  have hh : 1 ≤ (f x - wall a B x + T) / (2 * T) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  rcases eq_or_lt_of_le hh with he | he
  · simp only [mixing, mixingDerivative, ← he, CompactSmoothMaximum.slope, curvature]
    norm_num
  · have hp : ¬(f x - wall a B x + T) / (2 * T) ≤ 0 := by linarith
    simp only [mixing, mixingDerivative, CompactSmoothMaximum.slope, curvature, hp, not_le.mpr he,
      ↓reduceIte, zero_div, and_self]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixingDerivative_bounds (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E) :
    0 ≤ mixingDerivative f a B T x ∧ mixingDerivative f a B T x ≤ 1 / T :=
  smoothPositive_curvature_bound hT (f x - wall a B x)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mixing_outside (f : E → ℝ) (a B T : ℝ) (hT : 0 < T) (x : E)
    (hx : ¬|f x - wall a B x| ≤ T) :
    (mixing f a B T x = 0 ∨ mixing f a B T x = 1) ∧ mixingDerivative f a B T x = 0 := by
  by_cases hl : f x - wall a B x ≤ -T
  · have hh := mixing_left f a B T hT x hl
    exact ⟨Or.inl hh.1, hh.2⟩
  · have hr : T ≤ f x - wall a B x := by
      by_contra h
      apply hx
      exact abs_le.mpr ⟨(lt_of_not_ge hl).le, (lt_of_not_ge h).le⟩
    have hh := mixing_right f a B T hT x hr
    exact ⟨Or.inr hh.1, hh.2⟩

end LongTails.Proofs.GeneralizedSmoothShieldCalculus
