import LongTails.Proofs.QuadraticEnvelope
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SmoothInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma finite_envelope {ι : Type*} [Finite ι] [Nonempty ι] {L : ℝ} (hL : 0 < L)
    (x : ι → E) (z : ι → E × ℝ)
    (hs : ∀ i j, 0 ≤ (z j).2 - (z i).2 - L * ⟪x i - (z i).1, (z j).1 - (z i).1⟫) :
    ∃ (f : E → ℝ) (g : E → E),
      (∀ a, HasGradientAt f (g a) a) ∧
      (∀ a b, f a + ⟪g a, b - a⟫ ≤ f b) ∧
      (∀ a b, ‖g a - g b‖ ≤ L * ‖a - b‖) ∧
      (∀ i, f (x i) = L / 2 * ‖x i - (z i).1‖ ^ 2 + (z i).2 ∧
        g (x i) = L • (x i - (z i).1)) := by
  let K := convexHull ℝ (Set.range z)
  have hK : IsCompact K := (Set.finite_range z).isCompact_convexHull ℝ
  have hc : Convex ℝ K := convex_convexHull ℝ (Set.range z)
  have hi : ∀ i, z i ∈ K := fun i => subset_convexHull ℝ (Set.range z) (Set.mem_range_self i)
  have hn : K.Nonempty := ⟨z (Classical.arbitrary ι), hi _⟩
  refine ⟨QuadraticEnvelope.envelope L K hK hn, QuadraticEnvelope.field L K hK hn,
    fun a => QuadraticEnvelope.envelope_hasGradient hL.le hc hK hn a,
    fun a b => QuadraticEnvelope.envelope_lower hL.le hc hK hn a b,
    fun a b => QuadraticEnvelope.field_lipschitz hL hc hK hn a b, ?_⟩
  intro i
  apply QuadraticEnvelope.envelope_at_minimum hL hc hK hn (x i) (z i) (hi i)
  apply QuadraticEnvelope.cost_minimum_of_support hL.le
  apply QuadraticEnvelope.support_convexHull
  rintro b ⟨j, rfl⟩
  exact hs i j

omit [CompleteSpace E] in
lemma support_identity {L : ℝ} (hL : L ≠ 0) (xi xj gi gj : E) (fi fj : ℝ) :
    (fj - ‖gj‖ ^ 2 / (2 * L)) - (fi - ‖gi‖ ^ 2 / (2 * L)) -
      L * ⟪xi - (xi - (1 / L) • gi),
        (xj - (1 / L) • gj) - (xi - (1 / L) • gi)⟫ =
      fj - fi - ⟪gi, xj - xi⟫ - ‖gj - gi‖ ^ 2 / (2 * L) := by
  simp only [sub_sub_cancel, inner_sub_right,
    real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, real_inner_comm gj gi]
  field_simp [hL]
  ring

lemma smooth_interpolation {ι : Type*} [Finite ι] [Nonempty ι] {L : ℝ} (hL : 0 < L)
    (x g : ι → E) (v : ι → ℝ)
    (hs : ∀ i j, v i + ⟪g i, x j - x i⟫ + ‖g j - g i‖ ^ 2 / (2 * L) ≤ v j) :
    ∃ (f : E → ℝ) (G : E → E),
      (∀ a, HasGradientAt f (G a) a) ∧
      (∀ a b, f a + ⟪G a, b - a⟫ ≤ f b) ∧
      (∀ a b, ‖G a - G b‖ ≤ L * ‖a - b‖) ∧
      (∀ i, f (x i) = v i ∧ G (x i) = g i) := by
  let z : ι → E × ℝ := fun i => (x i - (1 / L) • g i, v i - ‖g i‖ ^ 2 / (2 * L))
  have hz : ∀ i j, 0 ≤ (z j).2 - (z i).2 - L * ⟪x i - (z i).1, (z j).1 - (z i).1⟫ := by
    intro i j
    dsimp only [z]
    rw [support_identity hL.ne']
    linarith [hs i j]
  obtain ⟨f, G, hf, hc, hG, hv⟩ := finite_envelope hL x z hz
  refine ⟨f, G, hf, hc, hG, fun i => ?_⟩
  obtain ⟨hfi, hgi⟩ := hv i
  dsimp only [z] at hfi hgi
  simp only [sub_sub_cancel] at hfi hgi
  constructor
  · rw [hfi, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
    field_simp
    ring
  · rw [hgi, smul_smul]
    simp [hL.ne']

omit [CompleteSpace E] in
lemma shifted_interpolation_identity (L μ : ℝ) (xi xj gi gj : E) (vi vj : ℝ) :
    2 * (L - μ) * ((vj - μ / 2 * ‖xj‖ ^ 2) - (vi - μ / 2 * ‖xi‖ ^ 2) -
      ⟪gi - μ • xi, xj - xi⟫) - ‖(gj - μ • xj) - (gi - μ • xi)‖ ^ 2 =
    2 * (L - μ) * (vj - vi - ⟪gi, xj - xi⟫) - ‖gj - gi‖ ^ 2 -
      μ * L * ‖xj - xi‖ ^ 2 + 2 * μ * ⟪gj - gi, xj - xi⟫ := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm xj xi, real_inner_comm xj gi, real_inner_comm xi gi]
  ring

lemma shifted_interpolation {ι : Type*} [Finite ι] [Nonempty ι] {L μ : ℝ}
    (hμL : μ < L) (x g : ι → E) (v : ι → ℝ)
    (hs : ∀ i j, ‖g j - g i‖ ^ 2 + μ * L * ‖x j - x i‖ ^ 2 -
      2 * μ * ⟪g j - g i, x j - x i⟫ ≤
        2 * (L - μ) * (v j - v i - ⟪g i, x j - x i⟫)) :
    ∃ (f : E → ℝ) (G : E → E),
      (∀ a, HasGradientAt f (G a) a) ∧
      (∀ a b, f a + ⟪G a, b - a⟫ ≤ f b) ∧
      (∀ a b, ‖G a - G b‖ ≤ (L - μ) * ‖a - b‖) ∧
      (∀ i, f (x i) = v i - μ / 2 * ‖x i‖ ^ 2 ∧ G (x i) = g i - μ • x i) := by
  apply smooth_interpolation (sub_pos.mpr hμL) x (fun i => g i - μ • x i)
    (fun i => v i - μ / 2 * ‖x i‖ ^ 2)
  intro i j
  have hid := shifted_interpolation_identity L μ (x i) (x j) (g i) (g j) (v i) (v j)
  have hp : 0 < 2 * (L - μ) := by linarith
  have he : ‖(g j - μ • x j) - (g i - μ • x i)‖ ^ 2 / (2 * (L - μ)) ≤
      (v j - μ / 2 * ‖x j‖ ^ 2) - (v i - μ / 2 * ‖x i‖ ^ 2) -
        ⟪g i - μ • x i, x j - x i⟫ := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [hs i j]
  linarith

lemma add_quadratic_gradient {f : E → ℝ} {g x : E} (hf : HasGradientAt f g x) (μ : ℝ) :
    HasGradientAt (fun y => f y + μ / 2 * ‖y‖ ^ 2) (g + μ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  convert hf.add ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2)) using 1
  ext y
  simp [toDual_apply_apply, innerSL_apply_apply]
  ring

lemma strong_interpolation {ι : Type*} [Finite ι] [Nonempty ι] {L μ : ℝ}
    (hμ : 0 ≤ μ) (hμL : μ < L) (x g : ι → E) (v : ι → ℝ)
    (hs : ∀ i j, ‖g j - g i‖ ^ 2 + μ * L * ‖x j - x i‖ ^ 2 -
      2 * μ * ⟪g j - g i, x j - x i⟫ ≤
        2 * (L - μ) * (v j - v i - ⟪g i, x j - x i⟫)) :
    ∃ (f : E → ℝ) (G : E → E),
      (∀ a, HasGradientAt f (G a) a) ∧
      (∀ a b, f a + ⟪G a, b - a⟫ + μ / 2 * ‖b - a‖ ^ 2 ≤ f b) ∧
      (∀ a b, ‖G a - G b‖ ≤ L * ‖a - b‖) ∧
      (∀ i, f (x i) = v i ∧ G (x i) = g i) := by
  obtain ⟨f, G, hf, hc, hl, hi⟩ := shifted_interpolation hμL x g v hs
  refine ⟨fun a => f a + μ / 2 * ‖a‖ ^ 2, fun a => G a + μ • a,
    fun a => add_quadratic_gradient (hf a) μ, ?_, ?_, ?_⟩
  · intro a b
    have h := hc a b
    simp only [inner_add_left, real_inner_smul_left, inner_sub_right]
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm b a]
    simp only [inner_sub_right] at h
    nlinarith
  · intro a b
    have he : (G a + μ • a) - (G b + μ • b) = (G a - G b) + μ • (a - b) := by module
    rw [he]
    calc
      _ ≤ ‖G a - G b‖ + ‖μ • (a - b)‖ := norm_add_le _ _
      _ ≤ (L - μ) * ‖a - b‖ + μ * ‖a - b‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
        linarith [hl a b]
      _ = L * ‖a - b‖ := by ring
  · intro i
    obtain ⟨hv, hg⟩ := hi i
    constructor
    · dsimp only
      rw [hv]
      ring
    · dsimp only
      rw [hg]
      module

end LongTails.Proofs.SmoothInterpolation
