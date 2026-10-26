import LongTails.Proofs.RecursiveEnvelopeGeometry
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticEnvelopeGeometry

open RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma model_hasGradientAt {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (x : E) : HasGradientAt f (g x) x := by
  rw [hasGradientAt_iff_tendsto]
  have hc : Continuous (fun y : E => L / 2 * ‖y - x‖) := by fun_prop
  have hl : Filter.Tendsto (fun y : E => L / 2 * ‖y - x‖) (nhds x) (nhds 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto x
  apply squeeze_zero (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hl
  intro y
  have hlo : 0 ≤ f y - f x - ⟪g x, y - x⟫ := by linarith [h.lower x y]
  have hup : f y - f x - ⟪g x, y - x⟫ ≤ L / 2 * ‖y - x‖ ^ 2 := by
    linarith [h.upper x y]
  rw [Real.norm_eq_abs, abs_of_nonneg hlo]
  by_cases hz : y = x
  · subst y
    simp
  · have hn : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
    calc
      _ ≤ ‖y - x‖⁻¹ * (L / 2 * ‖y - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hup (inv_nonneg.mpr (norm_nonneg _))
      _ = L / 2 * ‖y - x‖ := by field_simp

omit [CompleteSpace E] in
lemma model_convex {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (h.lower z x) ha
  have hy := mul_le_mul_of_nonneg_left (h.lower z y) hb
  have he : a * ⟪g z, x - z⟫ + b * ⟪g z, y - z⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hz : a • (x - z) + b • (y - z) = 0 := by
      rw [smul_sub, smul_sub]
      calc
        _ = (a • x + b • y) - (a + b) • z := by rw [add_smul]; abel
        _ = 0 := by rw [hab, one_smul]; exact sub_self z
    rw [hz, inner_zero_right]
  change f z ≤ a * f x + b * f y
  have hz : a * f z + b * f z = f z := by rw [← add_mul, hab, one_mul]
  nlinarith only [hx, hy, he, hz]

lemma center_field_bound {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (center : E) :
    ‖g center‖ ≤ (L + μ) * ‖center - prox g μ center‖ := by
  have hp : ‖g (prox g μ center)‖ = μ * ‖center - prox g μ center‖ := by
    rw [h.prox_field hμ, envelopeField, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
  have ht := norm_le_norm_sub_add (g center) (g (prox g μ center))
  have hl := h.lipschitz center (prox g μ center)
  rw [hp] at ht
  nlinarith only [ht, hl]

lemma localized_field_bound {L μ D : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (center anchor x : E)
    (ha : ‖anchor - prox g μ center‖ ≤ D) (hx : ‖x - anchor‖ ≤ D) :
    ‖g x‖ ≤ μ * ‖center - prox g μ center‖ + 2 * L * D := by
  have hd : ‖x - prox g μ center‖ ≤ 2 * D := by
    linarith [norm_sub_le_norm_sub_add_norm_sub x anchor (prox g μ center)]
  have hp : ‖g (prox g μ center)‖ = μ * ‖center - prox g μ center‖ := by
    rw [h.prox_field hμ, envelopeField, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
  have ht := norm_le_norm_sub_add (g x) (g (prox g μ center))
  have hl := (h.lipschitz x (prox g μ center)).trans
    (mul_le_mul_of_nonneg_left hd h.pos.le)
  rw [hp] at ht
  linarith

lemma localized_affine_scale {L μ D a s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (ha0 : 0 ≤ a) (center anchor x : E)
    (ha : ‖anchor - prox g μ center‖ ≤ D) (hx : ‖x - anchor‖ ≤ D) :
    s + a * ‖g x‖ ≤ s + a * μ * ‖center - prox g μ center‖ + 2 * a * L * D := by
  have hb := mul_le_mul_of_nonneg_left (localized_field_bound h hμ center anchor x ha hx) ha0
  nlinarith only [hb]

lemma regularized_mixed_error {L μ a s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (ha : 0 ≤ a) (center x reply : E)
    (herr : ‖reply - g x‖ ≤ a * ‖g x‖ + s) :
    ‖(reply + μ • (x - center)) - (g x + μ • (x - center))‖ ≤
      (2 * a) * ‖g x + μ • (x - center)‖ + a * μ * ‖center - prox g μ center‖ + s := by
  have hb := mul_le_mul_of_nonneg_left (h.regularized_oracle_bound hμ center x) ha
  have he : (reply + μ • (x - center)) - (g x + μ • (x - center)) = reply - g x := by
    abel
  rw [he]
  nlinarith only [herr, hb]

lemma prox_nonexpansive {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (x y : E) :
    ‖prox g μ x - prox g μ y‖ ≤ ‖x - y‖ := by
  let u := prox g μ x
  let v := prox g μ y
  have hu : g u = μ • (x - u) := h.prox_field hμ x
  have hv : g v = μ • (y - v) := h.prox_field hμ y
  have he : g u - g v = μ • ((x - y) - (u - v)) := by
    rw [hu, hv]
    module
  have hm := h.monotone u v
  rw [he, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hi := real_inner_le_norm (x - y) (u - v)
  have hh := mul_le_mul_of_nonneg_left hi hμ.le
  change ‖u - v‖ ≤ ‖x - y‖
  by_cases hz : ‖u - v‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hs : ‖u - v‖ ^ 2 ≤ ‖x - y‖ * ‖u - v‖ := by nlinarith
    nlinarith

lemma prox_fixed {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) {xs : E} (hz : g xs = 0) :
    prox g μ xs = xs := by
  have hd := h.regularized_distance hμ xs xs
  simp only [hz, sub_self, smul_zero, add_zero, norm_zero] at hd
  have he : ‖xs - prox g μ xs‖ = 0 := by nlinarith [norm_nonneg (xs - prox g μ xs)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

lemma prox_distance_to_stationary {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) {xs : E} (hz : g xs = 0) (x : E) :
    ‖prox g μ x - xs‖ ≤ ‖x - xs‖ := by
  simpa only [prox_fixed h hμ hz] using prox_nonexpansive h hμ x xs

omit [CompleteSpace E] in
lemma recovery_additive {μ δ : ℝ} {f : E → ℝ} {g : E → E}
    (hμ : 0 ≤ μ) (center x xs : E)
    (hx : regularized f μ center x - envelope f g μ center ≤ δ) :
    f x - f xs ≤ envelope f g μ center - f xs + δ := by
  have hn : 0 ≤ μ / 2 * ‖x - center‖ ^ 2 := by positivity
  unfold regularized at hx
  linarith

lemma recovery_distance {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (center x xs : E) :
    f x - f xs ≤ envelope f g μ center - f xs +
      (L + μ) / 2 * ‖x - prox g μ center‖ ^ 2 := by
  apply recovery_additive hμ.le center x xs
  have hh := h.regularized_upper (μ := μ) center (prox g μ center) x
  rw [h.prox_stationary hμ, inner_zero_left, add_zero] at hh
  change regularized f μ center x - regularized f μ center (prox g μ center) ≤ _
  linarith

omit [CompleteSpace E] in
lemma recovery_radius {μ ε : ℝ} {f : E → ℝ} {g : E → E}
    (hμ : 0 < μ) (hε : 0 ≤ ε) {xs center : E} (hm : ∀ x, f xs ≤ f x)
    (hgap : envelope f g μ center - f xs ≤ ε) :
    ‖center - prox g μ center‖ ≤ Real.sqrt (2 * ε / μ) := by
  have hf := hm (prox g μ center)
  unfold envelope regularized at hgap
  rw [norm_sub_rev (prox g μ center) center] at hgap
  have hb : ‖center - prox g μ center‖ ^ 2 ≤ 2 * ε / μ := by
    apply (le_div_iff₀ hμ).mpr
    nlinarith
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hb

end LongTails.Proofs.StochasticEnvelopeGeometry
