import LongTails.Proofs.GeneralizedSmoothShieldCalculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothShieldGeometry

open GeneralizedSmoothShield GeneralizedSmoothShieldCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma scaled_wall (a G : ℝ) (ha : 0 < a) (hG : 0 < G) (x : E) :
    a / G ^ 2 * wall a (16 * G / a) x = (a * ‖x‖ / G) ^ 2 / 2 - 128 := by
  unfold wall
  field_simp
  ring

omit [InnerProductSpace ℝ E] in
lemma scaled_gap (f : E → ℝ) (a G : ℝ) (ha : 0 < a) (hG : 0 < G) (x : E) :
    a / G ^ 2 * (f x - wall a (16 * G / a) x) =
      a * f x / G ^ 2 - ((a * ‖x‖ / G) ^ 2 / 2 - 128) := by
  rw [mul_sub, scaled_wall a G ha hG x]
  ring

omit [InnerProductSpace ℝ E] in
lemma scaled_upper (f : E → ℝ) (a G : ℝ) (ha : 0 < a) (hG : 0 < G) (x : E)
    (hf : f x ≤ G * ‖x‖ + G ^ 2 / a) : a * f x / G ^ 2 ≤ a * ‖x‖ / G + 1 := by
  have hh := mul_le_mul_of_nonneg_left hf (show 0 ≤ a / G ^ 2 by positivity)
  have he : a / G ^ 2 * (G * ‖x‖ + G ^ 2 / a) = a * ‖x‖ / G + 1 := by field_simp
  rw [he] at hh
  simpa only [div_mul_eq_mul_div] using hh

omit [InnerProductSpace ℝ E] in
lemma transition_bounds (f : E → ℝ) (a G : ℝ) (ha : 0 < a) (hG : 0 < G) (x : E)
    (hf0 : 0 ≤ f x) (hf : f x ≤ G * ‖x‖ + G ^ 2 / a)
    (hgap : |f x - wall a (16 * G / a) x| ≤ 64 * G ^ 2 / a) :
    11 * G / a ≤ ‖x‖ ∧ ‖x‖ ≤ 21 * G / a := by
  have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ a / G ^ 2 by positivity)
  have he : a / G ^ 2 * (64 * G ^ 2 / a) = 64 := by field_simp
  rw [he, ← abs_of_pos (show 0 < a / G ^ 2 by positivity), ← abs_mul,
    scaled_gap f a G ha hG x] at hh
  have ht := transition_radius_bounds (a * ‖x‖ / G) (a * f x / G ^ 2) (by positivity)
    (by positivity) (scaled_upper f a G ha hG x hf) hh
  have h1 := (le_div_iff₀ hG).mp ht.1
  have h2 := (div_le_iff₀ hG).mp ht.2
  constructor
  · apply (div_le_iff₀ ha).mpr
    nlinarith only [h1]
  · apply (le_div_iff₀ ha).mpr
    nlinarith only [h2]

omit [InnerProductSpace ℝ E] in
lemma interior_separation (f : E → ℝ) (a G r : ℝ) (ha : 0 < a) (hG : 0 < G)
    (har : a * r ≤ G) (x : E) (hx : ‖x‖ ≤ 2 * r) (hf : 0 ≤ f x) :
    64 * G ^ 2 / a ≤ f x - wall a (16 * G / a) x := by
  have ht : a * ‖x‖ / G ≤ 2 := by
    apply (div_le_iff₀ hG).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx ha.le]
  have hw := inner_wall_separation (a * ‖x‖ / G) (by positivity) ht
  rw [← scaled_wall a G ha hG x] at hw
  have hh : 64 ≤ a / G ^ 2 * (f x - wall a (16 * G / a) x) := by
    rw [mul_sub]
    have hp : 0 ≤ a / G ^ 2 * f x := by positivity
    linarith
  have he : 64 * G ^ 2 / a * (a / G ^ 2) = 64 := by field_simp
  apply (mul_le_mul_iff_of_pos_right (show 0 < a / G ^ 2 by positivity)).mp
  rw [he, mul_comm (f x - _)]
  exact hh

omit [InnerProductSpace ℝ E] in
lemma exterior_separation (f : E → ℝ) (a G : ℝ) (ha : 0 < a) (hG : 0 < G) (x : E)
    (hx : 24 * G / a ≤ ‖x‖) (hf : f x ≤ G * ‖x‖ + G ^ 2 / a) :
    f x - wall a (16 * G / a) x ≤ -(64 * G ^ 2 / a) := by
  have ht : 24 ≤ a * ‖x‖ / G := by
    apply (le_div_iff₀ hG).mpr
    have hh := (div_le_iff₀ ha).mp hx
    nlinarith only [hh]
  have hw := outer_wall_separation (a * ‖x‖ / G) (a * f x / G ^ 2) ht
    (scaled_upper f a G ha hG x hf)
  have hh : a / G ^ 2 * (f x - wall a (16 * G / a) x) ≤ -64 := by
    rw [scaled_gap f a G ha hG x]
    linarith
  have he : a / G ^ 2 * (-(64 * G ^ 2 / a)) = -64 := by field_simp
  apply (mul_le_mul_iff_of_pos_left (show 0 < a / G ^ 2 by positivity)).mp
  rw [he]
  exact hh

lemma convex_value_upper [CompleteSpace E] (f : E → ℝ) (g : E → E) (G r : ℝ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) (z x : E)
    (hz : f z = 0) (hzr : ‖z‖ ≤ r) (hG : ‖g x‖ ≤ G) : f x ≤ G * (‖x‖ + r) := by
  have hs := OracleTemplate.Gradient.convex_support hc hg x z
  have hi := (abs_le.mp (abs_real_inner_le_norm (g x) (z - x))).1
  have hn : ‖z - x‖ ≤ ‖x‖ + r := by
    have hh := norm_sub_le z x
    linarith
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  calc
    f x ≤ ‖g x‖ * ‖z - x‖ := by rw [hz] at hs; linarith
    _ ≤ G * (‖x‖ + r) := mul_le_mul hG hn (norm_nonneg _) hG0

omit [InnerProductSpace ℝ E] in
lemma enlarged_upper (a G r : ℝ) (ha : 0 < a) (hG : 0 ≤ G) (hr : 0 ≤ r) (x : E) :
    G * (‖x‖ + r) ≤ (G + a * r) * ‖x‖ + (G + a * r) ^ 2 / a := by
  have hg : 0 ≤ G + a * r := by positivity
  have h1 : G ≤ G + a * r := by have hh := mul_nonneg ha.le hr; linarith
  have h2 : a * r ≤ G + a * r := by linarith
  have hm := mul_le_mul h1 h2 (mul_nonneg ha.le hr) hg
  have ht : G * r ≤ (G + a * r) ^ 2 / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [hm]
  have hx := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  nlinarith only [hx, ht]

end LongTails.Proofs.GeneralizedSmoothShieldGeometry
