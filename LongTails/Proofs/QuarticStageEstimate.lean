import LongTails.Algorithms.QuarticMetricStage
import LongTails.Proofs.GuardedAcceleratedGeometry
import LongTails.Proofs.GuardedMetricDescent

namespace LongTails.Proofs.QuarticStageEstimate

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def estimate (p : Parameters E) : List (Plane E) → Point E → ℝ
  | [], u => p.center.value + p.μ / 2 * ‖p.S (u.x - p.center.x)‖ ^ 2
  | plane :: history, u => (1 - p.a) * estimate p history u + p.a *
      (value p plane.point + ⟪gradient p plane.point, u.x - plane.point.x⟫ +
        p.μ / 2 * ‖p.S (u.x - plane.point.x)‖ ^ 2)

omit [FiniteDimensional ℝ E] in
lemma estimate_support (p : Parameters E) (history : List (Plane E)) (u : Point E)
    (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hs : ∀ plane ∈ history, supports p u plane.point) :
    estimate p history u ≤ (1 - p.a) ^ history.length *
        (p.center.value + p.μ / 2 * ‖p.S (u.x - p.center.x)‖ ^ 2) +
      (1 - (1 - p.a) ^ history.length) * value p u := by
  induction history with
  | nil => simp [estimate]
  | cons plane history ih =>
    have hh := ih (fun plane hp => hs plane (List.mem_cons_of_mem _ hp))
    have hplane := hs plane (List.mem_cons_self)
    have hw := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ha₁)
    have hp := mul_le_mul_of_nonneg_left hplane ha
    simp only [estimate, List.length_cons, pow_succ]
    nlinarith

omit [FiniteDimensional ℝ E] in
lemma estimate_center (p : Parameters E) (history : List (Plane E))
    (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hs : ∀ plane ∈ history, supports p p.center plane.point) :
    estimate p history p.center ≤ p.center.value := by
  have hh := estimate_support p history p.center ha ha₁ hs
  simp [value, regularizedValue] at hh
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma initial_representation (p : Parameters E) (u : Point E) :
    estimate p [] u = p.center.value + p.μ / 2 * ‖p.S u.x - p.S p.center.x‖ ^ 2 := by
  simp only [estimate, map_sub]

lemma updated_representation (p : Parameters E) (history : List (Plane E)) (plane : Plane E)
    {φ : ℝ} {z : E} (hμ : p.μ ≠ 0)
    (hrep : ∀ u, estimate p history u = φ + p.μ / 2 * ‖p.S u.x - z‖ ^ 2) (u : Point E) :
    estimate p (plane :: history) u =
      GuardedAcceleratedGeometry.minimumUpdate p.a p.μ φ (value p plane.point)
        (p.S plane.point.x) z (transformedGradient p.S (gradient p plane.point)) +
      p.μ / 2 * ‖p.S u.x - centerStep p.a p.μ (p.S plane.point.x) z
        (transformedGradient p.S (gradient p plane.point))‖ ^ 2 := by
  rw [estimate, hrep]
  rw [GuardedMetricDescent.metric_pairing p.S, map_sub]
  exact GuardedAcceleratedGeometry.estimate_quadratic_identity hμ _ _ _ _

omit [FiniteDimensional ℝ E] in
lemma estimate_displacement (p : Parameters E) (history : List (Plane E))
    {φ : ℝ} {z : E} {x : Point E} (hμ : 0 < p.μ)
    (hcenter : estimate p history p.center ≤ p.center.value)
    (hrep : estimate p history p.center = φ + p.μ / 2 * ‖p.S p.center.x - z‖ ^ 2)
    (hminimum : value p x ≤ φ) (hgap : p.center.value - p.q ≤ x.value) (hα : 0 ≤ p.α) :
    ‖p.S p.center.x - z‖ ^ 2 ≤ 2 * p.q / p.μ := by
  have hf : x.value ≤ value p x := by
    unfold value regularizedValue
    exact le_add_of_nonneg_right (by positivity)
  apply (le_div_iff₀ hμ).mpr
  nlinarith

lemma accepted_minimum_step (p : Parameters E) (x y next : Point E) (z : E) {φ : ℝ}
    (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (htune : p.a ^ 2 * p.L = p.μ) (hy : p.S y.x = extrapolate p.a (p.S x.x) z)
    (hφ : value p x ≤ φ) (hsupport : supports p x y)
    (hdescent : value p next ≤ value p y - ‖transformedGradient p.S (gradient p y)‖ ^ 2 / (2 * p.L)) :
    value p next ≤ GuardedAcceleratedGeometry.minimumUpdate p.a p.μ φ (value p y)
      (p.S y.x) z (transformedGradient p.S (gradient p y)) := by
  have hs : value p y + ⟪transformedGradient p.S (gradient p y), p.S x.x - p.S y.x⟫ +
      p.μ * ‖p.S x.x - p.S y.x‖ ^ 2 / 2 ≤ value p x := by
    unfold supports at hsupport
    rw [GuardedMetricDescent.metric_pairing p.S, map_sub] at hsupport
    nlinarith only [hsupport]
  rw [hy] at hs ⊢
  exact GuardedAcceleratedGeometry.minimum_step ha ha₁ hμ hL htune hφ hs hdescent

end LongTails.Proofs.QuarticStageEstimate
