import LongTails.Proofs.ReusedCurvatureSupport
import LongTails.Proofs.MonotoneCurvatureGeometry
import LongTails.Proofs.MonotoneCurvatureTuning
import LongTails.Proofs.QuarticStageTransition
import LongTails.Proofs.ReusedCurvatureCorrection

namespace LongTails.Proofs.MonotoneCurvatureWitness

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma center_curvature {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (c : Point E) (w : Witness E)
    (hi : WitnessInvariant (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) f
      (MonotoneCurvatureTuning.metricRadius H γ t) (MonotoneCurvatureTuning.distanceScale H γ) w)
    (hmetric : ∀ v, ‖S v‖ ^ 2 ≤ ⟪v, A c.x v⟫ + 6 * (t ^ 2 * γ) * ‖v‖ ^ 2) :
    ⟪w.point.x - w.plane.point.x, A c.x (w.point.x - w.plane.point.x)⟫ <
      -γ * ‖w.point.x - w.plane.point.x‖ ^ 2 := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  let τ := MonotoneCurvatureTuning.distanceScale H γ
  have ht0 : 0 < t := by linarith
  have hscale := MonotoneCurvatureTuning.scales S c hH hγ ht
  have hpd : ‖w.plane.point.x - c.x‖ ≤ 3 * τ :=
    plane_distance p f hi.plane_geometry hscale.1 hscale.2.1
  have hdiff : ‖w.point.x - w.plane.point.x‖ ≤ 4 * τ := by
    have hh := norm_sub_le (w.point.x - c.x) (w.plane.point.x - c.x)
    rw [sub_sub_sub_cancel_right] at hh
    have hp := hi.point_distance
    change ‖w.point.x - c.x‖ ≤ τ at hp
    linarith
  have hμ : p.μ < 1 := by
    change 1 / (512 * t ^ 2) < 1
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hmul : 3 * p.μ * (2 * (t ^ 2 * γ)) = 3 * γ / 256 := by
    dsimp [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters]
    field_simp
    ring
  have hτeq : H * τ = γ / 2 ^ 30 := by
    dsimp [τ, MonotoneCurvatureTuning.distanceScale]
    field_simp
  have hlocal : 3 * p.μ * (2 * (t ^ 2 * γ)) +
      2 * (H * (‖w.plane.point.x - p.center.x‖ / 2 +
        ‖w.point.x - w.plane.point.x‖ / 6)) ≤ p.α := by
    rw [hmul]
    change 3 * γ / 256 + 2 * (H * (‖w.plane.point.x - c.x‖ / 2 +
      ‖w.point.x - w.plane.point.x‖ / 6)) ≤ γ
    have h₁ := mul_le_mul_of_nonneg_left hpd hH.le
    have h₂ := mul_le_mul_of_nonneg_left hdiff hH.le
    nlinarith
  exact ReusedCurvatureSupport.failed_support_center_curvature (δ := 2 * (t ^ 2 * γ)) hf hg hLip p w.point w.plane.point
    hi.point_faithful.1 hi.plane_geometry.point_faithful.1 hi.plane_geometry.point_faithful.2
    hγ hscale.2.2.1.le hμ (by
      dsimp [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters]
      convert hmetric (w.point.x - w.plane.point.x) using 1
      ring)
    hlocal hi.failure

lemma escape_descent {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (c : Point E) (w : Witness E) (hc : Faithful f c)
    (hcurv : ⟪w.point.x - w.plane.point.x, A c.x (w.point.x - w.plane.point.x)⟫ <
      -γ * ‖w.point.x - w.plane.point.x‖ ^ 2) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    f (LongTails.Algorithms.MonotoneCurvatureStage.witnessPoint p w) ≤
      c.value - γ * (γ / (1024 * H)) ^ 2 / 3 ∧
    ‖LongTails.Algorithms.MonotoneCurvatureStage.witnessPoint p w - c.x‖ = γ / (1024 * H) := by
  let v := w.point.x - w.plane.point.x
  have hv : v ≠ 0 := by
    intro hh
    change ⟪v, A c.x v⟫ < -γ * ‖v‖ ^ 2 at hcurv
    simp [hh] at hcurv
  let z := LongTails.Algorithms.MonotoneCurvatureStage.signedDirection c.gradient v
  have hz : ‖z‖ = 1 := MonotoneCurvatureGeometry.signed_direction_norm _ _ hv
  have hsign : ⟪_root_.gradient f c.x, z⟫ ≤ 0 := by
    rw [← hc.2]
    exact MonotoneCurvatureGeometry.signed_direction_pairing _ _
  have hcz : ⟪z, A c.x z⟫ ≤ -γ :=
    MonotoneCurvatureGeometry.signed_direction_curvature _ _ _ hv hcurv.le
  have hη : 0 < γ / (1024 * H) := by positivity
  have hηH : H * (γ / (1024 * H)) ≤ γ := by
    have he : H * (γ / (1024 * H)) = γ / 1024 := by field_simp
    rw [he]
    linarith
  have hd := ReusedCurvatureCorrection.negative_curvature_descent hf hg hLip c.x z hz hη.le hsign hcz hηH
  refine ⟨?_, ?_⟩
  · change f (c.x + (γ / (1024 * H)) • z) ≤ c.value - γ * (γ / (1024 * H)) ^ 2 / 3
    simpa only [hc.1] using hd
  · change ‖c.x + (γ / (1024 * H)) • z - c.x‖ = γ / (1024 * H)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hη, hz, mul_one]

end LongTails.Proofs.MonotoneCurvatureWitness
