import LongTails.Proofs.QuarticStageInvariant
import LongTails.Proofs.QuarticStageTrial

namespace LongTails.Proofs.QuarticStageModels

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma faithful_regularized_model (p : Parameters E) (f : E → ℝ) (u v : Point E) {β : ℝ}
    (hu : Faithful f u) (hv : Faithful f v) (hα : p.α ≤ β)
    (hL : p.L = 4) (hnorm : β * ‖u.x - v.x‖ ^ 2 ≤ ‖p.S (u.x - v.x)‖ ^ 2)
    (hmodel : f u.x - f v.x - ⟪_root_.gradient f v.x, u.x - v.x⟫ ≤ 9 / 16 * ‖p.S (u.x - v.x)‖ ^ 2) :
    value p u ≤ value p v + ⟪gradient p v, u.x - v.x⟫ + p.L / 2 * ‖p.S (u.x - v.x)‖ ^ 2 := by
  have hh := GuardedMetricDescent.regularized_upper p.S p.center.x u.x v.x (_root_.gradient f v.x)
    hα hnorm hmodel
  simpa only [value, LongTails.Algorithms.QuarticMetricStage.gradient, hu.1, hv.1, hv.2, hL, show (4 : ℝ) / 2 = 2 by norm_num] using hh

lemma trial_guard (p : Parameters E) (snapshot : E) (y : Point E) {A : ℝ}
    (hL : 0 < p.L) (hr : 0 ≤ p.r) (hA : A ≤ p.r / 8)
    (hc : ‖p.S (p.center.x - snapshot)‖ ≤ p.r / 4)
    (hy : ‖p.S (y.x - p.center.x)‖ ≤ A) :
    ‖p.S (y.x - snapshot)‖ ≤ p.r ∧ ‖p.S (trialPoint p y - snapshot)‖ ≤ p.r := by
  have hy' : ‖p.S (y.x - snapshot)‖ ≤ A + p.r / 4 := by
    calc
      _ = ‖p.S (y.x - p.center.x) + p.S (p.center.x - snapshot)‖ := by rw [← map_add]; congr 2; abel
      _ ≤ ‖p.S (y.x - p.center.x)‖ + ‖p.S (p.center.x - snapshot)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hy hc
  have hn : ‖p.S (trialPoint p y - snapshot)‖ ≤ p.r / 2 + (A + p.r / 4) := by
    calc
      _ = ‖p.S (trialPoint p y - y.x) + p.S (y.x - snapshot)‖ := by rw [← map_add]; congr 2; abel
      _ ≤ ‖p.S (trialPoint p y - y.x)‖ + ‖p.S (y.x - snapshot)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (QuarticStageTrial.trial_radius p y hL hr) hy'
  constructor <;> linarith

lemma query_plane_center_support (p : Parameters E) (y : Point E) {A : ℝ}
    (hμ : 0 ≤ p.μ) (hy : ‖p.S (y.x - p.center.x)‖ ≤ A)
    (hs : supports p p.center y) :
    value p y ≤ p.center.value + ‖transformedGradient p.S (gradient p y)‖ * A := by
  have hh := GuardedMetricDescent.support_center_upper p.S p.center.x y.x (gradient p y) hμ hs
  have hv : value p p.center = p.center.value := by simp [value, regularizedValue]
  rw [hv] at hh
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hy (norm_nonneg _)) _)

lemma modeled_continuation (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hα : 0 < p.α) (hr : 0 < p.r)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hA₂ : A ^ 2 = 2 * p.q / p.μ) (hτ₂ : p.α * τ ^ 2 = p.q)
    (hAr : A ≤ p.r / 8) (hq : p.q ≤ p.L * p.r ^ 2 / 16)
    (htune : p.a ^ 2 * p.L = p.μ) (y next : Point E)
    (hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z)
    (hyfaith : Faithful f y) (hnfaith : Faithful f next)
    (hcenter : supports p p.center y) (hsupport : supports p st.accepted y)
    (hnext : next.x = trialPoint p y)
    (hmodel : value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
      p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2)
    (hnosuccess : ¬successful p next) :
    Invariant p f A τ (k + 1) ⟨st.accepted, next,
      centerStep p.a p.μ (p.S y.x) st.z (transformedGradient p.S (gradient p y)),
      ⟨y, st.previous, st.accepted⟩ :: st.history⟩ := by
  have hygeom := query_plane_geometry p f hi ha y hy hyfaith
  have hc := query_plane_center_support p y hμ.le hygeom.point_radius hcenter
  have hd := QuarticStageTrial.trial_descent p y next hL hr.le hnext hmodel
  have hn : p.center.value - p.q < next.value := lt_of_not_ge (not_or.mp hnosuccess).1
  have hf := QuarticStageTrial.trial_full p y next hL hr hα.le hAr hq hnext hc hd hn
  exact continuing_invariant p f hi ha ha₁ hμ hL hα hA hτ hA₂ hτ₂ htune y next hy
    hyfaith hnfaith hcenter hsupport (QuarticStageTrial.full_step_descent p y next hL hf hmodel) hf hnosuccess

lemma snapshot_model (p : Parameters E) (f : E → ℝ) (snapshot : E)
    {L Δ σ R A : ℝ} (hf : ContDiff ℝ 3 f) (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ y, f snapshot - f y ≤ Δ)
    (hS : ∀ v, ‖p.S v‖ ^ 2 = ⟪fderiv ℝ (_root_.gradient f) snapshot v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (hα : p.α ≤ L * σ) (hmetricL : p.L = 4) (hr : p.r = R / 256)
    (hA : A ≤ p.r / 8) (hc : ‖p.S (p.center.x - snapshot)‖ ≤ p.r / 4)
    (y next : Point E) (hy : Faithful f y) (hn : Faithful f next)
    (hyr : ‖p.S (y.x - p.center.x)‖ ≤ A) (hnext : next.x = trialPoint p y) :
    value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
      p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2 := by
  have hL' : 0 < p.L := by rw [hmetricL]; norm_num
  have hr' : 0 ≤ p.r := by rw [hr]; positivity
  have hg := trial_guard p snapshot y hL' hr' hA hc hyr
  rw [← hnext, hr] at hg
  have hh := GuardedMetricSupport.guarded_support_bounds hf hL hσ hR hΔ hRΔ hT snapshot hgap p.S hS
    next.x y.x hg.2 hg.1
  have hl := ThirdOrderObjectiveGeometry.hessian_quadratic_lower hf hL hσ hΔ hT snapshot (next.x - y.x) hgap
  have hs := hS (next.x - y.x)
  have hm : L * σ * ‖next.x - y.x‖ ^ 2 ≤ ‖p.S (next.x - y.x)‖ ^ 2 := by
    nlinarith [mul_nonneg (mul_pos hL hσ).le (sq_nonneg ‖next.x - y.x‖)]
  exact faithful_regularized_model p f next y hn hy hα hmetricL hm hh.2

lemma snapshot_lower (p : Parameters E) (f : E → ℝ) (snapshot : E)
    {L Δ σ R A : ℝ} (hf : ContDiff ℝ 3 f) (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ y, f snapshot - f y ≤ Δ)
    (hS : ∀ v, ‖p.S v‖ ^ 2 = ⟪fderiv ℝ (_root_.gradient f) snapshot v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (hr : p.r = R / 256) (hA : A ≤ p.r / 8)
    (hc : ‖p.S (p.center.x - snapshot)‖ ≤ p.r / 4)
    (u v : E) (hu : ‖p.S (u - p.center.x)‖ ≤ 2 * A) (hv : ‖p.S (v - p.center.x)‖ ≤ A) :
    7 / 16 * ‖p.S (u - v)‖ ^ 2 - 4 * (L * σ) * ‖u - v‖ ^ 2 ≤
      f u - f v - ⟪_root_.gradient f v, u - v⟫ := by
  have hr' : 0 ≤ p.r := by rw [hr]; positivity
  have hguard (x : E) (hx : ‖p.S (x - p.center.x)‖ ≤ 2 * A) : ‖p.S (x - snapshot)‖ ≤ R / 256 := by
    have hh : ‖p.S (x - snapshot)‖ ≤ 2 * A + p.r / 4 := by
      calc
        _ = ‖p.S (x - p.center.x) + p.S (p.center.x - snapshot)‖ := by rw [← map_add]; congr 2; abel
        _ ≤ ‖p.S (x - p.center.x)‖ + ‖p.S (p.center.x - snapshot)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hx hc
    rw [← hr]
    linarith
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans hv
  have hh := GuardedMetricSupport.guarded_support_bounds hf hL hσ hR hΔ hRΔ hT snapshot hgap p.S hS
    u v (hguard u hu) (hguard v (hv.trans (by linarith)))
  nlinarith only [hh.1]

end LongTails.Proofs.QuarticStageModels
