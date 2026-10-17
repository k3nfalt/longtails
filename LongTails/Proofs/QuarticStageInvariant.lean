import LongTails.Proofs.QuarticStageEstimate
import LongTails.Proofs.QuarticStageExecution

namespace LongTails.Proofs.QuarticStageInvariant

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageEstimate
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def Faithful (f : E → ℝ) (x : Point E) : Prop :=
  x.value = f x.x ∧ x.gradient = _root_.gradient f x.x

structure PlaneGeometry (p : Parameters E) (f : E → ℝ) (A τ : ℝ) (plane : Plane E) : Prop where
  point_faithful : Faithful f plane.point
  previous_faithful : Faithful f plane.previous
  accepted_faithful : Faithful f plane.accepted
  previous_value : value p plane.previous ≤ p.center.value
  accepted_value : value p plane.accepted ≤ p.center.value
  previous_gap : p.center.value - p.q ≤ plane.previous.value
  accepted_gap : p.center.value - p.q ≤ plane.accepted.value
  previous_radius : ‖p.S (plane.previous.x - p.center.x)‖ ≤ A
  accepted_radius : ‖p.S (plane.accepted.x - p.center.x)‖ ≤ A
  point_radius : ‖p.S (plane.point.x - p.center.x)‖ ≤ A
  previous_distance : ‖plane.previous.x - p.center.x‖ ≤ τ
  accepted_distance : ‖plane.accepted.x - p.center.x‖ ≤ τ
  extrapolation : plane.point.x = plane.accepted.x + ((1 - p.a) / (1 + p.a)) •
    (plane.accepted.x - plane.previous.x)

structure Invariant (p : Parameters E) (f : E → ℝ) (A τ : ℝ) (k : ℕ) (st : State E) : Prop where
  previous_faithful : Faithful f st.previous
  accepted_faithful : Faithful f st.accepted
  previous_value : value p st.previous ≤ p.center.value
  accepted_value : value p st.accepted ≤ p.center.value
  previous_gap : p.center.value - p.q ≤ st.previous.value
  accepted_gap : p.center.value - p.q ≤ st.accepted.value
  previous_radius : ‖p.S (st.previous.x - p.center.x)‖ ≤ A
  accepted_radius : ‖p.S (st.accepted.x - p.center.x)‖ ≤ A
  previous_distance : ‖st.previous.x - p.center.x‖ ≤ τ
  accepted_distance : ‖st.accepted.x - p.center.x‖ ≤ τ
  center_radius : ‖st.z - p.S p.center.x‖ ≤ A
  momentum : p.S st.accepted.x = (1 - p.a) • p.S st.previous.x + p.a • st.z
  history_geometry : ∀ plane ∈ st.history, PlaneGeometry p f A τ plane
  history_support : ∀ plane ∈ st.history, supports p p.center plane.point
  history_length : st.history.length = k
  representation : ∃ φ : ℝ, value p st.accepted ≤ φ ∧
    ∀ u, estimate p st.history u = φ + p.μ / 2 * ‖p.S u.x - st.z‖ ^ 2
  gradient_large : 0 < k → p.ε < ‖st.accepted.gradient‖

lemma initial_invariant (p : Parameters E) (f : E → ℝ) {A τ : ℝ}
    (hc : Faithful f p.center) (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hq : 0 ≤ p.q) :
    Invariant p f A τ 0 ⟨p.center, p.center, p.S p.center.x, []⟩ := by
  have hv : value p p.center = p.center.value := by simp [value, regularizedValue]
  refine ⟨hc, hc, hv.le, hv.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · linarith
  · linarith
  · simpa using hA
  · simpa using hA
  · simpa using hτ
  · simpa using hτ
  · simpa using hA
  · module
  · simp
  · simp
  · exact ⟨p.center.value, hv.le, initial_representation p⟩
  · omega

lemma query_plane_geometry (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (y : Point E)
    (hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z) (hfaithful : Faithful f y) :
    PlaneGeometry p f A τ ⟨y, st.previous, st.accepted⟩ := by
  refine ⟨hfaithful, hi.previous_faithful, hi.accepted_faithful, hi.previous_value,
    hi.accepted_value, hi.previous_gap, hi.accepted_gap, hi.previous_radius,
    hi.accepted_radius, ?_, hi.previous_distance, hi.accepted_distance, ?_⟩
  · rw [map_sub, hy]
    exact GuardedAcceleratedGeometry.extrapolate_radius ha _ _ _
      (by simpa only [map_sub] using hi.accepted_radius) hi.center_radius
  · apply p.S.injective
    rw [hy, map_add, map_smul, map_sub]
    exact GuardedAcceleratedGeometry.momentum_relation (by positivity) _ _ _ hi.momentum

lemma plane_distance (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {plane : Plane E}
    (hi : PlaneGeometry p f A τ plane) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1) :
    ‖plane.point.x - p.center.x‖ ≤ 3 * τ := by
  have hp : 0 < 1 + p.a := by positivity
  have hθ : 0 ≤ (1 - p.a) / (1 + p.a) := div_nonneg (sub_nonneg.mpr ha₁) hp.le
  have hθ₁ : (1 - p.a) / (1 + p.a) ≤ 1 := (div_le_one hp).mpr (by linarith)
  have hd : ‖plane.accepted.x - plane.previous.x‖ ≤ 2 * τ := by
    calc
      _ = ‖(plane.accepted.x - p.center.x) - (plane.previous.x - p.center.x)‖ := by congr 1; abel
      _ ≤ ‖plane.accepted.x - p.center.x‖ + ‖plane.previous.x - p.center.x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hi.accepted_distance, hi.previous_distance]
  rw [hi.extrapolation]
  have he : plane.accepted.x + ((1 - p.a) / (1 + p.a)) •
      (plane.accepted.x - plane.previous.x) - p.center.x =
      (plane.accepted.x - p.center.x) + ((1 - p.a) / (1 + p.a)) •
      (plane.accepted.x - plane.previous.x) := by abel
  rw [he]
  calc
    _ ≤ ‖plane.accepted.x - p.center.x‖ +
      ‖((1 - p.a) / (1 + p.a)) • (plane.accepted.x - plane.previous.x)‖ := norm_add_le _ _
    _ = ‖plane.accepted.x - p.center.x‖ +
      ((1 - p.a) / (1 + p.a)) * ‖plane.accepted.x - plane.previous.x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    _ ≤ ‖plane.accepted.x - p.center.x‖ + 1 * ‖plane.accepted.x - plane.previous.x‖ := by gcongr
    _ ≤ _ := by linarith [hi.accepted_distance]

lemma continuing_invariant (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hα : 0 < p.α)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hA₂ : A ^ 2 = 2 * p.q / p.μ) (hτ₂ : p.α * τ ^ 2 = p.q)
    (htune : p.a ^ 2 * p.L = p.μ) (y next : Point E)
    (hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z)
    (hyfaith : Faithful f y) (hnfaith : Faithful f next)
    (hcenter : supports p p.center y) (hsupport : supports p st.accepted y)
    (hdescent : value p next ≤ value p y - ‖transformedGradient p.S (gradient p y)‖ ^ 2 / (2 * p.L))
    (hfull : p.S next.x = gradientStep p.L (p.S y.x) (transformedGradient p.S (gradient p y)))
    (hnosuccess : ¬successful p next) :
    Invariant p f A τ (k + 1) ⟨st.accepted, next,
      centerStep p.a p.μ (p.S y.x) st.z (transformedGradient p.S (gradient p y)),
      ⟨y, st.previous, st.accepted⟩ :: st.history⟩ := by
  let plane : Plane E := ⟨y, st.previous, st.accepted⟩
  let zn := centerStep p.a p.μ (p.S y.x) st.z (transformedGradient p.S (gradient p y))
  obtain ⟨φ, hmin, hrep⟩ := hi.representation
  let φn := GuardedAcceleratedGeometry.minimumUpdate p.a p.μ φ (value p y)
    (p.S y.x) st.z (transformedGradient p.S (gradient p y))
  have hminn : value p next ≤ φn := accepted_minimum_step p st.accepted y next st.z
    ha ha₁ hμ hL htune hy hmin hsupport hdescent
  have hrepn (u : Point E) : estimate p (plane :: st.history) u = φn + p.μ / 2 * ‖p.S u.x - zn‖ ^ 2 :=
    updated_representation p st.history plane hμ.ne' hrep u
  have hhistory : ∀ pl ∈ plane :: st.history, supports p p.center pl.point := by
    intro pl hp
    rcases List.mem_cons.mp hp with h | h
    · subst pl
      exact hcenter
    · exact hi.history_support pl h
  have hc := estimate_center p (plane :: st.history) ha ha₁ hhistory
  have hvalue : value p next ≤ p.center.value := by
    rw [hrepn] at hc
    have hp : 0 ≤ p.μ / 2 * ‖p.S p.center.x - zn‖ ^ 2 := by positivity
    linarith
  have hgap : p.center.value - p.q ≤ next.value := by
    unfold successful at hnosuccess
    exact (lt_of_not_ge (not_or.mp hnosuccess).1).le
  have hgradient : p.ε < ‖next.gradient‖ := lt_of_not_ge (not_or.mp hnosuccess).2
  have hzn : ‖zn - p.S p.center.x‖ ≤ A := by
    have hh := estimate_displacement p (plane :: st.history) hμ hc (hrepn p.center) hminn hgap hα.le
    rw [← hA₂, norm_sub_rev] at hh
    exact (sq_le_sq₀ (norm_nonneg _) hA).mp hh
  have hrelation : p.S next.x = (1 - p.a) • p.S st.accepted.x + p.a • zn := by
    rw [hfull, hy]
    simpa only [zn, hy] using GuardedAcceleratedGeometry.primal_center_relation
      (by positivity : 1 + p.a ≠ 0) hμ.ne' hL.ne' htune (p.S st.accepted.x) st.z
        (transformedGradient p.S (gradient p y))
  have hradius : ‖p.S (next.x - p.center.x)‖ ≤ A := by
    rw [map_sub, hrelation]
    exact GuardedAcceleratedGeometry.convex_radius ha ha₁ _ _ _
      (by simpa only [map_sub] using hi.accepted_radius) hzn
  have hdistance : ‖next.x - p.center.x‖ ≤ τ := by
    have hh := GuardedMetricDescent.regularized_distance p.center.x next.x hvalue hgap
    rw [← hτ₂] at hh
    have hh' := (mul_le_mul_iff_right₀ hα).mp hh
    exact (sq_le_sq₀ (norm_nonneg _) hτ).mp hh'
  refine ⟨hi.accepted_faithful, hnfaith, hi.accepted_value, hvalue, hi.accepted_gap, hgap,
    hi.accepted_radius, hradius, hi.accepted_distance, hdistance, hzn, hrelation, ?_, hhistory,
    ?_, ⟨φn, hminn, hrepn⟩, fun _ => hgradient⟩
  · intro pl hp
    rcases List.mem_cons.mp hp with h | h
    · subst pl
      exact query_plane_geometry p f hi ha y hy hyfaith
    · exact hi.history_geometry pl h
  · simp only [List.length_cons, hi.history_length]

end LongTails.Proofs.QuarticStageInvariant
