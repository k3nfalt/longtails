import LongTails.Proofs.QuarticStageModels

namespace LongTails.Proofs.QuarticStageTransition

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure WitnessInvariant (p : Parameters E) (f : E → ℝ) (A τ : ℝ) (w : Witness E) : Prop where
  plane_geometry : PlaneGeometry p f A τ w.plane
  point_faithful : Faithful f w.point
  point_value : value p w.point ≤ p.center.value
  point_gap : p.center.value - p.q ≤ w.point.value
  point_radius : ‖p.S (w.point.x - p.center.x)‖ ≤ 2 * A
  point_distance : ‖w.point.x - p.center.x‖ ≤ τ
  failure : ¬supports p w.point w.plane.point

def StatusInvariant (p : Parameters E) (f : E → ℝ) (A τ : ℝ) (k : ℕ) : Status E → Prop
  | .running st => Invariant p f A τ k st
  | .finished x => Faithful f x ∧ successful p x
  | .witness w => WitnessInvariant p f A τ w

lemma center_witness (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {plane : Plane E}
    (hc : Faithful f p.center) (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hq : 0 ≤ p.q)
    (hp : PlaneGeometry p f A τ plane) (hs : ¬supports p p.center plane.point) :
    WitnessInvariant p f A τ ⟨p.center, plane⟩ := by
  refine ⟨hp, hc, ?_, ?_, ?_, ?_, hs⟩
  · simp [value, regularizedValue]
  · linarith
  · simpa using (by linarith : 0 ≤ 2 * A)
  · simpa using hτ

lemma accepted_witness (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {plane : Plane E}
    (hA : 0 ≤ A) (hp : PlaneGeometry p f A τ plane)
    (hs : ¬supports p plane.accepted plane.point) :
    WitnessInvariant p f A τ ⟨plane.accepted, plane⟩ :=
  ⟨hp, hp.accepted_faithful, hp.accepted_value, hp.accepted_gap,
    hp.accepted_radius.trans (by linarith), hp.accepted_distance, hs⟩

lemma step_invariant (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    {A τ : ℝ} {k : ℕ} (status : Status E) (hi : StatusInvariant p f A τ k status)
    (hc : Faithful f p.center) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hα : 0 < p.α) (hr : 0 < p.r)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hq₀ : 0 ≤ p.q)
    (hA₂ : A ^ 2 = 2 * p.q / p.μ) (hτ₂ : p.α * τ ^ 2 = p.q)
    (hAr : A ≤ p.r / 8) (hq : p.q ≤ p.L * p.r ^ 2 / 16)
    (htune : p.a ^ 2 * p.L = p.μ)
    (hmodel : ∀ y next : Point E, Faithful f y → Faithful f next →
      ‖p.S (y.x - p.center.x)‖ ≤ A → next.x = trialPoint p y →
      value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
        p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2) :
    StatusInvariant p f A τ (k + 1) ((step p status).eval g) := by
  classical
  cases status with
  | finished x => simpa [step, stopAfter, eval, StatusInvariant] using hi
  | witness w => simpa [step, stopAfter, eval, StatusInvariant] using hi
  | running st =>
    let yx := p.S.symm (extrapolate p.a (p.S st.accepted.x) st.z)
    let y : Point E := ⟨yx, f yx, _root_.gradient f yx⟩
    let next : Point E := ⟨trialPoint p y, f (trialPoint p y), _root_.gradient f (trialPoint p y)⟩
    have hyfaith : Faithful f y := ⟨rfl, rfl⟩
    have hnfaith : Faithful f next := ⟨rfl, rfl⟩
    have hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z := by simp [y, yx]
    have hp := query_plane_geometry p f hi ha y hy hyfaith
    change Invariant p f A τ k st at hi
    simp only [step, eval, horacle, readPoint]
    split
    · rename_i hs
      exact ⟨hyfaith, hs⟩
    · rename_i hs
      split
      · rename_i hc'
        exact center_witness p f hc hA hτ hq₀ hp hc'
      · rename_i hc'
        split
        · rename_i hx'
          exact accepted_witness p f hA hp hx'
        · rename_i hx'
          simp only [eval, horacle]
          split
          · rename_i hn
            exact ⟨hnfaith, hn⟩
          · rename_i hn
            exact QuarticStageModels.modeled_continuation p f hi ha ha₁ hμ hL hα hr hA hτ
              hA₂ hτ₂ hAr hq htune y next hy hyfaith hnfaith (not_not.mp hc') (not_not.mp hx')
              rfl (hmodel y next hyfaith hnfaith hp.point_radius rfl) hn

lemma loop_invariant (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    {A τ : ℝ}
    (hstep : ∀ k status, StatusInvariant p f A τ k status →
      StatusInvariant p f A τ (k + 1) ((step p status).eval g))
    (n k : ℕ) (status : Status E) (hi : StatusInvariant p f A τ k status) :
    StatusInvariant p f A τ (k + n) ((loop p n status).eval g) := by
  induction n generalizing k status with
  | zero => simpa [loop, eval] using hi
  | succ n ih =>
    simp only [loop, id_eq, eval_bind]
    have hh := ih (k + 1) ((step p status).eval g) (hstep k status hi)
    convert hh using 1
    omega

end LongTails.Proofs.QuarticStageTransition
