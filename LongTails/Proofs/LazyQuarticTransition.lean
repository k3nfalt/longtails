import LongTails.Proofs.LazyQuarticStage
import LongTails.Proofs.LazyQuarticExecution

namespace LongTails.Proofs.LazyQuarticTransition

open OracleTemplate.QueryPlan
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Algorithms.QuarticMetricStage (Reply)
open LongTails.Proofs.QuarticStageInvariant (Faithful)
open LongTails.Proofs.LazyQuarticCurvature
open LongTails.Proofs.LazyQuarticExecution

structure Data (p : Params) (f : p.E → ℝ) : Prop where
  valid : spec.valid p
  smooth : ContDiff ℝ 3 f
  third : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
    fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ p.L₃ * ‖x - y‖
  gap : ∀ x, f p.x0 - f x ≤ p.Δ
  initial_hessian : ‖fderiv ℝ (_root_.gradient f) p.x0‖ ≤ p.H₀

structure SnapshotValid (p : Params) (f : p.E → ℝ) (st : State p) : Prop where
  value : f st.snapshot ≤ f p.x0
  coordinates : st.coordinates = coordinates p (fderiv ℝ (_root_.gradient f) st.snapshot)
  path : ‖st.snapshot - p.x0‖ ^ 2 ≤ pathCap p

lemma refresh_valid (p : Params) (f : p.E → ℝ) (g : Fin 2 × p.E → Reply p.E)
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hs : SnapshotValid p f st)
    (hv : f st.point.x ≤ f p.x0) (hx : ‖st.point.x - p.x0‖ ^ 2 ≤ pathCap p) :
    SnapshotValid p f ((refresh p st).eval g) := by
  classical
  unfold refresh
  split
  · simp only [eval, hH, readHessian]
    exact ⟨hv, rfl, hx⟩
  · exact hs

lemma refresh_guard (p : Params) (hp : spec.valid p) (_f : p.E → ℝ)
    (g : Fin 2 × p.E → Reply p.E) (st : State p)
    (ha : p.ε < ‖st.point.gradient‖) :
    ‖((refresh p st).eval g).coordinates
      (((refresh p st).eval g).point.x - ((refresh p st).eval g).snapshot)‖ ≤ radius p / 4 := by
  classical
  unfold refresh
  split
  · simp only [eval, sub_self, map_zero, norm_zero]
    exact div_nonneg (LazyQuarticParameters.radius_pos p hp).le (by norm_num)
  · rename_i hn
    simpa only [eval] using le_of_not_gt (fun hh => hn ⟨ha, hh⟩)

lemma step_correct (p : Params) (f : p.E → ℝ) (h : Data p f)
    (g : Fin 2 × p.E → Reply p.E)
    (hg : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hc : Faithful f st.point) (hs : SnapshotValid p f st)
    (hv : f st.point.x ≤ f p.x0) (hx : ‖st.point.x - p.x0‖ ^ 2 ≤ pathCap p)
    (ha : p.ε < ‖st.point.gradient‖) :
    Faithful f ((step p st).eval g).point ∧ SnapshotValid p f ((step p st).eval g) ∧
    (p.ε < ‖((step p st).eval g).point.gradient‖ →
      ((step p st).eval g).point.value ≤ st.point.value - decrease p ∧
      (parameters p ((refresh p st).eval g)).μ *
        ‖((refresh p st).eval g).coordinates (((step p st).eval g).point.x - st.point.x)‖ ^ 2 ≤
        256 * (st.point.value - ((step p st).eval g).point.value)) := by
  classical
  let fresh := (refresh p st).eval g
  have hf : fresh.point = st.point := refresh_point p g st
  have hs' : SnapshotValid p f fresh := refresh_valid p f g hH st hs hv hx
  have hp := LazyQuarticStage.hypotheses p h.valid f h.smooth h.third h.gap h.initial_hessian
    fresh (hf ▸ hc) (by simpa only [hf] using hv) hs'.value hs'.coordinates
    (refresh_guard p h.valid f g st ha) hs'.path
  have hh := QuarticStageGuarantee.plan_correct (parameters p fresh) f g hg (innerSteps p) hp
  have he : (step p st).eval g =
      { fresh with point := (LongTails.Algorithms.QuarticMetricStage.plan
          (parameters p fresh) (innerSteps p)).eval g } := by
    simp only [step, eval_bind]
    rw [ite_eq_left (by simpa only [refresh_point] using ha), eval_map]
  rw [he]
  refine ⟨hh.1, ⟨hs'.value, hs'.coordinates, hs'.path⟩, ?_⟩
  intro hn
  have hv' := hh.2.1.resolve_right (not_le.mpr hn)
  have he' := hh.2.2.resolve_left (not_le.mpr hn)
  simpa only [parameters, hf, fresh] using And.intro hv' he'

lemma euclidean_energy (p : Params) (f : p.E → ℝ) (h : Data p f)
    (st : State p) (hs : SnapshotValid p f st) (v : p.E) (D : ℝ)
    (he : (parameters p st).μ * ‖st.coordinates v‖ ^ 2 ≤ 256 * D) :
    alpha p * ‖v‖ ^ 2 ≤ 16384 * D := by
  have hg (y : p.E) : f st.snapshot - f y ≤ p.Δ := by linarith [h.gap y, hs.value]
  have hl := LazyQuarticSnapshot.coordinates_lower p h.valid f h.smooth h.third st.snapshot hg v
  rw [← hs.coordinates] at hl
  have hm := LazyQuarticStageParameters.basic_scales p h.valid st
  have hh := mul_le_mul_of_nonneg_left hl hm.1.le
  have hid := hm.2.2.2.2.2
  nlinarith only [hh, hid, he]

end LongTails.Proofs.LazyQuarticTransition
