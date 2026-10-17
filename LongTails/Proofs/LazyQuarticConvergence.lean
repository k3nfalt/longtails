import LongTails.Proofs.LazyQuarticTrace

namespace LongTails.Proofs.LazyQuarticConvergence

open OracleTemplate.QueryPlan
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Algorithms.QuarticMetricStage (Reply)
open LongTails.Proofs.LazyQuarticExecution
open LongTails.Proofs.LazyQuarticTransition

noncomputable def replies (p : Params) (f : p.E → ℝ) (q : Fin 2 × p.E) : Reply p.E :=
  if q.1 = 0 then .inl (f q.2, _root_.gradient f q.2) else .inr (fderiv ℝ (_root_.gradient f) q.2)

noncomputable def initial (p : Params) (f : p.E → ℝ) : State p :=
  ⟨⟨p.x0, f p.x0, _root_.gradient f p.x0⟩, p.x0, coordinates p (fderiv ℝ (_root_.gradient f) p.x0)⟩

lemma replies_gradient (p : Params) (f : p.E → ℝ) (x : p.E) :
    replies p f (0, x) = .inl (f x, _root_.gradient f x) := by simp [replies]

lemma replies_hessian (p : Params) (f : p.E → ℝ) (x : p.E) :
    replies p f (1, x) = .inr (fderiv ℝ (_root_.gradient f) x) := by simp [replies]

lemma initial_faithful (p : Params) (f : p.E → ℝ) :
    QuarticStageInvariant.Faithful f (initial p f).point := ⟨rfl, rfl⟩

lemma initial_snapshot (p : Params) (f : p.E → ℝ) (hp : spec.valid p) :
    SnapshotValid p f (initial p f) := by
  refine ⟨le_rfl, rfl, ?_⟩
  change ‖p.x0 - p.x0‖ ^ 2 ≤ LazyQuarticCurvature.pathCap p
  rw [sub_self, norm_zero, zero_pow (by decide)]
  have hΔ := hp.2.1
  have hε := hp.2.2.2
  have hb := LazyQuarticParameters.beta_pos p hp
  unfold LazyQuarticCurvature.pathCap
  positivity

lemma plan_eval (p : Params) (f : p.E → ℝ) :
    (plan p).eval (replies p f) = (states p (replies p f) (initial p f) (stages p)).point.x := by
  simp only [plan, eval, replies_gradient, replies_hessian,
    LongTails.Algorithms.QuarticMetricStage.readPoint, readHessian, eval_map, loop_eval]
  rfl

lemma plan_accuracy (p : Params) (f : p.E → ℝ) (h : Data p f) :
    ‖_root_.gradient f ((plan p).eval (replies p f))‖ ≤ p.ε := by
  rw [plan_eval]
  exact LazyQuarticTrace.trace_terminates p f h (replies p f) (replies_gradient p f)
    (replies_hessian p f) (initial p f) (initial_faithful p f) (initial_snapshot p f h.valid) rfl

end LongTails.Proofs.LazyQuarticConvergence
