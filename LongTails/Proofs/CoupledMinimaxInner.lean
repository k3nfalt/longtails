import LongTails.Proofs.CoupledMinimaxTuning
import LongTails.Proofs.ConstrainedSaddleInner
import LongTails.Proofs.CoupledMinimaxDescent

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxInner

open OracleTemplate
open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry
open LongTails.Proofs.CoupledMinimaxTuning
open LongTails.Proofs.CoupledMinimaxAcceleration

lemma projectY_spec {p : Params} (hv : Valid p) (v : YSpace p) :
    SaddlePoint.project p.Y v ∈ p.Y ∧
      ∀ u ∈ p.Y, ⟪v - SaddlePoint.project p.Y v, u - SaddlePoint.project p.Y v⟫ ≤ 0 :=
  ConstrainedSaddleInner.closed_project_spec ⟨p.y0, hv.startY⟩
    hv.compactY.isClosed hv.convexY v

lemma restarted_accuracy {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {u : YSpace p} (hu : u ∈ p.Y) (hm : IsMinOn (innerObjective I q) p.Y u) :
    let y := QueryPlan.eval (innerGradient I q)
      (Algorithms.CoupledMinimaxInner.restart id id (SaddlePoint.project p.Y)
        (smoothness p) (innerIterations p) (innerRestarts p) p.y0)
    y ∈ p.Y ∧ ‖y - u‖ ≤ tolerance p / (12 * smoothness p) := by
  have hh := restart_bound hv.convexY (fun v => (projectY_spec hv v).1)
    (fun v => (projectY_spec hv v).2) (smoothness_pos hv)
    (fun y hy v hv' => inner_support hv H hq hy hv')
    (fun y hy v hv' => inner_smooth_upper hv H hq hy hv') hv.startY hu
    (fun v hv' => inner_minimizer_growth hv H hq hu hm hv')
    (innerIterations p) (inner_weight hv) (innerRestarts p)
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (hv.diameterY p.y0 hv.startY u hu)
    (by positivity)).trans (restart_accuracy hv)

lemma mapped_accuracy {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {u : YSpace p} (hu : u ∈ p.Y) (hm : IsMinOn (innerObjective I q) p.Y u) :
    let y := QueryPlan.eval (exactReply p I)
      (Algorithms.CoupledMinimaxInner.restart (query p q)
        (fun r => -(lagrangianGradient p r q.snd).snd) (SaddlePoint.project p.Y)
        (smoothness p) (innerIterations p) (innerRestarts p) p.y0)
    y ∈ p.Y ∧ ‖y - u‖ ≤ tolerance p / (12 * smoothness p) := by
  dsimp only
  rw [restart_eval_map]
  exact restarted_accuracy hv H hq hu hm

lemma projectMin_spec {p : Params} (hv : Valid p) (v : MinSpace p) :
    SaddlePoint.project (minDomain p) v ∈ minDomain p ∧
      ∀ u ∈ minDomain p, ⟪v - SaddlePoint.project (minDomain p) v,
        u - SaddlePoint.project (minDomain p) v⟫ ≤ 0 :=
  ConstrainedSaddleInner.closed_project_spec ⟨start p, start_mem hv⟩
    (minDomain_closed hv) (minDomain_convex hv) v

lemma step_supported {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    FeasibleGapExecution.Supported (exactReply p I) (fun z => z ∈ domain p) (step p q) := by
  unfold step
  apply FeasibleGapExecution.supported_bind
  · exact restart_supported hv.convexY (fun v => (projectY_spec hv v).1)
      (smoothness_pos hv) _ _ _ _ (fun y hy => ⟨hq.1, hy⟩) _ _ hv.startY
  · obtain ⟨u, hu, hm⟩ := inner_attain hv H hq
    have hy := (mapped_accuracy hv H hq hu hm).1
    refine ⟨⟨hq.1, hy⟩, ?_⟩
    exact ⟨⟨hq.1, (projectY_spec hv _).1⟩, trivial⟩

lemma step_min_mem {p : Params} {I : Instance p} (hv : Valid p) (q : MinSpace p) :
    (QueryPlan.eval (exactReply p I) (step p q)).1 ∈ minDomain p := by
  unfold step stepCalls
  rw [QueryPlan.eval_bind]
  simp only [QueryPlan.eval]
  exact (projectMin_spec hv _).1

lemma supported_map {Q R U V : Type*} (g : Q → R) (allowed : Q → Prop)
    (f : U → V) {k : ℕ} (plan : QueryPlan Q R U k)
    (hp : FeasibleGapExecution.Supported g allowed plan) :
    FeasibleGapExecution.Supported g allowed (plan.map f) := by
  induction plan with
  | done value => trivial
  | ask q next ih => exact ⟨hp.1, ih (g q) hp.2⟩

lemma outer_supported {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) (N : ℕ) {q : MinSpace p} (hq : q ∈ minDomain p) :
    FeasibleGapExecution.Supported (exactReply p I) (fun z => z ∈ domain p) (outer p N q) := by
  induction N generalizing q with
  | zero => trivial
  | succ N ih =>
      apply FeasibleGapExecution.supported_bind
      · exact step_supported hv H hq
      · have hh := ih (step_min_mem (I := I) hv q)
        exact supported_map _ _ _ _ hh


lemma execute_eq {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) (O : Oracle (Joint p) (Reply p))
    (hans : ∀ history seed z, z ∈ domain p → O.answer history (0, z) seed = exactReply p I z)
    {K : ℕ} (hK : calls p ≤ K) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) () ξ =
      select p (QueryPlan.eval (exactReply p I) (outer p (outerIterations p) (start p))) := by
  have hp := supported_map (exactReply p I) (fun z => z ∈ domain p) (select p)
    (outer p (outerIterations p) (start p))
    (outer_supported hv H (outerIterations p) (start_mem hv))
  have hh := FeasibleGapExecution.execute_supported O (exactReply p I)
    (fun z => z ∈ domain p) (fun history z seed hz => hans history seed z hz)
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    (query p (start p) p.y0) (⟨p.x0, p.y0, 0⟩ : Output p)
    (calls p) K (fun _ : Unit => (outer p (outerIterations p) (start p)).map (select p))
    () hp hK ξ
  unfold calls at hh
  rw [QueryPlan.eval_map] at hh
  exact hh

lemma cleanup_distance {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {u y : YSpace p} (hu : u ∈ p.Y) (hy : y ∈ p.Y)
    (hm : IsMinOn (innerObjective I q) p.Y u) :
    ‖SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y) - u‖ ≤ ‖y - u‖ := by
  let L := smoothness p
  let g := innerGradient I q y
  let b := SaddlePoint.project p.Y (y - (1 / L) • g)
  have hL : 0 < L := smoothness_pos hv
  have hb := projectY_spec hv (y - (1 / L) • g)
  have hp := hb.2 u hu
  have hproj : 0 ≤ ⟪g + L • (b - y), u - b⟫ := by
    have he : g + L • (b - y) = -L • (y - (1 / L) • g - b) := by
      simp only [smul_sub, smul_smul, one_div, neg_mul, mul_inv_cancel₀ hL.ne', neg_smul]
      module
    rw [he, real_inner_smul_left]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hp
  have hupper := inner_smooth_upper hv H hq hy hb.1
  have hlower := inner_strong_model hv H hq hy hu
  have hmin : innerObjective I q u ≤ innerObjective I q b := hm hb.1
  have hh := CoupledMinimaxDescent.inner_contraction hL hupper hlower hmin hproj
  have hcoeff : 1 - p.μ / L ≤ 1 := by
    have hh : 0 ≤ p.μ / L := div_nonneg hv.μ_pos.le hL.le
    linarith
  have hs := hh.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖y - u‖))
  simp only [one_mul] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

lemma cleanup_residual {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y) :
    let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
    ∃ n, Normal p.Y b n ∧ ‖innerGradient I q b + n‖ ≤ 2 * smoothness p * ‖b - y‖ := by
  let L := smoothness p
  let g := innerGradient I q y
  let b := SaddlePoint.project p.Y (y - (1 / L) • g)
  have hL : 0 < L := smoothness_pos hv
  have hb := projectY_spec hv (y - (1 / L) • g)
  have he : L • (y - (1 / L) • g - b) = L • (y - b) - g := by
    simp only [smul_sub, smul_smul, one_div, mul_inv_cancel₀ hL.ne', one_smul]
    abel
  refine ⟨L • (y - b) - g, ?_, ?_⟩
  · intro v hv'
    rw [← he, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos hL.le (hb.2 v hv')
  · have hh := inner_gradient_lipschitz hv H hq hb.1 hy
    have hid : innerGradient I q b + (L • (y - b) - g) =
        (innerGradient I q b - g) + L • (y - b) := by abel
    rw [hid]
    have hn := norm_add_le (innerGradient I q b - g) (L • (y - b))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_sub_rev y b] at hn
    change ‖innerGradient I q b - g‖ ≤ L * ‖b - y‖ at hh
    change _ ≤ 2 * L * ‖b - y‖
    linarith

end LongTails.Proofs.CoupledMinimaxInner
