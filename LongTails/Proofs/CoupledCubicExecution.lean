import LongTails.Algorithms.CoupledCubicTournament
import LongTails.Proofs.PLMinimaxCubicDescent

namespace LongTails.Proofs.CoupledCubicExecution

open OracleTemplate MeasureTheory
open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament
open scoped RealInnerProductSpace

lemma modelStep_min (p : Params) (hρ : 0 < p.ρ) (m : Model p) (u : p.E) :
    CappedCubicModel.model m.2 m.1 0 (p.ρ / 2) (modelStep p m) ≤
      CappedCubicModel.model m.2 m.1 0 (p.ρ / 2) u := by
  simpa [modelStep, CappedCubicModel.model, PLMinimax.envelopeCubicModel] using
    PLMinimax.envelopeCubicStep_min m.1 m.2 (show 0 < p.ρ / 2 by positivity) u

lemma modelStep_zero (p : Params) (hρ : 0 < p.ρ) (m : Model p) (hg : m.1 = 0)
    (hm : ∀ v : p.E, 0 ≤ ⟪v, m.2 v⟫) : modelStep p m = 0 := by
  have hmin := modelStep_min p hρ m 0
  have hquad := hm (modelStep p m)
  simp only [CappedCubicModel.model, hg, inner_zero_left, map_zero, inner_zero_right,
    norm_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_mul, add_zero, zero_add] at hmin
  apply norm_eq_zero.mp
  by_contra hn
  have hp : 0 < ‖modelStep p m‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have hc := mul_pos hρ (pow_pos hp 3)
  nlinarith

lemma selectedIndex_spec (p : Params) (models : List (Model p))
    (h : ∃ j, j < models.length ∧ qualifies p models j) :
    selectedIndex p models < models.length ∧ qualifies p models (selectedIndex p models) := by
  classical
  simp only [selectedIndex, dite_eq_left h]
  exact Nat.find_spec h

lemma compatible_symm (p : Params) (a b : Model p) (h : compatible p a b) :
    compatible p b a := ⟨h.2, h.1⟩

lemma modelStep_stationary (p : Params) (hρ : 0 < p.ρ) (m : Model p)
    (hm : ∀ x y : p.E, ⟪x, m.2 y⟫ = ⟪m.2 x, y⟫) :
    m.1 + m.2 (modelStep p m) + (p.ρ / 2 * ‖modelStep p m‖) • modelStep p m = 0 :=
  PLMinimax.envelopeCubicStep_stationary m.1 m.2 (show 0 < p.ρ / 2 by positivity) hm

lemma modelStep_psd (p : Params) (hρ : 0 < p.ρ) (m : Model p)
    (hm : ∀ x y : p.E, ⟪x, m.2 y⟫ = ⟪m.2 x, y⟫) (v : p.E) :
    0 ≤ ⟪v, m.2 v + (p.ρ / 2 * ‖modelStep p m‖) • v⟫ :=
  PLMinimax.envelopeCubicStep_psd m.1 m.2 (show 0 < p.ρ / 2 by positivity) hm v

lemma execute_method (p : Params) (b K T B : ℕ) (hB : ((1 * b) * K) * T ≤ B)
    (g : Fin p.n × p.E → Model p) (O : Oracle (Fin p.n × p.E) (Model p))
    (hO : ∀ history q seed, O.answer history (0, q) seed = g q)
    (ξ : Seeds p b K T) (ω : (k : ℕ) → O.Seed k) :
    execute O (method p b K T) (fun _ => B) ξ ω = output p b K T g ξ := by
  erw [execute_eq_of_answer_eq O g hO]
  unfold method output
  exact QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hB

lemma execute_event_measurable (p : Params) (b K T B : ℕ)
    (hB : ((1 * b) * K) * T ≤ B) (g : Fin p.n × p.E → Model p)
    (O : Oracle (Fin p.n × p.E) (Model p))
    (hO : ∀ history q seed, O.answer history (0, q) seed = g q) (ψ : p.E → Prop) :
    MeasurableSet {seed : Seeds p b K T × ((k : ℕ) → O.Seed k) |
      ψ (execute O (method p b K T) (fun _ => B) seed.1 seed.2)} := by
  have he : {seed : Seeds p b K T × ((k : ℕ) → O.Seed k) |
      ψ (execute O (method p b K T) (fun _ => B) seed.1 seed.2)} =
      Prod.fst ⁻¹' {ξ : Seeds p b K T | ψ (output p b K T g ξ)} := by
    ext seed
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [execute_method p b K T B hB g O hO]
  rw [he]
  exact measurable_fst (Set.toFinite _).measurableSet


lemma eval_batchPlan (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin b → Fin p.n) :
    QueryPlan.eval g (batchPlan p b x ξ) = sampledModel p b g x ξ := by
  simp only [batchPlan, QueryPlan.eval_map, QueryPlan.eval_traverse, QueryPlan.eval,
    List.sum_ofFn, sampledModel]

lemma eval_roundPlan (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin K → Fin b → Fin p.n) :
    QueryPlan.eval g (roundPlan p b K x ξ) = sampledModels p b K g x ξ := by
  simp only [roundPlan, QueryPlan.eval_traverse, eval_batchPlan, sampledModels]

lemma eval_allPlan (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (T : ℕ) (state : p.E × Bool) (ξ : Seeds p b K T) :
    QueryPlan.eval g (allPlan p b K T state ξ) = (runState p b K g T state ξ).1 := by
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
    simp only [allPlan, QueryPlan.eval_bind, eval_roundPlan, runState]
    exact ih _ _

lemma output_eq_runState (p : Params) (b K T : ℕ) (g : Fin p.n × p.E → Model p)
    (ξ : Seeds p b K T) : output p b K T g ξ = (runState p b K g T (p.x0, false) ξ).1 :=
  eval_allPlan p b K g T (p.x0, false) ξ

lemma runState_stopped (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (T : ℕ) (state : p.E × Bool) (hstop : state.2 = true) (ξ : Seeds p b K T) :
    runState p b K g T state ξ = state := by
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
    simp only [runState, nextState, hstop, ite_true]
    exact ih state hstop (fun i => ξ i.succ)


lemma sampledModel_gradient (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin b → Fin p.n) :
    (sampledModel p b g x ξ).1 = (b : ℝ)⁻¹ • ∑ i, (g (ξ i, x)).1 := by
  simp [sampledModel, Prod.fst_sum]

lemma sampledModel_hessian_apply (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x v : p.E) (ξ : Fin b → Fin p.n) :
    (sampledModel p b g x ξ).2 v = (b : ℝ)⁻¹ • ∑ i, (g (ξ i, x)).2 v := by
  simp [sampledModel, Prod.snd_sum, sum_apply]

lemma sampledModel_coupled (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x s : p.E) (ξ : Fin b → Fin p.n) :
    (sampledModel p b g x ξ).1 + (sampledModel p b g x ξ).2 s =
      (b : ℝ)⁻¹ • ∑ i, ((g (ξ i, x)).1 + (g (ξ i, x)).2 s) := by
  rw [sampledModel_gradient, sampledModel_hessian_apply, Finset.sum_add_distrib, smul_add]

lemma sampledModel_coupled_error (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x s u : p.E) (H : p.E →L[ℝ] p.E) (ξ : Fin b → Fin p.n) :
    (sampledModel p b g x ξ).1 - u + ((sampledModel p b g x ξ).2 - H) s =
      (b : ℝ)⁻¹ • ∑ i, ((g (ξ i, x)).1 + (g (ξ i, x)).2 s) - (u + H s) := by
  rw [← sampledModel_coupled, sub_apply]
  abel

lemma sampledModel_symmetric (p : Params) (b : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin b → Fin p.n)
    (hsym : ∀ i, (g (i, x)).2.toLinearMap.IsSymmetric) :
    (sampledModel p b g x ξ).2.toLinearMap.IsSymmetric := by
  intro u v
  change ⟪(sampledModel p b g x ξ).2 u, v⟫ = ⟪u, (sampledModel p b g x ξ).2 v⟫
  simp only [sampledModel_hessian_apply, real_inner_smul_left, inner_smul_right,
    sum_inner, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hsym (ξ i) u v

lemma modelAt_sampledModels (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin K → Fin b → Fin p.n) (j : Fin K) :
    modelAt p (sampledModels p b K g x ξ) j = sampledModel p b g x (ξ j) := by
  simp [modelAt, sampledModels, j.isLt]

lemma sampledModels_symmetric (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (x : p.E) (ξ : Fin K → Fin b → Fin p.n)
    (hsym : ∀ i, (g (i, x)).2.toLinearMap.IsSymmetric)
    (j : ℕ) (hj : j < (sampledModels p b K g x ξ).length) :
    (modelAt p (sampledModels p b K g x ξ) j).2.toLinearMap.IsSymmetric := by
  have hjK : j < K := by simpa [sampledModels] using hj
  have he := modelAt_sampledModels p b K g x ξ ⟨j, hjK⟩
  change modelAt p (sampledModels p b K g x ξ) j = _ at he
  rw [he]
  exact sampledModel_symmetric p b g x (ξ ⟨j, hjK⟩) hsym

end LongTails.Proofs.CoupledCubicExecution
