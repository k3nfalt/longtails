import LongTails.Proofs.LazyQuarticTrace
import LongTails.Proofs.QuarticRefreshLedger

namespace LongTails.Proofs.LazyQuarticLedger

open OracleTemplate.QueryPlan
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Algorithms.QuarticMetricStage (Reply)
open LongTails.Proofs.LazyQuarticExecution

noncomputable def ghost (p : Params) (s : ℕ → State p) : ℕ → p.E
  | 0 => (s 0).point.x
  | t + 1 => if p.ε < ‖(s (t + 1)).point.gradient‖ then (s (t + 1)).point.x else ghost p s t

noncomputable def potential (p : Params) (st : State p) : ℝ :=
  if p.ε < ‖st.point.gradient‖ then ‖st.coordinates (st.point.x - st.snapshot)‖ else 0

lemma ghost_active (p : Params) (s : ℕ → State p) (t : ℕ)
    (ha : p.ε < ‖(s t).point.gradient‖) : ghost p s t = (s t).point.x := by
  cases t with
  | zero => rfl
  | succ t => exact ite_eq_left ha

lemma active_previous (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ)
    (ha : p.ε < ‖(states p g st (t + 1)).point.gradient‖) :
    p.ε < ‖(states p g st t).point.gradient‖ := by
  by_contra hn
  rw [states_succ, step_inactive p g _ (le_of_not_gt hn)] at ha
  exact hn ha

lemma charge_sum (p : Params) (f : p.E → ℝ) (s : ℕ → State p)
    (hx0 : (s 0).point.x = p.x0) (hg : ∀ x, f p.x0 - f x ≤ p.Δ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (f (ghost p s t) - f (ghost p s (t + 1))) ≤ p.Δ := by
  have he : ∑ t ∈ Finset.range T, (f (ghost p s t) - f (ghost p s (t + 1))) =
      f (ghost p s 0) - f (ghost p s T) := by
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, ih]; ring
  rw [he]
  simpa only [ghost, hx0] using hg (ghost p s T)

lemma refresh_movement (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p)
    (ha : p.ε < ‖((step p st).eval g).point.gradient‖) :
    potential p ((step p st).eval g) ≤
      (if refreshNeeded p st then 0 else potential p st) +
      ‖((refresh p st).eval g).coordinates (((step p st).eval g).point.x - st.point.x)‖ := by
  classical
  have hprev : p.ε < ‖st.point.gradient‖ := by
    by_contra hn
    rw [step_inactive p g st (le_of_not_gt hn)] at ha
    exact hn ha
  rw [potential, ite_eq_left ha, step_coordinates, step_snapshot]
  have hh : ((step p st).eval g).point.x - ((refresh p st).eval g).snapshot =
      (((step p st).eval g).point.x - st.point.x) + (st.point.x - ((refresh p st).eval g).snapshot) := by abel
  rw [hh, map_add]
  have ht := norm_add_le (((refresh p st).eval g).coordinates (((step p st).eval g).point.x - st.point.x))
    (((refresh p st).eval g).coordinates (st.point.x - ((refresh p st).eval g).snapshot))
  have he : ‖((refresh p st).eval g).coordinates (st.point.x - ((refresh p st).eval g).snapshot)‖ =
      if refreshNeeded p st then 0 else potential p st := by
    unfold refresh refreshNeeded
    split <;> simp_all [eval, potential]
  rw [he] at ht
  linarith

noncomputable def chargeCoefficient (p : Params) : ℝ :=
  16 / Real.sqrt (alpha p / (64 * beta p) * decrease p)

lemma potential_nonneg (p : Params) (st : State p) : 0 ≤ potential p st := by
  unfold potential
  split <;> positivity

lemma reset_threshold (p : Params) (st : State p) (hr : refreshNeeded p st = true) :
    radius p / 4 < potential p st := by
  have hh : p.ε < ‖st.point.gradient‖ ∧ radius p / 4 < ‖st.coordinates (st.point.x - st.snapshot)‖ := by
    simpa only [refreshNeeded, decide_eq_true_eq] using hr
  simpa only [potential, ite_eq_left hh.1] using hh.2

lemma ledger_step (p : Params) (f : p.E → ℝ) (h : LazyQuarticTransition.Data p f)
    (g : Fin 2 × p.E → Reply p.E)
    (hg : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hc : QuarticStageInvariant.Faithful f st.point)
    (hs : LazyQuarticTransition.SnapshotValid p f st) (hx0 : st.point.x = p.x0)
    (t : ℕ) (ht : t < stages p) :
    (if refreshNeeded p (states p g st t) then radius p / 4 else 0) +
      potential p (states p g st (t + 1)) - potential p (states p g st t) ≤
      chargeCoefficient p * (f (ghost p (states p g st) t) - f (ghost p (states p g st) (t + 1))) := by
  classical
  by_cases hn : p.ε < ‖(states p g st (t + 1)).point.gradient‖
  · have ha := active_previous p g st t hn
    have hi := LazyQuarticTrace.trace_invariant p f h g hg hH st hc hs hx0 t (by omega)
    have hh := hi.history ha
    have hb := LazyQuarticPrefix.active_bounds p h.valid f h.gap
      (fun i => (states p g st i).point.x) hx0 t (by omega)
      (fun i hit => (hh i hit).1) (fun i hit => (hh i hit).2)
    have hd := LazyQuarticTransition.step_correct p f h g hg hH (states p g st t)
      hi.faithful hi.snapshot hb.1 hb.2.2 ha
    have hn' : p.ε < ‖((step p (states p g st t)).eval g).point.gradient‖ := by
      simpa only [states_succ] using hn
    have he := hd.2.2 hn'
    have hm := (LazyQuarticStageParameters.basic_scales p h.valid ((refresh p (states p g st t)).eval g)).1
    have hq := LazyQuarticParameters.decrease_pos p h.valid
    have hcharge := QuarticRefreshLedger.movement_charge hm hq
      (norm_nonneg _) (by linarith only [he.1]) he.2
    have hroot : 0 < Real.sqrt (alpha p / (64 * beta p) * decrease p) :=
      Real.sqrt_pos.mpr (mul_pos hm hq)
    have hc' : ‖((refresh p (states p g st t)).eval g).coordinates
        (((step p (states p g st t)).eval g).point.x - (states p g st t).point.x)‖ ≤
        chargeCoefficient p * ((states p g st t).point.value - ((step p (states p g st t)).eval g).point.value) := by
      unfold chargeCoefficient
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hroot).mpr
      simpa only [parameters, mul_comm] using hcharge
    have hmoved := refresh_movement p g (states p g st t) hn'
    have hl := QuarticRefreshLedger.refresh_step
      (reset_threshold p (states p g st t)) hmoved hc'
    rw [hi.faithful.1, hd.1.1] at hl
    rw [ghost_active p _ t ha, ghost_active p _ (t + 1) hn]
    simpa only [states_succ] using hl
  · have hz : ghost p (states p g st) (t + 1) = ghost p (states p g st) t := by
      exact ite_eq_right hn
    rw [hz, sub_self, mul_zero, potential, ite_eq_right hn, add_zero]
    exact QuarticRefreshLedger.terminal_step (potential_nonneg p _) (reset_threshold p _)

lemma loop_hessian_bound (p : Params) (f : p.E → ℝ) (h : LazyQuarticTransition.Data p f)
    (g : Fin 2 × p.E → Reply p.E)
    (hg : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hc : QuarticStageInvariant.Faithful f st.point)
    (hs : LazyQuarticTransition.SnapshotValid p f st) (hx0 : st.point.x = p.x0)
    (hs0 : st.snapshot = p.x0) :
    (EnergyHessianExecution.counts g (loop p (stages p) st) 1 : ℝ) ≤
      4 * chargeCoefficient p * p.Δ / radius p := by
  have hzero : potential p (states p g st 0) = 0 := by
    simp only [states_zero, potential, hx0, hs0, sub_self, map_zero, norm_zero, ite_self]
  have hh := QuarticRefreshLedger.refresh_prefix
    (V := fun t => potential p (states p g st t))
    (D := fun t => f (ghost p (states p g st) t) - f (ghost p (states p g st) (t + 1)))
    (refresh := fun t => refreshNeeded p (states p g st t))
    (LazyQuarticParameters.radius_pos p h.valid)
    (show 0 ≤ chargeCoefficient p by unfold chargeCoefficient; positivity) hzero (stages p)
    (ledger_step p f h g hg hH st hc hs hx0) (potential_nonneg p _)
    (charge_sum p f (states p g st) hx0 h.gap (stages p))
  rw [loop_hessian_calls]
  push_cast
  convert hh using 1

end LongTails.Proofs.LazyQuarticLedger
