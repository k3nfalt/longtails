import LongTails.Proofs.LazyQuarticTransition
import LongTails.Proofs.LazyQuarticPrefix

namespace LongTails.Proofs.LazyQuarticTrace

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Algorithms.QuarticMetricStage (Reply)
open LongTails.Proofs.QuarticStageInvariant (Faithful)
open LongTails.Proofs.LazyQuarticExecution
open LongTails.Proofs.LazyQuarticTransition

structure Invariant (p : Params) (f : p.E → ℝ) (s : ℕ → State p) (t : ℕ) : Prop where
  faithful : Faithful f (s t).point
  snapshot : SnapshotValid p f (s t)
  history : p.ε < ‖(s t).point.gradient‖ → ∀ i < t,
    f (s (i + 1)).point.x ≤ f (s i).point.x - decrease p ∧
    alpha p * ‖(s (i + 1)).point.x - (s i).point.x‖ ^ 2 ≤
      16384 * (f (s i).point.x - f (s (i + 1)).point.x)

lemma trace_invariant (p : Params) (f : p.E → ℝ) (h : Data p f)
    (g : Fin 2 × p.E → Reply p.E)
    (hg : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hc : Faithful f st.point) (hs : SnapshotValid p f st)
    (hx0 : st.point.x = p.x0) (t : ℕ) (ht : t ≤ stages p) :
    Invariant p f (states p g st) t := by
  induction t with
  | zero => exact ⟨hc, hs, by intro ha i hi; omega⟩
  | succ t ih =>
    have hi := ih (by omega)
    by_cases ha : p.ε < ‖(states p g st t).point.gradient‖
    · have hh := hi.history ha
      have hb := LazyQuarticPrefix.active_bounds p h.valid f h.gap
        (fun i => (states p g st i).point.x) hx0 t (by omega)
        (fun i hit => (hh i hit).1) (fun i hit => (hh i hit).2)
      have hc' := step_correct p f h g hg hH (states p g st t) hi.faithful hi.snapshot hb.1 hb.2.2 ha
      have hr := refresh_valid p f g hH (states p g st t) hi.snapshot hb.1 hb.2.2
      refine ⟨by simpa only [states_succ] using hc'.1,
        by simpa only [states_succ] using hc'.2.1, ?_⟩
      intro hn i hit
      have hn' : p.ε < ‖((step p (states p g st t)).eval g).point.gradient‖ := by
        simpa only [states_succ] using hn
      have hd := hc'.2.2 hn'
      have he := euclidean_energy p f h ((refresh p (states p g st t)).eval g) hr
        (((step p (states p g st t)).eval g).point.x - (states p g st t).point.x)
        ((states p g st t).point.value - ((step p (states p g st t)).eval g).point.value) hd.2
      by_cases hit' : i < t
      · exact hh i hit'
      · have hie : i = t := by omega
        subst i
        rw [hi.faithful.1, hc'.1.1] at hd he
        simpa only [states_succ] using And.intro hd.1 he
    · have he : states p g st (t + 1) = states p g st t := by
        rw [states_succ, step_inactive p g _ (le_of_not_gt ha)]
      refine ⟨by simpa only [he] using hi.faithful,
        by simpa only [he] using hi.snapshot, ?_⟩
      intro hn
      exact False.elim (ha (by simpa only [he] using hn))

lemma trace_terminates (p : Params) (f : p.E → ℝ) (h : Data p f)
    (g : Fin 2 × p.E → Reply p.E)
    (hg : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, g (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : State p) (hc : Faithful f st.point) (hs : SnapshotValid p f st)
    (hx0 : st.point.x = p.x0) :
    ‖_root_.gradient f (states p g st (stages p)).point.x‖ ≤ p.ε := by
  have hi := trace_invariant p f h g hg hH st hc hs hx0 (stages p) le_rfl
  rw [← hi.faithful.2]
  by_contra hn
  have hh := hi.history (lt_of_not_ge hn)
  have hd := LazyQuarticPrefix.value_decrease (fun i => f (states p g st i).point.x)
    (decrease p) (stages p) (fun i hit => (hh i hit).1)
  change f (states p g st (stages p)).point.x ≤ f st.point.x - _ at hd
  rw [hx0] at hd
  have hg' := h.gap (states p g st (stages p)).point.x
  have hT := LazyQuarticParameters.stages_sufficient p h.valid
  linarith

end LongTails.Proofs.LazyQuarticTrace
