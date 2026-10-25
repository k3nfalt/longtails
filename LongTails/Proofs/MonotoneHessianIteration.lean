import LongTails.Proofs.MonotoneHessianProgress

namespace LongTails.Proofs.MonotoneHessianIteration

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.MonotoneHessianTransitions
open scoped RealInnerProductSpace

variable (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, O (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))

include hp hf hg hA hLip hO hH

lemma step_invariant (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st)
    (hd : st.done = true → ‖_root_.gradient f st.point.x‖ ≤ p.ε) (signs : Block p) :
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
    StateValid p f (fderiv ℝ (_root_.gradient f)) next ∧
      (next.done = true → ‖_root_.gradient f next.point.x‖ ≤ p.ε) ∧
      next.point.value ≤ st.point.value ∧
      (next.done = false → next.point.value ≤ st.point.value - progress p) := by
  by_cases hb : st.done = true
  · rw [done_step p O st signs hb]
    exact ⟨hi, hd, le_rfl, fun hh => by simp [hb] at hh⟩
  · have hb' : st.done = false := Bool.eq_false_iff.mpr hb
    have hh := MonotoneHessianProgress.step_progress p hp f hf hg hA hLip O hO hH st hb' hi signs
    refine ⟨hh.1, ?_, ?_, ?_⟩
    · intro hn
      have hv := hh.2.2
      simp only [hn, ↓reduceIte] at hv
      exact hv.2
    · have hq := MonotoneHessianParameters.progress_pos p hp
      have hv := hh.2.2
      split at hv
      · exact hv.1
      · linarith [hv.1]
    · intro hn
      have hv := hh.2.2
      simp only [hn, Bool.false_eq_true, ↓reduceIte] at hv
      exact hv.1

lemma loop_invariant (n : ℕ) (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st)
    (hd : st.done = true → ‖_root_.gradient f st.point.x‖ ≤ p.ε) (signs : Fin n → Block p) :
    let out := (LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs).eval O
    StateValid p f (fderiv ℝ (_root_.gradient f)) out ∧
      (out.done = true → ‖_root_.gradient f out.point.x‖ ≤ p.ε) ∧
      out.point.value ≤ st.point.value ∧
      (out.done = false → out.point.value ≤ st.point.value - n * progress p) := by
  induction n generalizing st with
  | zero =>
    simp only [LongTails.Algorithms.MonotoneHessianReuse.loop, QueryPlan.eval, Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨hi, hd, le_rfl, fun _ => le_rfl⟩
  | succ n ih =>
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st (signs 0)).eval O
    have hs := step_invariant p hp f hf hg hA hLip O hO hH st hi hd (signs 0)
    have ht := ih next hs.1 hs.2.1 (fun j => signs j.succ)
    simp only [LongTails.Algorithms.MonotoneHessianReuse.loop, id_eq, QueryPlan.eval_bind]
    refine ⟨ht.1, ht.2.1, ht.2.2.1.trans hs.2.2.1, ?_⟩
    intro hfinal
    have hn : next.done = false := by
      by_contra h
      have hh : next.done = true := Bool.eq_true_of_not_eq_false h
      rw [loop_done p O n next _ hh] at hfinal
      simp [hh] at hfinal
    have h₁ := hs.2.2.2 hn
    have h₂ := ht.2.2.2 hfinal
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

lemma termination (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (signs : Fin (stages p) → Block p) :
    let initial : LongTails.Algorithms.MonotoneHessianReuse.State p :=
      ⟨⟨p.x0, f p.x0, _root_.gradient f p.x0⟩, none, false⟩
    let out := (LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O
    out.done = true ∧ ‖_root_.gradient f out.point.x‖ ≤ p.ε := by
  let initial : LongTails.Algorithms.MonotoneHessianReuse.State p :=
    ⟨⟨p.x0, f p.x0, _root_.gradient f p.x0⟩, none, false⟩
  have hi : StateValid p f (fderiv ℝ (_root_.gradient f)) initial :=
    ⟨⟨rfl, rfl⟩, fun snap hs => by simp [initial] at hs⟩
  have hh := loop_invariant p hp f hf hg hA hLip O hO hH (stages p) initial hi
    (fun hs => by simp [initial] at hs) signs
  have hd : ((LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O).done = true := by
    by_contra hn
    have hn' := Bool.eq_false_iff.mpr hn
    have hb := hh.2.2.2 hn'
    have hv := hh.1.faithful.1
    have hg := hgap ((LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O).point.x
    have hk := MonotoneHessianParameters.horizon_exhausts p hp
    change _ ≤ f p.x0 - _ at hb
    rw [hv] at hb
    linarith
  exact ⟨hd, hh.2.1 hd⟩

end LongTails.Proofs.MonotoneHessianIteration
