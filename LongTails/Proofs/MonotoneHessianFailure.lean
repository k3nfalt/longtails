import LongTails.Proofs.MonotoneHessianProbability

namespace LongTails.Proofs.MonotoneHessianFailure

open OracleTemplate MeasureTheory LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.MonotoneHessianTransitions
open scoped RealInnerProductSpace

noncomputable def blockLaw (p : Params) : Measure (Block p) :=
  Measure.pi fun _ : Fin (repetitions p) => (PMF.uniformOfFintype (Sign p)).toMeasure

instance (p : Params) : IsProbabilityMeasure (blockLaw p) := by unfold blockLaw; infer_instance

def curvatureGood (p : Params) (f : p.E → ℝ) (x : p.E) : Prop :=
  ∀ v, -gamma p * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (_root_.gradient f) x v⟫

def badStep (p : Params) (f : p.E → ℝ) (O : Fin 2 × p.E → Reply p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (signs : Block p) : Prop :=
  st.done = false ∧ ((LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O).done = true ∧
    ¬curvatureGood p f ((LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O).point.x

lemma post_bad_iff (p : Params) (f : p.E → ℝ) (O : Fin 2 × p.E → Reply p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (snap : Snapshot p) (x : Point p.E) (signs : Block p) :
    (((postStage p st snap x signs).eval O).done = true ∧
      ¬curvatureGood p f ((postStage p st snap x signs).eval O).point.x) ↔
      (¬x.value ≤ st.point.value - progress p ∧ (detect p snap.coordinates x signs).eval O = none ∧
        ¬curvatureGood p f x.x) := by
  classical
  simp only [postStage]
  split
  · simp_all [padding_eval]
  · simp only [RandomReshuffling.eval_cast, QueryPlan.eval_bind]
    cases he : (detect p snap.coordinates x signs).eval O <;>
      simp_all [padding_eval, QueryPlan.eval_map]

lemma post_failure_bound (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hg : Differentiable ℝ (_root_.gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (snap : Snapshot p) (x : Point p.E) (hx : Faithful f x)
    (hA : (fderiv ℝ (_root_.gradient f) x.x).toLinearMap.IsSymmetric)
    (hmetric : ∀ v, 3 * delta p * ‖v‖ ^ 2 ≤ ‖snap.coordinates v‖ ^ 2)
    (hlo : ∀ v, ‖snap.coordinates v‖ ^ 2 - 6 * delta p * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫)
    (hhi : ∀ v, ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ ≤ ‖snap.coordinates v‖ ^ 2) :
    (blockLaw p).real {signs | ((postStage p st snap x signs).eval O).done = true ∧
      ¬curvatureGood p f ((postStage p st snap x signs).eval O).point.x} ≤ p.ρ / stages p := by
  classical
  by_cases hgood : curvatureGood p f x.x
  · have he : {signs : Block p | ((postStage p st snap x signs).eval O).done = true ∧
        ¬curvatureGood p f ((postStage p st snap x signs).eval O).point.x} = ∅ := by
      ext signs
      simp [post_bad_iff p f O st hd snap x signs, hgood]
    rw [he, measureReal_empty]
    exact div_nonneg hp.2.2.2.2.1.le (Nat.cast_nonneg _)
  · obtain ⟨v, hv⟩ : ∃ v, ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ < -gamma p * ‖v‖ ^ 2 := by
      simpa only [curvatureGood, not_forall, not_le] using hgood
    have hh := MonotoneHessianDetection.single_probability p hp f hg hLip snap.coordinates x hx.2
      hA hmetric hlo hhi O hO v hv
    have hb := MonotoneHessianDetection.detect_failure_probability p hp O snap.coordinates x hh
    apply (measureReal_mono ?_).trans hb
    intro signs hs
    exact ((post_bad_iff p f O st hd snap x signs).mp hs).2.1

lemma body_failure_bound (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (v : Option p.E)
    (hr : Prepared p (fderiv ℝ (_root_.gradient f)) st v) :
    (blockLaw p).real {signs | ((body p st v signs).eval O).done = true ∧
      ¬curvatureGood p f ((body p st v signs).eval O).point.x} ≤ p.ρ / stages p := by
  classical
  have hρ : 0 ≤ p.ρ / stages p := div_nonneg hp.2.2.2.2.1.le (Nat.cast_nonneg _)
  cases v with
  | some v =>
    simpa [body, hd, QueryPlan.eval_bind, padding_eval] using hρ
  | none =>
    obtain ⟨snap, hs, hdist⟩ := hr
    let x := (LongTails.Algorithms.MonotoneCurvatureStage.plan
      (LongTails.Algorithms.MonotoneCurvatureStage.parameters snap.coordinates st.point p.H (gamma p) (scale p))
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon (scale p))).eval O
    have he (signs : Block p) : (body p st none signs).eval O = (postStage p st snap x signs).eval O := by
      simp only [body, hd, Bool.false_eq_true, ↓reduceIte, hs]
      erw [RandomReshuffling.eval_cast, QueryPlan.eval_bind]
    simp_rw [he]
    by_cases hdrop : x.value ≤ st.point.value - progress p
    · have hempty : {signs : Block p | ((postStage p st snap x signs).eval O).done = true ∧
          ¬curvatureGood p f ((postStage p st snap x signs).eval O).point.x} = ∅ := by
        ext signs
        simp [post_bad_iff p f O st hd snap x signs, hdrop]
      simpa only [hempty, measureReal_empty] using hρ
    · have hsv := hi.snapshot snap hs
      have hstage := MonotoneHessianProgress.stage_progress p hp f _ hf hg hA hLip O hO st.point hi.faithful snap hsv hdist
      have ht := hstage.2.resolve_left (fun hh => hdrop hh.1)
      have hlocal := MonotoneHessianSnapshot.stage_local_metric p hp _ hA hLip snap.point st.point.x
        snap.coordinates hsv.factor hsv.lower hdist
      have hγ := MonotoneHessianParameters.gamma_pos p hp
      have hδ := MonotoneHessianParameters.delta_pos p hp
      have hτ := MonotoneCurvatureTuning.distanceScale_pos hp.1 hγ
      have hxr : ‖x.x - st.point.x‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale p.H (gamma p) := by
        have hx := ht.2.2
        change ‖x.x - st.point.x‖ ≤ _ at hx
        linarith
      apply post_failure_bound p hp f (fun z => (hg z).differentiableAt) hLip O hO st hd snap x hstage.1 (hA x.x)
      · intro v
        rw [hsv.factor]
        have hh := hsv.lower v
        linarith
      · intro v
        have hh := MonotoneCurvatureStageGuarantee.local_comparison _ snap.coordinates _ st.point.x x.x hlocal hxr v
        change ‖snap.coordinates v‖ ^ 2 ≤ _ + 6 * delta p * ‖v‖ ^ 2 at hh
        linarith
      · intro v
        have hh := hlocal.upper x.x hxr v
        exact hh.trans (sub_le_self _ (by positivity))

lemma step_failure_bound (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, O (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) :
    (blockLaw p) {signs | badStep p f O st signs} ≤ ENNReal.ofReal (p.ρ / stages p) := by
  classical
  have hh : (blockLaw p).real {signs | badStep p f O st signs} ≤ p.ρ / stages p := by
    by_cases hd : st.done = true
    · simp [badStep, hd]
      exact div_nonneg hp.2.2.2.2.1.le (Nat.cast_nonneg _)
    · have hd' : st.done = false := Bool.eq_false_iff.mpr hd
      have hpoint := prepare_point p O st
      have hvalid := prepare_valid p hp f _ hA O hH st hi
      have hready := prepare_ready p hp _ O hH st hd'
      have hb := body_failure_bound p hp f hf hg hA hLip O hO ((prepare p st).eval O).1
        (hpoint.2.trans hd') hvalid ((prepare p st).eval O).2 hready
      simpa only [badStep, hd', true_and, LongTails.Algorithms.MonotoneHessianReuse.step, QueryPlan.eval_bind] using hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top (blockLaw p) _)]
  exact ENNReal.ofReal_le_ofReal hh

lemma loop_good (p : Params) (f : p.E → ℝ) (O : Fin 2 × p.E → Reply p.E)
    (n : ℕ) (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (signs : Fin n → Block p)
    (hgood : st.done = true → curvatureGood p f st.point.x)
    (hbad : ¬MonotoneHessianProbability.badRun
      (fun st signs => (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O)
      (badStep p f O) n st signs) :
    ((LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs).eval O).done = true →
      curvatureGood p f ((LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs).eval O).point.x := by
  induction n generalizing st with
  | zero => exact hgood
  | succ n ih =>
    have hn := not_or.mp hbad
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st (signs 0)).eval O
    have hg : next.done = true → curvatureGood p f next.point.x := by
      intro hd
      by_cases hs : st.done = true
      · simpa only [next, done_step p O st (signs 0) hs] using hgood hs
      · by_contra hb
        exact hn.1 ⟨Bool.eq_false_iff.mpr hs, hd, hb⟩
    simpa only [LongTails.Algorithms.MonotoneHessianReuse.loop, id_eq, QueryPlan.eval_bind] using
      ih next (fun j => signs j.succ) hg hn.2

end LongTails.Proofs.MonotoneHessianFailure
