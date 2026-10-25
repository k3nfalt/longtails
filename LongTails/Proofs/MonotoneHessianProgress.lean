import LongTails.Proofs.MonotoneHessianTransitions
import LongTails.Proofs.MonotoneHessianDetection
import LongTails.Proofs.MonotoneHessianLedger

namespace LongTails.Proofs.MonotoneHessianProgress

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.MonotoneHessianTransitions
open scoped RealInnerProductSpace

lemma stage_progress (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (A : p.E → p.E →L[ℝ] p.E)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (c : Point p.E) (hc : Faithful f c) (snap : Snapshot p) (hs : SnapshotValid p A snap)
    (hr : ‖c.x - snap.point‖ ≤ delta p / (4 * p.H)) :
    let out := (LongTails.Algorithms.MonotoneCurvatureStage.plan
      (LongTails.Algorithms.MonotoneCurvatureStage.parameters snap.coordinates c p.H (gamma p) (scale p))
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon (scale p))).eval O
    Faithful f out ∧
      ((out.value ≤ c.value - progress p ∧ p.ε / 2 ^ 40 * ‖out.x - c.x‖ ≤ c.value - out.value) ∨
        (out.value ≤ c.value ∧ ‖_root_.gradient f out.x‖ ≤ p.ε ∧
          ‖out.x - c.x‖ ≤ 4 * MonotoneCurvatureTuning.distanceScale p.H (gamma p))) := by
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have ht := MonotoneHessianParameters.scale_ge_one p
  have hε := MonotoneHessianParameters.gamma_sq p hp
  have hτ := MonotoneCurvatureTuning.distanceScale_pos hp.1 hγ
  have he := (MonotoneHessianParameters.distance_scale_identities p hp).2
  have hη : gamma p / (1024 * p.H) =
      2 ^ 20 * MonotoneCurvatureTuning.distanceScale p.H (gamma p) := by
    unfold MonotoneCurvatureTuning.distanceScale
    ring
  have hcharge := MonotoneHessianLedger.curvature_charge hγ.le hτ.le he hη
  have hlarge : (7 * gamma p / 1024) * (gamma p / (1024 * p.H)) ^ 2 / 3 ≤
      gamma p * (gamma p / (1024 * p.H)) ^ 2 / 3 := by
    nlinarith [mul_nonneg hγ.le (sq_nonneg (gamma p / (1024 * p.H)))]
  have hlocal := MonotoneHessianSnapshot.stage_local_metric p hp A hA hLip snap.point c.x
    snap.coordinates hs.factor hs.lower hr
  obtain ⟨ho, hw | hordinary | hterminal⟩ := MonotoneCurvatureStageGuarantee.stage_guarantee
    hp.1 hγ ht hε hf hg hLip snap.coordinates
    (A snap.point + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) c hc hlocal O hO
  · refine ⟨ho, Or.inl ⟨?_, ?_⟩⟩
    · have hh := hcharge.1.trans hlarge
      change progress p ≤ _ at hh
      linarith [hw.1]
    · rw [hw.2]
      have hh := hcharge.2.trans hlarge
      have hn : 0 ≤ p.ε / 2 ^ 40 * (4 * MonotoneCurvatureTuning.distanceScale p.H (gamma p)) := by
        have hε0 := hp.2.2.1
        positivity
      nlinarith [hw.1]
  · refine ⟨ho, Or.inl ⟨hordinary.1, ?_⟩⟩
    apply MonotoneHessianLedger.ordinary_charge hp.2.2.1.le hτ.le he hordinary.2
    linarith [hordinary.1]
  · exact ⟨ho, Or.inr hterminal⟩

lemma postStage_progress (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (snap : Snapshot p) (x : Point p.E) (hx : Faithful f x)
    (hmetric : ∀ v, 3 * delta p * ‖v‖ ^ 2 ≤ ‖snap.coordinates v‖ ^ 2)
    (hstage : (x.value ≤ st.point.value - progress p ∧ p.ε / 2 ^ 40 * ‖x.x - st.point.x‖ ≤ st.point.value - x.value) ∨
      (x.value ≤ st.point.value ∧ ‖_root_.gradient f x.x‖ ≤ p.ε ∧
        ‖x.x - st.point.x‖ ≤ 4 * MonotoneCurvatureTuning.distanceScale p.H (gamma p))) (signs : Block p) :
    let next := (postStage p st snap x signs).eval O
    Faithful f next.point ∧ next.snapshot = st.snapshot ∧
      (if next.done then next.point.value ≤ st.point.value ∧ ‖_root_.gradient f next.point.x‖ ≤ p.ε
        else next.point.value ≤ st.point.value - progress p ∧
          p.ε / 2 ^ 40 * ‖next.point.x - st.point.x‖ ≤ st.point.value - next.point.value) := by
  classical
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have hτ := MonotoneCurvatureTuning.distanceScale_pos hp.1 hγ
  have hε := hp.2.2.1
  have hη : 0 ≤ gamma p / (1024 * p.H) := by have hh := hp.1; positivity
  have hηH : p.H * (gamma p / (1024 * p.H)) ≤ 7 * gamma p / 1024 := by
    have he : p.H * (gamma p / (1024 * p.H)) = gamma p / 1024 := by field_simp [hp.1.ne']
    rw [he]
    linarith
  simp only [postStage]
  split
  · rename_i hdrop
    rw [padding_eval]
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hx, trivial, hdrop, ?_⟩
    rcases hstage with hh | hh
    · exact hh.2
    · apply MonotoneHessianLedger.ordinary_charge hε.le hτ.le
        (MonotoneHessianParameters.distance_scale_identities p hp).2
        (show ‖x.x - st.point.x‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale p.H (gamma p) by linarith [hh.2.2])
      change progress p ≤ _
      linarith
  · rename_i hn
    have ht := hstage.resolve_left (fun hh => hn hh.1)
    simp only [RandomReshuffling.eval_cast, QueryPlan.eval_bind]
    cases he : (detect p snap.coordinates x signs).eval O with
    | none =>
      rw [padding_eval]
      exact ⟨hx, rfl, ht.1, ht.2.1⟩
    | some v =>
      simp only [QueryPlan.eval_map, hd, Bool.false_eq_true, ↓reduceIte]
      have hv := MonotoneHessianDetection.detect_sound p hp f (fun z => (hg z).differentiableAt)
        hLip snap.coordinates x hx.2 hmetric O hO signs v he
      obtain ⟨hy, hdrop, hdist⟩ := escape_guarantee p f _ hf hg hLip O hO x hx v hv.1 hη hηH hv.2
      have hid : gamma p / (1024 * p.H) =
          2 ^ 20 * MonotoneCurvatureTuning.distanceScale p.H (gamma p) := by
        unfold MonotoneCurvatureTuning.distanceScale
        ring
      have hc := MonotoneHessianLedger.curvature_charge hγ.le hτ.le
        (MonotoneHessianParameters.distance_scale_identities p hp).2 hid
      refine ⟨hy, trivial, ?_, ?_⟩
      · have hq := hc.1
        change progress p ≤ _ at hq
        linarith [hq, ht.1]
      · have hd := norm_sub_le
          (((escape p x (gamma p / (1024 * p.H)) v).eval O).x - x.x) (st.point.x - x.x)
        rw [sub_sub_sub_cancel_right, norm_sub_rev st.point.x x.x] at hd
        have htotal : ‖((escape p x (gamma p / (1024 * p.H)) v).eval O).x - st.point.x‖ ≤
            4 * MonotoneCurvatureTuning.distanceScale p.H (gamma p) + gamma p / (1024 * p.H) := by
          linarith [ht.2.2, hdist]
        have hh := mul_le_mul_of_nonneg_left htotal (show 0 ≤ p.ε / 2 ^ 40 by positivity)
        linarith [hc.2, ht.1]

lemma body_progress (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (v : Option p.E)
    (hr : Prepared p (fderiv ℝ (_root_.gradient f)) st v) (signs : Block p) :
    let next := (body p st v signs).eval O
    StateValid p f (fderiv ℝ (_root_.gradient f)) next ∧ next.snapshot = st.snapshot ∧
      (if next.done then next.point.value ≤ st.point.value ∧ ‖_root_.gradient f next.point.x‖ ≤ p.ε
        else next.point.value ≤ st.point.value - progress p ∧
          p.ε / 2 ^ 40 * ‖next.point.x - st.point.x‖ ≤ st.point.value - next.point.value) := by
  classical
  have hδ := MonotoneHessianParameters.delta_pos p hp
  simp only [body, hd, Bool.false_eq_true, ↓reduceIte]
  cases v with
  | some v =>
    obtain ⟨hs, hv, hc⟩ := hr
    simp only [QueryPlan.eval_bind, padding_eval,
      Bool.false_eq_true, ↓reduceIte]
    have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
    have hη : 0 ≤ delta p / p.H := div_nonneg hδ.le hp.1.le
    have hηH : p.H * (delta p / p.H) ≤ delta p := by rw [mul_div_cancel₀ _ hp.1.ne']
    have hc' : ⟪v, fderiv ℝ (_root_.gradient f) st.point.x v⟫ ≤ -delta p * ‖v‖ ^ 2 := by
      simpa [hv] using hc.le
    obtain ⟨hy, hdrop, hdist⟩ := escape_guarantee p f _ hf hg hLip O hO st.point hi.faithful v hv0 hη hηH hc'
    refine ⟨⟨hy, ?_⟩, hs.symm, ?_, ?_⟩
    · intro snap hh
      simp at hh
    · have hq := MonotoneHessianLedger.coarse_progress p hp
      linarith
    · rw [hdist]
      have hh := MonotoneHessianLedger.coarse_curvature_charge hp.1
        (MonotoneHessianParameters.gamma_pos p hp).le
        (MonotoneHessianParameters.gamma_le_delta p hp) (MonotoneHessianParameters.gamma_sq p hp)
      linarith
  | none =>
    obtain ⟨snap, hs, hdist⟩ := hr
    have hvalid := hi.snapshot snap hs
    simp only [hs]
    erw [RandomReshuffling.eval_cast, QueryPlan.eval_bind]
    let x := (LongTails.Algorithms.MonotoneCurvatureStage.plan
      (LongTails.Algorithms.MonotoneCurvatureStage.parameters snap.coordinates st.point p.H (gamma p) (scale p))
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon (scale p))).eval O
    have hstage := stage_progress p hp f _ hf hg hA hLip O hO st.point hi.faithful snap hvalid hdist
    have hm (v : p.E) : 3 * delta p * ‖v‖ ^ 2 ≤ ‖snap.coordinates v‖ ^ 2 := by
      rw [hvalid.factor]
      have hh := hvalid.lower v
      linarith
    have hh := postStage_progress p hp f hf hg hLip O hO st hd snap x hstage.1 hm hstage.2 signs
    refine ⟨⟨hh.1, ?_⟩, hh.2.1.trans hs, hh.2.2⟩
    intro old hold
    rw [hh.2.1] at hold
    exact hi.snapshot old hold

lemma coarse_body_drop (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (hi : Faithful f st.point) (v : p.E)
    (hr : Prepared p (fderiv ℝ (_root_.gradient f)) st (some v)) (signs : Block p) :
    ((body p st (some v) signs).eval O).point.value ≤
      st.point.value - delta p * (delta p / p.H) ^ 2 / 3 := by
  obtain ⟨_, hv, hc⟩ := hr
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
  have hη : 0 ≤ delta p / p.H := div_nonneg hδ.le hp.1.le
  have hηH : p.H * (delta p / p.H) ≤ delta p := by rw [mul_div_cancel₀ _ hp.1.ne']
  have hc' : ⟪v, fderiv ℝ (_root_.gradient f) st.point.x v⟫ ≤ -delta p * ‖v‖ ^ 2 := by
    simpa [hv] using hc.le
  have hh := escape_guarantee p f _ hf hg hLip O hO st.point hi v hv0 hη hηH hc'
  simpa only [body, hd, Bool.false_eq_true, ↓reduceIte, QueryPlan.eval_bind, padding_eval] using hh.2.1

lemma step_progress (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, O (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (signs : Block p) :
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
    StateValid p f (fderiv ℝ (_root_.gradient f)) next ∧
      next.snapshot = ((prepare p st).eval O).1.snapshot ∧
      (if next.done then next.point.value ≤ st.point.value ∧ ‖_root_.gradient f next.point.x‖ ≤ p.ε
        else next.point.value ≤ st.point.value - progress p ∧
          p.ε / 2 ^ 40 * ‖next.point.x - st.point.x‖ ≤ st.point.value - next.point.value) := by
  have hpoint := prepare_point p O st
  have hvalid := prepare_valid p hp f _ hA O hH st hi
  have hready := prepare_ready p hp _ O hH st hd
  have hh := body_progress p hp f hf hg hA hLip O hO ((prepare p st).eval O).1
    (hpoint.2.trans hd) hvalid ((prepare p st).eval O).2 hready signs
  simpa only [LongTails.Algorithms.MonotoneHessianReuse.step, QueryPlan.eval_bind,
    hpoint.1] using hh

end LongTails.Proofs.MonotoneHessianProgress
