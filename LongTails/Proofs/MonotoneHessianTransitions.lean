import LongTails.Proofs.MonotoneHessianSnapshot
import LongTails.Proofs.MonotoneHessianCounts

namespace LongTails.Proofs.MonotoneHessianTransitions

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open scoped RealInnerProductSpace

structure SnapshotValid (p : Params) (A : p.E → p.E →L[ℝ] p.E) (snap : Snapshot p) : Prop where
  factor : ∀ v, ‖snap.coordinates v‖ ^ 2 = ⟪v, A snap.point v⟫ + 4 * delta p * ‖v‖ ^ 2
  lower : ∀ v, -delta p * ‖v‖ ^ 2 ≤ ⟪v, A snap.point v⟫

structure StateValid (p : Params) (f : p.E → ℝ) (A : p.E → p.E →L[ℝ] p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) : Prop where
  faithful : LongTails.Proofs.QuarticStageInvariant.Faithful f st.point
  snapshot : ∀ snap, st.snapshot = some snap → SnapshotValid p A snap

lemma padding_eval (p : Params) (O : Fin 2 × p.E → Reply p.E) (x : p.E) (n : ℕ)
    {U : Type} (u : U) : (padding p x n u).eval O = u := by
  simp [padding, RandomReshuffling.eval_cast, QueryPlan.eval_map]

lemma prepare_point (p : Params) (O : Fin 2 × p.E → Reply p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) :
    ((prepare p st).eval O).1.point = st.point ∧ ((prepare p st).eval O).1.done = st.done := by
  classical
  simp only [prepare]
  split
  · simp [padding_eval]
  · cases hs : st.snapshot
    all_goals simp only [QueryPlan.eval]
    all_goals (try split) <;> simp_all [QueryPlan.eval, padding_eval]
    all_goals (try split) <;> simp_all [QueryPlan.eval]

lemma prepare_valid (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (A : p.E → p.E →L[ℝ] p.E) (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (1, x) = .inr (A x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hi : StateValid p f A st) :
    StateValid p f A ((prepare p st).eval O).1 := by
  classical
  have hf := (prepare_point p O st).1
  refine ⟨by rw [hf]; exact hi.faithful, ?_⟩
  intro snap hsnap
  simp only [prepare] at hsnap
  split at hsnap
  · rw [padding_eval] at hsnap
    exact hi.snapshot snap hsnap
  · cases hs : st.snapshot with
    | none =>
      simp only [hs, QueryPlan.eval, hO, readHessian] at hsnap
      split at hsnap
      · simp [QueryPlan.eval] at hsnap
      · rename_i hn
        simp only [QueryPlan.eval, Option.some.injEq] at hsnap
        subst snap
        exact ⟨MonotoneHessianSnapshot.snapshot_metric p (A st.point.x) (hA _)
          (MonotoneHessianParameters.delta_pos p hp) hn,
          MonotoneHessianSnapshot.no_negative_direction p (A st.point.x) hn⟩
    | some old =>
      simp only [hs] at hsnap
      split at hsnap
      · rw [padding_eval] at hsnap
        exact hi.snapshot snap hsnap
      · simp only [QueryPlan.eval, hO, readHessian] at hsnap
        split at hsnap
        · simp [QueryPlan.eval] at hsnap
        · rename_i hn
          simp only [QueryPlan.eval, Option.some.injEq] at hsnap
          subst snap
          exact ⟨MonotoneHessianSnapshot.snapshot_metric p (A st.point.x) (hA _)
            (MonotoneHessianParameters.delta_pos p hp) hn,
            MonotoneHessianSnapshot.no_negative_direction p (A st.point.x) hn⟩

def Prepared (p : Params) (A : p.E → p.E →L[ℝ] p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) : Option p.E → Prop
  | some v => st.snapshot = none ∧ ‖v‖ = 1 ∧ ⟪v, A st.point.x v⟫ < -delta p
  | none => ∃ snap, st.snapshot = some snap ∧ ‖st.point.x - snap.point‖ ≤ delta p / (4 * p.H)

lemma prepare_ready (p : Params) (hp : spec.valid p)
    (A : p.E → p.E →L[ℝ] p.E)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (1, x) = .inr (A x))
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (hd : st.done = false) :
    Prepared p A ((prepare p st).eval O).1 ((prepare p st).eval O).2 := by
  classical
  have hR : 0 ≤ delta p / (4 * p.H) := by
    have hh := (MonotoneHessianParameters.delta_pos p hp).le
    exact div_nonneg hh (by linarith [hp.1])
  simp only [prepare, hd, Bool.false_eq_true, ↓reduceIte]
  cases hs : st.snapshot with
  | none =>
    simp only [QueryPlan.eval, hO, readHessian]
    split
    · rename_i v hv
      exact ⟨rfl, MonotoneHessianSnapshot.chosen_negative_direction p (A st.point.x) v hv⟩
    · exact ⟨_, rfl, by simpa [QueryPlan.eval] using hR⟩
  | some snap =>
    dsimp only
    split
    · rename_i hr
      rw [padding_eval]
      exact ⟨snap, hs, hr⟩
    · simp only [QueryPlan.eval, hO, readHessian]
      split
      · rename_i v hv
        exact ⟨rfl, MonotoneHessianSnapshot.chosen_negative_direction p (A st.point.x) v hv⟩
      · exact ⟨_, rfl, by simpa [QueryPlan.eval] using hR⟩

lemma done_step (p : Params) (O : Fin 2 × p.E → Reply p.E)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (signs : Block p) (hd : st.done = true) :
    (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O = st := by
  simp [LongTails.Algorithms.MonotoneHessianReuse.step,
    QueryPlan.eval_bind, prepare, hd, padding_eval, body]

lemma escape_guarantee (p : Params) (f : p.E → ℝ) (A : p.E → p.E →L[ℝ] p.E)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (x : Point p.E) (hx : LongTails.Proofs.QuarticStageInvariant.Faithful f x)
    (v : p.E) (hv : v ≠ 0) {η κ : ℝ} (hη : 0 ≤ η) (hηH : p.H * η ≤ κ)
    (hcurv : ⟪v, A x.x v⟫ ≤ -κ * ‖v‖ ^ 2) :
    let y := (escape p x η v).eval O
    LongTails.Proofs.QuarticStageInvariant.Faithful f y ∧
      y.value ≤ x.value - κ * η ^ 2 / 3 ∧ ‖y.x - x.x‖ = η := by
  let z := LongTails.Algorithms.MonotoneCurvatureStage.signedDirection x.gradient v
  have hz := MonotoneCurvatureGeometry.signed_direction_norm x.gradient v hv
  have hc := MonotoneCurvatureGeometry.signed_direction_curvature (A x.x) x.gradient v hv hcurv
  have hs : ⟪_root_.gradient f x.x, z⟫ ≤ 0 := by
    rw [← hx.2]
    exact MonotoneCurvatureGeometry.signed_direction_pairing _ _
  have hh := ReusedCurvatureCorrection.negative_curvature_descent hf hg hLip x.x z hz hη hs hc hηH
  simp only [escape, QueryPlan.eval, hO, readPoint]
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · simpa only [hx.1] using hh
  · change ‖x.x + η • z - x.x‖ = η
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, hz, mul_one]

lemma loop_done (p : Params) (O : Fin 2 × p.E → Reply p.E) (n : ℕ)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) (signs : Fin n → Block p)
    (hd : st.done = true) : (LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs).eval O = st := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LongTails.Algorithms.MonotoneHessianReuse.loop, id_eq, QueryPlan.eval_bind, done_step p O st _ hd]
    exact ih _

end LongTails.Proofs.MonotoneHessianTransitions
