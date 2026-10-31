import LongTails.Proofs.MonotoneHessianTransitions
import LongTails.Proofs.MonotoneHessianLedger

namespace LongTails.Proofs.MonotoneHessianPotential

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.MonotoneHessianTransitions LongTails.Proofs.EnergyHessianExecution

noncomputable def credit (p : Params) (st : LongTails.Algorithms.MonotoneHessianReuse.State p) : ℝ :=
  if st.done then 0 else match st.snapshot with
    | none => delta p / (4 * p.H)
    | some snap => ‖st.point.x - snap.point‖

lemma credit_nonneg (p : Params) (hp : spec.valid p)
    (st : LongTails.Algorithms.MonotoneHessianReuse.State p) : 0 ≤ credit p st := by
  have hδ := (MonotoneHessianParameters.delta_pos p hp).le
  have hH := hp.1.le
  unfold credit
  split
  · exact le_rfl
  · cases st.snapshot <;> simp only
    · positivity
    · exact norm_nonneg _

lemma preserved_snapshot_credit (p : Params) (hp : spec.valid p)
    (st next : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hd : st.done = false) (hs : next.snapshot = st.snapshot) :
    credit p next ≤ credit p st + if next.done then 0 else ‖next.point.x - st.point.x‖ := by
  by_cases hn : next.done = true
  · simp only [credit, hn, ↓reduceIte, add_zero]
    exact credit_nonneg p hp st
  · have hn' : next.done = false := Bool.eq_false_iff.mpr hn
    simp only [credit, hd, hn', Bool.false_eq_true, ↓reduceIte, hs]
    cases st.snapshot with
    | none => exact le_add_of_nonneg_right (norm_nonneg _)
    | some snap =>
      have hh := norm_sub_le (next.point.x - st.point.x) (snap.point - st.point.x)
      rw [sub_sub_sub_cancel_right, norm_sub_rev snap.point st.point.x] at hh
      linarith

lemma prepare_credit (p : Params) (hp : spec.valid p)
    (O : Fin 2 × p.E → Reply p.E) (st : LongTails.Algorithms.MonotoneHessianReuse.State p) :
    let ready := (prepare p st).eval O
    delta p / (4 * p.H) * (counts O (prepare p st) 1 : ℝ) + credit p ready.1 ≤
      credit p st + delta p / (4 * p.H) * (if ready.2.isSome then 1 else 0) := by
  classical
  have hδ := (MonotoneHessianParameters.delta_pos p hp).le
  have hH := hp.1.le
  have hR : 0 ≤ delta p / (4 * p.H) := by positivity
  by_cases hd : st.done = true
  · simp [prepare, hd, padding_eval, MonotoneHessianCounts.padding_hessian, credit]
  · have hd' : st.done = false := Bool.eq_false_iff.mpr hd
    cases hs : st.snapshot with
    | none =>
      simp only [prepare, hd, hs]
      cases hv : negativeDirection p (readHessian p (O (1, st.point.x))) <;>
        simp [hv, QueryPlan.eval, counts, credit, hd', hs]
    | some snap =>
      by_cases hr : ‖st.point.x - snap.point‖ ≤ delta p / (4 * p.H)
      · simp [prepare, hd, hs, hr, padding_eval, MonotoneHessianCounts.padding_hessian]
      · have hb : delta p / (4 * p.H) ≤ ‖st.point.x - snap.point‖ := (lt_of_not_ge hr).le
        simp only [prepare, hd, ↓reduceIte, hs, hr]
        cases hv : negativeDirection p (readHessian p (O (1, st.point.x))) <;>
          simp [hv, QueryPlan.eval, counts, credit, hd', hs] <;> linarith

lemma step_credit (p : Params) (hp : spec.valid p)
    (O : Fin 2 × p.E → Reply p.E) (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (signs : Block p) (hd : st.done = false)
    (hs : ((LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O).snapshot =
      ((prepare p st).eval O).1.snapshot) :
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
    delta p / (4 * p.H) * (counts O (LongTails.Algorithms.MonotoneHessianReuse.step p st signs) 1 : ℝ) +
      credit p next ≤ credit p st + (if next.done then 0 else ‖next.point.x - st.point.x‖) +
        delta p / (4 * p.H) * (if ((prepare p st).eval O).2.isSome then 1 else 0) := by
  have hpnt := prepare_point p O st
  have h₁ := prepare_credit p hp O st
  have h₂ := preserved_snapshot_credit p hp ((prepare p st).eval O).1
    ((LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O) (hpnt.2.trans hd) hs
  rw [hpnt.1] at h₂
  rw [MonotoneHessianCounts.step_hessian]
  linarith

lemma scalar_charge {R ℓ D drop distance coarse fresh before after : ℝ}
    (hR : 0 ≤ R) (hℓ : 0 < ℓ) (hD : 0 < D)
    (hmovement : ℓ * distance ≤ drop) (hcoarse : D * coarse ≤ drop)
    (hpotential : R * fresh + after ≤ before + distance + R * coarse) :
    R * fresh + after ≤ before + (1 / ℓ + R / D) * drop := by
  have hd : distance ≤ drop / ℓ := (le_div_iff₀ hℓ).mpr (by nlinarith only [hmovement])
  have hc : coarse ≤ drop / D := (le_div_iff₀ hD).mpr (by nlinarith only [hcoarse])
  have hh := mul_le_mul_of_nonneg_left hc hR
  calc
    R * fresh + after ≤ before + distance + R * coarse := hpotential
    _ ≤ before + drop / ℓ + R * (drop / D) := by linarith
    _ = before + (1 / ℓ + R / D) * drop := by ring

end LongTails.Proofs.MonotoneHessianPotential
