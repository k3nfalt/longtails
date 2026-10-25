import LongTails.Proofs.MonotoneHessianIteration
import LongTails.Proofs.MonotoneHessianPotential

namespace LongTails.Proofs.MonotoneHessianCost

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.MonotoneHessianTransitions
open LongTails.Proofs.MonotoneHessianPotential LongTails.Proofs.EnergyHessianExecution
open scoped RealInnerProductSpace

noncomputable def chargeFactor (p : Params) : ℝ :=
  1 / (p.ε / 2 ^ 40) + (delta p / (4 * p.H)) / (delta p * (delta p / p.H) ^ 2 / 3)

variable (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, O (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))

include hp hf hg hA hLip hO hH

lemma step_amortized (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (signs : Block p) :
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
    delta p / (4 * p.H) * (counts O (LongTails.Algorithms.MonotoneHessianReuse.step p st signs) 1 : ℝ) +
      credit p next ≤ credit p st + chargeFactor p * (st.point.value - next.point.value) := by
  let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
  let ready := (prepare p st).eval O
  by_cases hd : st.done = true
  · rw [done_step p O st signs hd, MonotoneHessianCounts.step_hessian,
      MonotoneHessianCounts.done_prepare_hessian p O st hd]
    simp
  · have hd' : st.done = false := Bool.eq_false_iff.mpr hd
    have hs := MonotoneHessianProgress.step_progress p hp f hf hg hA hLip O hO hH st hd' hi signs
    have hpoint := prepare_point p O st
    have hready := prepare_ready p hp _ O hH st hd'
    have hq := MonotoneHessianParameters.progress_pos p hp
    have hδ := MonotoneHessianParameters.delta_pos p hp
    have hHpos := hp.1
    have hε := hp.2.2.1
    have hnonneg : 0 ≤ st.point.value - next.point.value := by
      have hh := hs.2.2
      split at hh <;> linarith [hh.1]
    have hmove : p.ε / 2 ^ 40 * (if next.done then 0 else ‖next.point.x - st.point.x‖) ≤
        st.point.value - next.point.value := by
      by_cases hn : next.done = true
      · simpa only [hn, ↓reduceIte, mul_zero] using hnonneg
      · have hh := hs.2.2
        change (if next.done then _ else _) at hh
        simp only [hn] at hh ⊢
        exact hh.2
    have hc : (delta p * (delta p / p.H) ^ 2 / 3) * (if ready.2.isSome then 1 else 0) ≤
        st.point.value - next.point.value := by
      cases hv : ready.2 with
      | none => simpa only [hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, mul_zero] using hnonneg
      | some v =>
        have hr : Prepared p (fderiv ℝ (_root_.gradient f)) ready.1 (some v) := by
          change Prepared p (fderiv ℝ (_root_.gradient f)) ready.1 ready.2 at hready
          rwa [hv] at hready
        have hh := MonotoneHessianProgress.coarse_body_drop p hp f hf hg hLip O hO ready.1
          (hpoint.2.trans hd') (by rw [hpoint.1]; exact hi.faithful) v hr signs
        have he : next = (body p ready.1 (some v) signs).eval O := by
          simp only [next, LongTails.Algorithms.MonotoneHessianReuse.step, QueryPlan.eval_bind]
          rw [hv]
        rw [← he, hpoint.1] at hh
        simp only [Option.isSome_some, ↓reduceIte, mul_one]
        linarith
    exact scalar_charge (by positivity) (by positivity) (by positivity) hmove hc
      (step_credit p hp O st signs hd' hs.2.1)

lemma loop_amortized (n : ℕ) (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
    (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (signs : Fin n → Block p) :
    let out := (LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs).eval O
    delta p / (4 * p.H) * (counts O (LongTails.Algorithms.MonotoneHessianReuse.loop p n st signs) 1 : ℝ) +
      credit p out ≤ credit p st + chargeFactor p * (st.point.value - out.point.value) := by
  induction n generalizing st with
  | zero => simp [LongTails.Algorithms.MonotoneHessianReuse.loop, QueryPlan.eval, counts]
  | succ n ih =>
    let next := (LongTails.Algorithms.MonotoneHessianReuse.step p st (signs 0)).eval O
    have hv : StateValid p f (fderiv ℝ (_root_.gradient f)) next := by
      by_cases hd : st.done = true
      · simpa only [next, done_step p O st (signs 0) hd] using hi
      · exact (MonotoneHessianProgress.step_progress p hp f hf hg hA hLip O hO hH st
          (Bool.eq_false_iff.mpr hd) hi (signs 0)).1
    have hs := step_amortized p hp f hf hg hA hLip O hO hH st hi (signs 0)
    have ht := ih next hv (fun j => signs j.succ)
    simp only [LongTails.Algorithms.MonotoneHessianReuse.loop, id_eq, QueryPlan.eval_bind,
      counts_bind, Nat.cast_add]
    change delta p / (4 * p.H) * ((counts O (LongTails.Algorithms.MonotoneHessianReuse.step p st (signs 0)) 1 : ℝ) +
      (counts O (LongTails.Algorithms.MonotoneHessianReuse.loop p n next (fun j => signs j.succ)) 1 : ℝ)) + _ ≤ _
    nlinarith

lemma initial_hessian_bound (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (signs : Fin (stages p) → Block p) :
    (counts O (LongTails.Algorithms.MonotoneHessianReuse.plan p signs) 1 : ℝ) ≤
      1 + chargeFactor p * p.Δ / (delta p / (4 * p.H)) := by
  let initial : LongTails.Algorithms.MonotoneHessianReuse.State p :=
    ⟨⟨p.x0, f p.x0, _root_.gradient f p.x0⟩, none, false⟩
  have hi : StateValid p f (fderiv ℝ (_root_.gradient f)) initial :=
    ⟨⟨rfl, rfl⟩, fun snap hs => by simp [initial] at hs⟩
  have hh := loop_amortized p hp f hf hg hA hLip O hO hH (stages p) initial hi signs
  have hout := MonotoneHessianIteration.loop_invariant p hp f hf hg hA hLip O hO hH
    (stages p) initial hi (fun hs => by simp [initial] at hs) signs
  have hn := credit_nonneg p hp ((LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O)
  have hv := hout.1.faithful.1
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hHpos := hp.1
  have hε := hp.2.2.1
  have hC : 0 ≤ chargeFactor p := by unfold chargeFactor; positivity
  have hb := mul_le_mul_of_nonneg_left (hgap
    ((LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O).point.x) hC
  have hcred : credit p initial = delta p / (4 * p.H) := rfl
  rw [hcred] at hh
  change delta p / (4 * p.H) * _ + _ ≤ delta p / (4 * p.H) + chargeFactor p * (f p.x0 - _) at hh
  rw [hv] at hh
  simp only [LongTails.Algorithms.MonotoneHessianReuse.plan, counts, hO, readPoint,
    counts_map, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, zero_add]
  change (counts O (LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs) 1 : ℝ) ≤ _
  have hR : 0 < delta p / (4 * p.H) := by positivity
  apply (mul_le_mul_iff_right₀ hR).mp
  have he : (1 + chargeFactor p * p.Δ / (delta p / (4 * p.H))) * (delta p / (4 * p.H)) =
      delta p / (4 * p.H) + chargeFactor p * p.Δ := by field_simp
  rw [mul_comm (delta p / (4 * p.H)) (1 + chargeFactor p * p.Δ / (delta p / (4 * p.H))), he]
  nlinarith

end LongTails.Proofs.MonotoneHessianCost
