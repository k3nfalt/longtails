import LongTails.Algorithms.FullRangeTuned
import LongTails.Proofs.FullRangeExecution
import LongTails.Proofs.FullRangeCertificate
import LongTails.Proofs.SmoothBanachExecution
import LongTails.Proofs.GeneralizedLipschitzBurnin

open MeasureTheory

namespace LongTails.Proofs.FullRangeGlue

open OracleTemplate OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Algorithms.FullRangeTuned
open LongTails.Proofs.FullRangeInner LongTails.Proofs.FullRangeExecution
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params)
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open OracleTemplate.LocalHiddenConvex (ballProj)

variable (q : Params)

lemma to_of (s : LongTails.Algorithms.SmoothBanachAnchoring.State (anchorParams q)) :
    toState q (ofState q s) = s := rfl

lemma update_measurable :
    Measurable (fun w : St q × q.E => (cfg q).update w.1 w.2) := by
  have hslice (j k : ℕ) : Measurable (fun w : (q.E × q.E) × q.E =>
      ofState q (LongTails.Algorithms.SmoothBanachAnchoring.update (anchorParams q)
        ⟨j, k, w.1.1, w.1.2⟩ w.2)) := by
    unfold LongTails.Algorithms.SmoothBanachAnchoring.update ofState
    by_cases hj : j ≤ LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q)
    · by_cases hk : k + 1 < LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q)
      · simp only [hj, hk, ite_true]
        unfold LongTails.Algorithms.SmoothBanachAnchoring.picardStep
        fun_prop
      · simp only [hj, hk, ite_true, ite_false]
        unfold LongTails.Algorithms.SmoothBanachAnchoring.picardStep
        fun_prop
    · simp only [hj, ite_false]
      fun_prop
  have h2 : Measurable (fun w : ℕ × (ℕ × ((q.E × q.E) × q.E)) =>
      ofState q (LongTails.Algorithms.SmoothBanachAnchoring.update (anchorParams q)
        ⟨w.1, w.2.1, w.2.2.1.1, w.2.2.1.2⟩ w.2.2.2)) :=
    measurable_from_prod_countable_right fun j =>
      measurable_from_prod_countable_right fun k => hslice j k
  exact h2.comp (show Measurable (fun w : St q × q.E =>
    (w.1.1, (w.1.2.1, ((w.1.2.2.1, w.1.2.2.2), w.2)))) from by fun_prop)

section Hyp

variable {F : q.E → q.E} {G : q.E → Set q.E} {J : ℝ → q.E → q.E} (H : OpHyp F G J q.L q.ρ)
  (g : q.E → q.Ω → q.E) (hg : Measurable (Function.uncurry g))

include H hg in
lemma callAdv_measurable (hη : 0 < eta q) (hγ : 0 < gamma0 q) (hr : 0 ≤ radius q) (l : ℕ) :
    Measurable (fun w : St q × (ℕ → q.Ω) => callAdv J g (cfg q) w.1 l w.2) := by
  have hP : Measurable (ballProj q.x0 (radius q) : q.E → q.E) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro a b
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
        LongTails.Proofs.FullRangeClip.ballProj_nonexpansive q.x0 a b hr)).continuous.measurable
  have hy : Measurable (fun w : St q × (ℕ → q.Ω) => ballProj q.x0 (radius q) w.1.2.2.2) :=
    hP.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hp2 (k : ℕ) : Measurable (fun w : St q × (ℕ → q.Ω) =>
      innerPath J g (eta q) (gamma0 q) (n0 q) (ballProj q.x0 (radius q) w.1.2.2.2) k w.2) :=
    (LongTails.Proofs.FullRangeOperator.innerPath_joint_measurable H hη (n0 := n0 q) g hγ hg k).comp
      (hy.prodMk measurable_snd)
  have hest : Measurable (fun w : St q × (ℕ → q.Ω) =>
      estimator J g (eta q) (gamma0 q) (n0 q) (top q) (ballProj q.x0 (radius q) w.1.2.2.2) l w.2) := by
    unfold estimator
    by_cases hl : l = 0
    · simpa [hl] using hp2 (n0 q)
    · simp only [hl, ite_false]
      exact (hp2 _).add (((hp2 _).sub (hp2 _)).const_smul _)
  unfold callAdv
  exact (update_measurable q).comp (measurable_fst.prodMk ((hy.const_smul _).add (hest.const_smul _)))

lemma callAdv_dep (s : St q) (l : ℕ) (ξ ξ' : ℕ → q.Ω) (h : ∀ i < levelTime (cfg q).n0 l, ξ i = ξ' i) :
    callAdv J g (cfg q) s l ξ = callAdv J g (cfg q) s l ξ' := by
  have hp (k : ℕ) (hk : k ≤ levelTime (cfg q).n0 l) (x : q.E) :
      innerPath J g (cfg q).η (cfg q).γ0 (cfg q).n0 x k ξ =
        innerPath J g (cfg q).η (cfg q).γ0 (cfg q).n0 x k ξ' :=
    LongTails.Proofs.FullRangeCertificate.innerPath_dep g _ _ _ x k ξ ξ' (fun i hi => h i (by omega))
  unfold callAdv estimator
  by_cases hl : l = 0
  · simp only [hl, ite_true]
    rw [hp _ (by simpa [hl] using n0_le_levelTime (cfg q).n0 0)]
  · simp only [hl, ite_false]
    rw [hp _ (n0_le_levelTime _ _), hp _ le_rfl, hp _ (levelTime_le _ _ hl)]

noncomputable def gA : q.E → thetaType q → q.E :=
  LongTails.Proofs.FullRangeOperator.callEstimate J g (eta q) (gamma0 q) (tau q) (n0 q) (top q)
    q.x0 (radius q)

lemma iterate_ofState (K : ℕ) (s0 : LongTails.Algorithms.SmoothBanachAnchoring.State (anchorParams q))
    (θ : Fin K → thetaType q) :
    iterateSamples (LongTails.Proofs.FullRangeLaw.advTheta (top := top q) (callAdv J g (cfg q))) K
        (ofState q s0) θ =
      ofState q (iterateSamples (fun st ω => LongTails.Algorithms.SmoothBanachAnchoring.update
        (anchorParams q) st (gA q (J := J) g st.point ω)) K s0 θ) := by
  induction K generalizing s0 with
  | zero => rfl
  | succ K ih =>
      simp only [iterateSamples]
      exact ih _ _

lemma ideal_point (θext : ℕ → thetaType q) (hK : (LongTails.Algorithms.SmoothBanachAnchoring.levels
      (anchorParams q) + 1) * LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q) ≤ calls q) :
    (iterateSamples (LongTails.Proofs.FullRangeLaw.advTheta (top := top q) (callAdv J g (cfg q)))
        (calls q) (cfg q).init (fun i : Fin (calls q) => θext i)).2.2.2 =
      (LongTails.Algorithms.SmoothBanachAnchoring.epochState (anchorParams q) (gA q (J := J) g)
        (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1)
        (fun j i => θext (j * LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q) + i))).2.2 := by
  have h1 := iterate_ofState q (J := J) g (calls q) (LongTails.Algorithms.SmoothBanachAnchoring.initial (anchorParams q))
    (fun i : Fin (calls q) => θext i)
  change (iterateSamples _ (calls q) (ofState q _) _).2.2.2 = _
  rw [h1]
  have h2 := LongTails.Proofs.GeneralizedLipschitzBurnin.iterateSamples_eq_advance
    (fun st ω => LongTails.Algorithms.SmoothBanachAnchoring.update (anchorParams q) st
      (gA q (J := J) g st.point ω)) θext (calls q) 0
    (LongTails.Algorithms.SmoothBanachAnchoring.initial (anchorParams q))
  simp only [zero_add] at h2
  rw [h2]
  have h3 := LongTails.Proofs.SmoothBanachExecution.advance_padded (anchorParams q) (gA q (J := J) g) θext
    (by norm_num [anchorParams]) (calls q) hK
  exact h3

end Hyp

end LongTails.Proofs.FullRangeGlue
