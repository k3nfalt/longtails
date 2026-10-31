import LongTails.Proofs.MonotoneCurvatureExecution
import LongTails.Proofs.MonotoneCurvatureModel
import LongTails.Proofs.MonotoneCurvatureWitness
import LongTails.Proofs.ReshufflingExecution

namespace LongTails.Proofs.MonotoneCurvatureStageGuarantee

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure LocalMetric (A : E → E →L[ℝ] E) (S : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (c : E) (H γ t : ℝ) : Prop where
  symmetric : B.toLinearMap.IsSymmetric
  factor : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫
  lower : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2
  upper : ∀ x, ‖x - c‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ →
    ∀ v, ⟪v, A x v⟫ ≤ ‖S v‖ ^ 2 - (t ^ 2 * γ) * ‖v‖ ^ 2
  error : ∀ x, ‖x - c‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ →
    ‖B - A x‖ ≤ 6 * (t ^ 2 * γ)

omit [FiniteDimensional ℝ E] in
lemma metric_ball_distance (S : E ≃L[ℝ] E) (c x : E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hmetric : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hx : ‖S (x - c)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t) :
    ‖x - c‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hb : 0 < t * Real.sqrt γ := mul_pos ht0 hs
  have hsq : (t * Real.sqrt γ) ^ 2 = t ^ 2 * γ := by rw [mul_pow, Real.sq_sqrt hγ.le]
  have hn := MonotoneCurvatureGeometry.inverse_radius S hb
    (fun v => by rw [hsq]; exact hmetric v) (S (x - c))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hn
  have he : MonotoneCurvatureTuning.metricRadius H γ t / (t * Real.sqrt γ) =
      32 * MonotoneCurvatureTuning.distanceScale H γ := by
    unfold MonotoneCurvatureTuning.metricRadius
    field_simp
  have hh := hn.trans (div_le_div_of_nonneg_right hx hb.le)
  rw [he] at hh
  have hτ := MonotoneCurvatureTuning.distanceScale_pos hH hγ
  linarith

lemma local_trial_model {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (c : Point E)
    (hlocal : LocalMetric A S B c.x H γ t) (x y : Point E)
    (hx : Faithful f x) (hy : Faithful f y)
    (hr : ‖S (x.x - c.x)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t)
    (hpoint : y.x = trialPoint (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) x) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    value p y ≤ value p x + ⟪gradient p x, y.x - x.x⟫ + p.L / 2 * ‖S (y.x - x.x)‖ ^ 2 := by
  apply MonotoneCurvatureModel.tuned_trial_model hH hγ ht hf hg hLip S c hlocal.lower
    _ x y hx.1 hx.2 hy.1 hr hpoint
  intro z hz v
  exact (hlocal.upper z (metric_ball_distance S c.x z hH hγ ht hlocal.lower hz) v).trans
    (sub_le_self _ (by positivity))

omit [FiniteDimensional ℝ E] in
lemma local_comparison (A : E → E →L[ℝ] E) (S : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (c x : E) {H γ t : ℝ} (hlocal : LocalMetric A S B c H γ t)
    (hx : ‖x - c‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ) (v : E) :
    ‖S v‖ ^ 2 ≤ ⟪v, A x v⟫ + 6 * (t ^ 2 * γ) * ‖v‖ ^ 2 := by
  have he := hlocal.error x hx
  have hn := ((B - A x).le_opNorm v).trans (mul_le_mul_of_nonneg_right he (norm_nonneg v))
  have hi := real_inner_le_norm v ((B - A x) v)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  simp only [sub_apply, inner_sub_right] at hi hm
  rw [hlocal.factor]
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma local_center_comparison (A : E → E →L[ℝ] E) (S : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (c : E) {H γ t : ℝ} (hH : 0 < H) (hγ : 0 < γ)
    (hlocal : LocalMetric A S B c H γ t) (v : E) :
    ‖S v‖ ^ 2 ≤ ⟪v, A c v⟫ + 6 * (t ^ 2 * γ) * ‖v‖ ^ 2 := by
  have hτ := MonotoneCurvatureTuning.distanceScale_pos hH hγ
  have he := hlocal.error c (by simp; positivity)
  have hn := ((B - A c).le_opNorm v).trans (mul_le_mul_of_nonneg_right he (norm_nonneg v))
  have hi := real_inner_le_norm v ((B - A c) v)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  simp only [sub_apply, inner_sub_right] at hi hm
  rw [hlocal.factor]
  nlinarith

lemma local_correction {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t ε : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (hε : γ ^ 2 = H * ε)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (c x : Point E)
    (hlocal : LocalMetric A S B c.x H γ t) (hx : Faithful f x)
    (hr : ‖x.x - c.x‖ ≤ MonotoneCurvatureTuning.distanceScale H γ)
    (hdual : let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t;
      ‖LongTails.Algorithms.GuardedMetricAcceleration.transformedGradient S (gradient p x)‖ ^ 2 ≤ p.q / t ^ 2) :
    let y := LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint S x
    ‖_root_.gradient f y‖ ≤ ε ∧ f y ≤ f x.x ∧
      ‖y - c.x‖ ≤ 4 * MonotoneCurvatureTuning.distanceScale H γ := by
  have hτ := MonotoneCurvatureTuning.distanceScale_pos hH hγ
  have hxball : ‖x.x - c.x‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ := by linarith
  have hstep := MonotoneCurvatureCertificate.tuned_correction_distance S c x hH hγ ht hlocal.lower hr hdual
  have hupper (v : E) : ⟪v, A x.x v⟫ ≤ ⟪v, B v⟫ - (t ^ 2 * γ) * ‖v‖ ^ 2 := by
    rw [← hlocal.factor]
    exact hlocal.upper x.x hxball v
  obtain ⟨hgrad, hvalue, hdist⟩ := MonotoneCurvatureCertificate.correction_guarantee hH hγ ht hε
    hf hg hLip S B x hx.2 hlocal.symmetric hlocal.factor hlocal.lower hupper
    (hlocal.error x.x hxball) hstep
  refine ⟨hgrad, hvalue, ?_⟩
  have hh := norm_sub_le
    (LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint S x - x.x) (c.x - x.x)
  rw [sub_sub_sub_cancel_right, norm_sub_rev c.x x.x] at hh
  linarith

lemma plan_characterization {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (c : Point E) (hc : Faithful f c)
    (hlocal : LocalMetric A S B c.x H γ t)
    (O : Fin 2 × E → Reply E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x)) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    let out := (LongTails.Algorithms.MonotoneCurvatureStage.plan p
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon t)).eval O
    Faithful f out ∧
      ((∃ w, WitnessInvariant p f (MonotoneCurvatureTuning.metricRadius H γ t)
          (MonotoneCurvatureTuning.distanceScale H γ) w ∧
          out.x = LongTails.Algorithms.MonotoneCurvatureStage.witnessPoint p w) ∨
        (successful p out ∧ ‖out.x - c.x‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale H γ) ∨
        ∃ x, Faithful f x ∧ value p x ≤ c.value ∧
          ‖x.x - c.x‖ ≤ MonotoneCurvatureTuning.distanceScale H γ ∧
          ‖LongTails.Algorithms.GuardedMetricAcceleration.transformedGradient S (gradient p x)‖ ^ 2 ≤ p.q / t ^ 2 ∧
          out.x = LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint S x) := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  let n := LongTails.Algorithms.MonotoneCurvatureStage.horizon t
  let initial := Status.running (State.mk c c (S c.x) [])
  have hmodel := local_trial_model hH hγ ht hf hg hLip S B c hlocal
  have hi := MonotoneCurvatureExecution.tuned_loop_invariant S c hH hγ ht f O hO hc hmodel n
  have hterminal := MonotoneCurvatureCertificate.tuned_terminal S c hH hγ ht f
  have hcompletion := MonotoneCurvatureExecution.certificate_completion p f O hO
    ((loop p n initial).eval O) hi
    (fun st hs w hw hp hn => by
      have hh := hterminal st w hs hp hn (hmodel st.accepted w hs.accepted_faithful hw hs.accepted_radius hp)
      exact ⟨hh.1, hh.2.1, hh.2.2.1⟩)
    (fun st hs w hw hp hn hall => by
      have hh := hterminal st w hs hp hn (hmodel st.accepted w hs.accepted_faithful hw hs.accepted_radius hp)
      exact hh.2.2.2 hall)
  have ht0 : 0 < t := by linarith
  have hb : 0 < t * Real.sqrt γ := mul_pos ht0 (Real.sqrt_pos.mpr hγ)
  have hS (v : E) : (t * Real.sqrt γ) ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hγ.le]
    exact hlocal.lower v
  have hlr := MonotoneCurvatureExecution.tuned_loop_radius S c hH hγ ht f O hO hc hlocal.lower hmodel n
  have hrad := MonotoneCurvatureTuning.query_radius (H := H) S c hγ ht0
  have hr := MonotoneCurvatureExecution.finished_radius_certificate p O _ hi hO hb hS
    (by norm_num [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters])
    (MonotoneCurvatureTuning.scales S c hH hγ ht).2.2.2.2.1.le
    (by rw [hrad]; have hh := MonotoneCurvatureTuning.distanceScale_pos hH hγ; linarith)
    (by rw [hrad]; exact hlr)
  rw [hrad] at hr
  have hout := MonotoneCurvatureExecution.finish_characterization p f O hO _ hcompletion hr
  simpa only [LongTails.Algorithms.MonotoneCurvatureStage.plan,
    OracleTemplate.RandomReshuffling.eval_cast, OracleTemplate.QueryPlan.eval_bind, initial, p, n,
    LongTails.Algorithms.MonotoneCurvatureStage.parameters] using hout

lemma stage_guarantee {f : E → ℝ} {A : E → E →L[ℝ] E} {H γ t ε : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (hε : γ ^ 2 = H * ε)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (c : Point E) (hc : Faithful f c)
    (hlocal : LocalMetric A S B c.x H γ t)
    (O : Fin 2 × E → Reply E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x)) :
    let τ := MonotoneCurvatureTuning.distanceScale H γ
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    let out := (LongTails.Algorithms.MonotoneCurvatureStage.plan p
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon t)).eval O
    Faithful f out ∧
      ((out.value ≤ c.value - γ * (γ / (1024 * H)) ^ 2 / 3 ∧
          ‖out.x - c.x‖ = γ / (1024 * H)) ∨
        (out.value ≤ c.value - γ * τ ^ 2 ∧ ‖out.x - c.x‖ ≤ 160 * τ) ∨
        (out.value ≤ c.value ∧ ‖_root_.gradient f out.x‖ ≤ ε ∧ ‖out.x - c.x‖ ≤ 4 * τ)) := by
  dsimp only
  obtain ⟨hout, hw | hs | hterminal⟩ := plan_characterization hH hγ ht hf hg hLip S B c hc hlocal O hO
  · refine ⟨hout, Or.inl ?_⟩
    obtain ⟨w, hw, he⟩ := hw
    have hcurv := MonotoneCurvatureWitness.center_curvature hH hγ ht hf hg hLip S c w hw
      (local_center_comparison A S B c.x hH hγ hlocal)
    have hh := MonotoneCurvatureWitness.escape_descent (t := t) hH hγ hf hg hLip S c w hc hcurv
    rw [hout.1, he]
    exact hh
  · refine ⟨hout, Or.inr (Or.inl ⟨?_, hs.2⟩)⟩
    rcases hs.1 with hd | hg
    · exact hd
    · have hn := norm_nonneg (LongTails.Algorithms.MonotoneCurvatureStage.plan
        (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t)
        (LongTails.Algorithms.MonotoneCurvatureStage.horizon t) |>.eval O).gradient
      change _ ≤ -1 at hg
      linarith
  · refine ⟨hout, Or.inr (Or.inr ?_)⟩
    obtain ⟨x, hx, hv, hr, hgx, he⟩ := hterminal
    obtain ⟨hgrad, hval, hdist⟩ := local_correction hH hγ ht hε hf hg hLip S B c x hlocal hx hr hgx
    have hxval : f x.x ≤ c.value := by
      change x.value + γ * ‖x.x - c.x‖ ^ 2 ≤ c.value at hv
      rw [hx.1] at hv
      nlinarith [mul_nonneg hγ.le (sq_nonneg ‖x.x - c.x‖)]
    rw [hout.1, he]
    exact ⟨hval.trans hxval, hgrad, hdist⟩

end LongTails.Proofs.MonotoneCurvatureStageGuarantee
