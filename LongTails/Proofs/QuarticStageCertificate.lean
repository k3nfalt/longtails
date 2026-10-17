import LongTails.Proofs.QuarticStageTransition

namespace LongTails.Proofs.QuarticStageCertificate

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open LongTails.Proofs.QuarticStageEstimate
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma certificate_full (p : Parameters E) (x w : Point E)
    (hL : 0 < p.L) (hr : 0 < p.r) (hα : 0 ≤ p.α)
    (hq : p.q ≤ p.L * p.r ^ 2 / 16) (hx : value p x ≤ p.center.value)
    (hw : w.x = trialPoint p x)
    (hmodel : value p w ≤ value p x + ⟪gradient p x, w.x - x.x⟫ +
      p.L / 2 * ‖p.S (w.x - x.x)‖ ^ 2)
    (hno : ¬successful p w) :
    p.S w.x = gradientStep p.L (p.S x.x) (transformedGradient p.S (gradient p x)) ∧
    value p w ≤ value p x - ‖transformedGradient p.S (gradient p x)‖ ^ 2 / (2 * p.L) := by
  have hd := QuarticStageTrial.trial_descent p x w hL hr.le hw hmodel
  have hn : p.center.value - p.q < w.value := lt_of_not_ge (not_or.mp hno).1
  have hs : value p x ≤ p.center.value + ‖transformedGradient p.S (gradient p x)‖ * 0 := by simpa using hx
  have hf := QuarticStageTrial.trial_full p x w hL hr hα (by positivity : (0 : ℝ) ≤ p.r / 8) hq hw hs hd hn
  exact ⟨hf, QuarticStageTrial.full_step_descent p x w hL hf hmodel⟩

lemma certificate_geometry (p : Parameters E) (x w : Point E) {A τ : ℝ}
    (hL : 0 < p.L) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L) (hα : 0 < p.α)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hA₂ : A ^ 2 = 2 * p.q / p.μ) (hτ₂ : p.α * τ ^ 2 = p.q)
    (hx : value p x ≤ p.center.value) (hxr : ‖p.S (x.x - p.center.x)‖ ≤ A)
    (hfull : p.S w.x = gradientStep p.L (p.S x.x) (transformedGradient p.S (gradient p x)))
    (hd : value p w ≤ value p x - ‖transformedGradient p.S (gradient p x)‖ ^ 2 / (2 * p.L))
    (hno : ¬successful p w) :
    value p w ≤ p.center.value ∧ ‖p.S (w.x - p.center.x)‖ ≤ 2 * A ∧
      ‖w.x - p.center.x‖ ≤ τ := by
  have hn : p.center.value - p.q ≤ w.value := (lt_of_not_ge (not_or.mp hno).1).le
  have hraw : w.value ≤ value p w := by
    unfold value regularizedValue
    exact le_add_of_nonneg_right (by positivity)
  have hv : value p w ≤ p.center.value := by
    have hh : 0 ≤ ‖transformedGradient p.S (gradient p x)‖ ^ 2 / (2 * p.L) := by positivity
    linarith
  have hg : ‖transformedGradient p.S (gradient p x)‖ ^ 2 ≤ 2 * p.L * p.q := by
    have hh : ‖transformedGradient p.S (gradient p x)‖ ^ 2 / (2 * p.L) ≤ p.q := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 2 * p.L)).mp hh |>.trans_eq (mul_comm _ _)
  have hqeq : 2 * p.q = p.μ * A ^ 2 := by
    have hh := (eq_div_iff hμ.ne').mp hA₂
    nlinarith only [hh]
  have hgA : ‖transformedGradient p.S (gradient p x)‖ ≤ p.L * A := by
    have hh := mul_le_mul_of_nonneg_right hμL (sq_nonneg A)
    have hh' := mul_le_mul_of_nonneg_left hh hL.le
    rw [← hqeq] at hh'
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le hA)).mp (by nlinarith)
  have hstep : ‖p.S (w.x - x.x)‖ ≤ A := by
    rw [map_sub, hfull, gradientStep, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact (inv_mul_le_iff₀ hL).mpr hgA
  have hwr : ‖p.S (w.x - p.center.x)‖ ≤ 2 * A := by
    calc
      _ = ‖p.S (w.x - x.x) + p.S (x.x - p.center.x)‖ := by rw [← map_add]; congr 2; abel
      _ ≤ ‖p.S (w.x - x.x)‖ + ‖p.S (x.x - p.center.x)‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have he := GuardedMetricDescent.regularized_distance p.center.x w.x hv hn
  rw [← hτ₂] at he
  have he' := (mul_le_mul_iff_right₀ hα).mp he
  exact ⟨hv, hwr, (sq_le_sq₀ (norm_nonneg _) hτ).mp he'⟩

lemma certificate_estimate (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1) (hμ : 0 < p.μ)
    (hL : 0 < p.L) (w : Point E)
    (hs : ∀ plane ∈ st.history, supports p w plane.point)
    (hd : value p w ≤ value p st.accepted -
      ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 / (2 * p.L)) :
    ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 ≤
      2 * p.L * (1 - p.a) ^ k *
        (p.center.value - value p w + p.μ * ‖p.S (w.x - p.center.x)‖ ^ 2 / 2) := by
  obtain ⟨φ, hmin, hrep⟩ := hi.representation
  have hm : value p st.accepted ≤ estimate p st.history w := by
    rw [hrep]
    exact hmin.trans (le_add_of_nonneg_right (by positivity))
  have hs' := estimate_support p st.history w ha ha₁ hs
  rw [hi.history_length] at hs'
  apply GuardedAcceleratedGeometry.certificate_gradient hL hd hm
  nlinarith only [hs']

lemma cached_success (p : Parameters E) (f : E → ℝ) {A τ M C : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1) (hμ : 0 < p.μ)
    (hL : 0 < p.L) (hα : 0 < p.α) (hε : 0 < p.ε) (hM : 0 ≤ M)
    (hmetric : ∀ v : E, ‖p.S v‖ ^ 2 ≤ M * ‖v‖ ^ 2) (w : Point E)
    (hs : ∀ plane ∈ st.history, supports p w plane.point)
    (hd : value p w ≤ value p st.accepted -
      ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 / (2 * p.L))
    (hbracket : p.center.value - value p w + p.μ * ‖p.S (w.x - p.center.x)‖ ^ 2 / 2 ≤ C)
    (hdecay : M * (2 * p.L * (1 - p.a) ^ k * C) ≤ (p.ε / 2) ^ 2)
    (hq : p.q ≤ p.ε ^ 2 / (16 * p.α)) :
    successful p st.accepted := by
  have he := certificate_estimate p f hi ha ha₁ hμ hL w hs hd
  have hbound := mul_le_mul_of_nonneg_left hbracket
    (by positivity : 0 ≤ 2 * p.L * (1 - p.a) ^ k)
  have hg := GuardedMetricDescent.gradient_norm_bound p.S hmetric (gradient p st.accepted)
  have hsmall : ‖gradient p st.accepted‖ ≤ p.ε / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ p.ε / 2)).mp
    exact hg.trans ((mul_le_mul_of_nonneg_left (he.trans hbound) hM).trans hdecay)
  by_cases hlarge : p.ε < ‖st.accepted.gradient‖
  · left
    have hp := GuardedMetricDescent.small_regularized_progress hα hε p.center.x
      st.accepted.x st.accepted.gradient hi.accepted_value hlarge hsmall
    linarith
  · right
    exact le_of_not_gt hlarge

lemma certificate_invariant (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    {A τ : ℝ} {k : ℕ} (status : Status E)
    (hi : QuarticStageTransition.StatusInvariant p f A τ k status)
    (hgeometry : ∀ st : State E, Invariant p f A τ k st → ∀ w : Point E,
      Faithful f w → w.x = trialPoint p st.accepted → ¬successful p w →
      value p w ≤ p.center.value ∧ ‖p.S (w.x - p.center.x)‖ ≤ 2 * A ∧ ‖w.x - p.center.x‖ ≤ τ)
    (hcomplete : ∀ st : State E, Invariant p f A τ k st → ∀ w : Point E,
      Faithful f w → w.x = trialPoint p st.accepted → ¬successful p w →
      (∀ plane ∈ st.history, supports p w plane.point) → successful p st.accepted) :
    QuarticStageTransition.StatusInvariant p f A τ k ((certificate p status).eval g) ∧
      (∀ st, (certificate p status).eval g ≠ .running st) := by
  classical
  cases status with
  | finished x => exact ⟨hi, by intro st; simp [certificate, stopAfter, OracleTemplate.QueryPlan.eval]⟩
  | witness w => exact ⟨hi, by intro st; simp [certificate, stopAfter, OracleTemplate.QueryPlan.eval]⟩
  | running st =>
    change Invariant p f A τ k st at hi
    let w : Point E := ⟨trialPoint p st.accepted, f (trialPoint p st.accepted),
      _root_.gradient f (trialPoint p st.accepted)⟩
    have hw : Faithful f w := ⟨rfl, rfl⟩
    simp only [certificate, OracleTemplate.QueryPlan.eval, horacle, readPoint]
    split_ifs with hs
    · exact ⟨⟨hw, hs⟩, by intro st'; simp [OracleTemplate.QueryPlan.eval]⟩
    · change QuarticStageTransition.StatusInvariant p f A τ k
        (OracleTemplate.QueryPlan.eval g (match st.history.find? (fun plane => ¬supports p w plane.point) with
          | some plane => .done (.witness ⟨w, plane⟩)
          | none => .done (.finished st.accepted))) ∧ _
      cases he : st.history.find? (fun plane => ¬supports p w plane.point) with
      | none =>
        have hall : ∀ plane ∈ st.history, supports p w plane.point := by
          intro plane hp
          have hh := List.find?_eq_none.mp he plane hp
          simpa using hh
        exact ⟨⟨hi.accepted_faithful, hcomplete st hi w hw rfl hs hall⟩, by intro st'; simp [OracleTemplate.QueryPlan.eval]⟩
      | some plane =>
        have hp := List.mem_of_find?_eq_some he
        have hf : ¬supports p w plane.point := by
          have hh := List.find?_some he
          simpa using hh
        obtain ⟨hv, hr, hd⟩ := hgeometry st hi w hw rfl hs
        have hwit : QuarticStageTransition.WitnessInvariant p f A τ ⟨w, plane⟩ :=
          ⟨hi.history_geometry plane hp, hw, hv, (lt_of_not_ge (not_or.mp hs).1).le, hr, hd, hf⟩
        exact ⟨hwit, by intro st'; simp [OracleTemplate.QueryPlan.eval]⟩

end LongTails.Proofs.QuarticStageCertificate
