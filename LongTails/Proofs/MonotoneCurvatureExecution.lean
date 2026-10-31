import LongTails.Proofs.MonotoneCurvatureGeometry
import LongTails.Proofs.QuarticStageTransition
import LongTails.Proofs.MonotoneCurvatureCertificate
import LongTails.Proofs.MonotoneCurvatureTuning

namespace LongTails.Proofs.MonotoneCurvatureExecution

open OracleTemplate LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def FinishedRadius (p : Parameters E) (R : ℝ) : Status E → Prop
  | .finished x => ‖x.x - p.center.x‖ ≤ R
  | _ => True

lemma finished_radius_step (p : Parameters E) (f : E → ℝ) (O : Fin 2 × E → Reply E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    {A τ b : ℝ} {k : ℕ} (status : Status E) (hi : StatusInvariant p f A τ k status)
    (hb : 0 < b) (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2)
    (ha : 0 ≤ p.a) (hL : 0 < p.L) (hr : 0 ≤ p.r)
    (hradius : FinishedRadius p ((A + p.r / 2) / b) status) :
    FinishedRadius p ((A + p.r / 2) / b) ((step p status).eval O) := by
  classical
  cases status with
  | finished x => simpa [step, stopAfter, QueryPlan.eval, FinishedRadius] using hradius
  | witness w => simp [step, stopAfter, QueryPlan.eval, FinishedRadius]
  | running st =>
    let yx := p.S.symm (extrapolate p.a (p.S st.accepted.x) st.z)
    let y : Point E := ⟨yx, f yx, _root_.gradient f yx⟩
    have hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z := by simp [y, yx]
    have hp := query_plane_geometry p f hi ha y hy ⟨rfl, rfl⟩
    have hyr : ‖y.x - p.center.x‖ ≤ (A + p.r / 2) / b := by
      have h := MonotoneCurvatureGeometry.inverse_radius p.S hb hS (p.S (y.x - p.center.x))
      simp only [ContinuousLinearEquiv.symm_apply_apply] at h
      exact h.trans (div_le_div_of_nonneg_right (hp.point_radius.trans (by linarith)) hb.le)
    have htr := MonotoneCurvatureGeometry.trial_distance p hb hS hL hr y hp.point_radius
    simp only [step, QueryPlan.eval, hO, readPoint]
    split
    · exact hyr
    · split
      · trivial
      · split
        · trivial
        · simp only [QueryPlan.eval, hO]
          split
          · exact htr
          · trivial

lemma finished_radius_loop (p : Parameters E) (f : E → ℝ) (O : Fin 2 × E → Reply E)
    {A τ R : ℝ}
    (hstep : ∀ k status, StatusInvariant p f A τ k status →
      StatusInvariant p f A τ (k + 1) ((step p status).eval O))
    (hradius : ∀ k status, StatusInvariant p f A τ k status → FinishedRadius p R status →
      FinishedRadius p R ((step p status).eval O))
    (n k : ℕ) (status : Status E) (hi : StatusInvariant p f A τ k status)
    (hb : FinishedRadius p R status) :
    FinishedRadius p R ((loop p n status).eval O) := by
  induction n generalizing k status with
  | zero => simpa [loop, QueryPlan.eval] using hb
  | succ n ih =>
    simp only [loop, id_eq, QueryPlan.eval_bind]
    exact ih (k + 1) ((step p status).eval O) (hstep k status hi) (hradius k status hi hb)

lemma finished_radius_certificate (p : Parameters E) (O : Fin 2 × E → Reply E)
    {f : E → ℝ} {A τ b : ℝ} {k : ℕ} (status : Status E)
    (hi : StatusInvariant p f A τ k status)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hb : 0 < b) (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2)
    (hL : 0 < p.L) (hr : 0 ≤ p.r) (hτ : τ ≤ (A + p.r / 2) / b)
    (hradius : FinishedRadius p ((A + p.r / 2) / b) status) :
    FinishedRadius p ((A + p.r / 2) / b) ((certificate p status).eval O) := by
  classical
  cases status with
  | finished x => simpa [certificate, stopAfter, QueryPlan.eval, FinishedRadius] using hradius
  | witness w => simp [certificate, stopAfter, QueryPlan.eval, FinishedRadius]
  | running st =>
    change Invariant p f A τ k st at hi
    have ht := MonotoneCurvatureGeometry.trial_distance p hb hS hL hr st.accepted hi.accepted_radius
    simp only [certificate, QueryPlan.eval, hO, readPoint]
    split
    · exact ht
    · split
      · trivial
      · exact hi.accepted_distance.trans hτ

def Completion (p : Parameters E) (f : E → ℝ) (A τ G : ℝ) : Status E → Prop
  | .running _ => False
  | .witness w => WitnessInvariant p f A τ w
  | .finished x => Faithful f x ∧ (successful p x ∨
      value p x ≤ p.center.value ∧ ‖x.x - p.center.x‖ ≤ τ ∧
        ‖transformedGradient p.S (gradient p x)‖ ^ 2 ≤ G)

lemma certificate_completion (p : Parameters E) (f : E → ℝ) (O : Fin 2 × E → Reply E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    {A τ G : ℝ} {k : ℕ} (status : Status E) (hi : StatusInvariant p f A τ k status)
    (hgeometry : ∀ st : State E, Invariant p f A τ k st → ∀ w : Point E,
      Faithful f w → w.x = trialPoint p st.accepted → ¬successful p w →
      value p w ≤ p.center.value ∧ ‖p.S (w.x - p.center.x)‖ ≤ 2 * A ∧ ‖w.x - p.center.x‖ ≤ τ)
    (hterminal : ∀ st : State E, Invariant p f A τ k st → ∀ w : Point E,
      Faithful f w → w.x = trialPoint p st.accepted → ¬successful p w →
      (∀ plane ∈ st.history, supports p w plane.point) →
        ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 ≤ G) :
    Completion p f A τ G ((certificate p status).eval O) := by
  classical
  cases status with
  | finished x =>
    have hh : Faithful f x ∧ successful p x := hi
    simpa [certificate, stopAfter, QueryPlan.eval, Completion] using ⟨hh.1, Or.inl hh.2⟩
  | witness w => simpa [certificate, stopAfter, QueryPlan.eval, Completion, StatusInvariant] using hi
  | running st =>
    change Invariant p f A τ k st at hi
    let w : Point E := ⟨trialPoint p st.accepted, f (trialPoint p st.accepted),
      _root_.gradient f (trialPoint p st.accepted)⟩
    have hw : Faithful f w := ⟨rfl, rfl⟩
    simp only [certificate, QueryPlan.eval, hO, readPoint]
    split_ifs with hs
    · exact ⟨hw, Or.inl hs⟩
    · change Completion p f A τ G (QueryPlan.eval O
        (match st.history.find? (fun plane => ¬supports p w plane.point) with
          | some plane => .done (.witness ⟨w, plane⟩)
          | none => .done (.finished st.accepted)))
      cases he : st.history.find? (fun plane => ¬supports p w plane.point) with
      | none =>
        have hall : ∀ plane ∈ st.history, supports p w plane.point := by
          intro plane hp
          have hh := List.find?_eq_none.mp he plane hp
          simpa using hh
        exact ⟨hi.accepted_faithful, Or.inr ⟨hi.accepted_value, hi.accepted_distance,
          hterminal st hi w hw rfl hs hall⟩⟩
      | some plane =>
        have hp := List.mem_of_find?_eq_some he
        have hf : ¬supports p w plane.point := by
          have hh := List.find?_some he
          simpa using hh
        obtain ⟨hv, hr, hd⟩ := hgeometry st hi w hw rfl hs
        exact ⟨hi.history_geometry plane hp, hw, hv,
          (lt_of_not_ge (not_or.mp hs).1).le, hr, hd, hf⟩

lemma tuned_loop_invariant (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (f : E → ℝ)
    (O : Fin 2 × E → Reply E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hc : Faithful f c)
    (hmodel : let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t;
      ∀ y next : Point E, Faithful f y → Faithful f next →
      ‖S (y.x - c.x)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t → next.x = trialPoint p y →
      value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
        p.L / 2 * ‖S (next.x - y.x)‖ ^ 2) (n : ℕ) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    StatusInvariant p f (MonotoneCurvatureTuning.metricRadius H γ t)
      (MonotoneCurvatureTuning.distanceScale H γ) n
      ((loop p n (.running ⟨c, c, S c.x, []⟩)).eval O) := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  let A := MonotoneCurvatureTuning.metricRadius H γ t
  let τ := MonotoneCurvatureTuning.distanceScale H γ
  have ht0 : 0 < t := by linarith
  have hscale := MonotoneCurvatureTuning.scales S c hH hγ ht
  have hA : 0 ≤ A := (MonotoneCurvatureTuning.metricRadius_pos hH hγ ht0).le
  have hτ : 0 ≤ τ := (MonotoneCurvatureTuning.distanceScale_pos hH hγ).le
  have hq : 0 ≤ p.q := hscale.2.2.2.2.2.le
  have hstep (k : ℕ) (status : Status E) (hi : StatusInvariant p f A τ k status) :
      StatusInvariant p f A τ (k + 1) ((step p status).eval O) := by
    apply step_invariant p f O hO status hi hc hscale.1 hscale.2.1 hscale.2.2.1
      (by norm_num [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters]) hγ
      hscale.2.2.2.2.1 hA hτ hq
      (MonotoneCurvatureTuning.radius_identity S c hγ.le ht0.ne') rfl
      (MonotoneCurvatureTuning.radius_clipping S c H γ t).le
      (MonotoneCurvatureTuning.progress_clipping S c hH hγ ht)
      (MonotoneCurvatureTuning.acceleration S c H γ t) hmodel
  have hi : StatusInvariant p f A τ 0 (.running ⟨c, c, S c.x, []⟩) :=
    initial_invariant p f hc hA hτ hq
  simpa only [zero_add] using loop_invariant p f O hstep n 0 _ hi

lemma tuned_loop_radius (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (f : E → ℝ)
    (O : Fin 2 × E → Reply E) (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hc : Faithful f c)
    (hmetric : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hmodel : let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t;
      ∀ y next : Point E, Faithful f y → Faithful f next →
      ‖S (y.x - c.x)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t → next.x = trialPoint p y →
      value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
        p.L / 2 * ‖S (next.x - y.x)‖ ^ 2) (n : ℕ) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    FinishedRadius p (160 * MonotoneCurvatureTuning.distanceScale H γ)
      ((loop p n (.running ⟨c, c, S c.x, []⟩)).eval O) := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  let A := MonotoneCurvatureTuning.metricRadius H γ t
  let τ := MonotoneCurvatureTuning.distanceScale H γ
  have ht0 : 0 < t := by linarith
  have hscale := MonotoneCurvatureTuning.scales S c hH hγ ht
  have hA : 0 ≤ A := (MonotoneCurvatureTuning.metricRadius_pos hH hγ ht0).le
  have hτ : 0 ≤ τ := (MonotoneCurvatureTuning.distanceScale_pos hH hγ).le
  have hq : 0 ≤ p.q := hscale.2.2.2.2.2.le
  have hstep (k : ℕ) (status : Status E) (hi : StatusInvariant p f A τ k status) :
      StatusInvariant p f A τ (k + 1) ((step p status).eval O) := by
    apply step_invariant p f O hO status hi hc hscale.1 hscale.2.1 hscale.2.2.1
      (by norm_num [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters]) hγ
      hscale.2.2.2.2.1 hA hτ hq
      (MonotoneCurvatureTuning.radius_identity S c hγ.le ht0.ne') rfl
      (MonotoneCurvatureTuning.radius_clipping S c H γ t).le
      (MonotoneCurvatureTuning.progress_clipping S c hH hγ ht)
      (MonotoneCurvatureTuning.acceleration S c H γ t) hmodel
  have hi : StatusInvariant p f A τ 0 (.running ⟨c, c, S c.x, []⟩) :=
    initial_invariant p f hc hA hτ hq
  have hb : 0 < t * Real.sqrt γ := mul_pos ht0 (Real.sqrt_pos.mpr hγ)
  have hS (v : E) : (t * Real.sqrt γ) ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hγ.le]
    exact hmetric v
  have hh := finished_radius_loop p f O hstep
    (fun k status hs hr => finished_radius_step p f O hO status hs hb hS hscale.1
      (by norm_num [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters])
      hscale.2.2.2.2.1.le hr) n 0 _ hi (by trivial)
  change FinishedRadius p ((MonotoneCurvatureTuning.metricRadius H γ t +
    (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t).r / 2) / (t * Real.sqrt γ)) _ at hh
  rw [MonotoneCurvatureTuning.query_radius S c hγ ht0] at hh
  exact hh

lemma finish_characterization (p : Parameters E) (f : E → ℝ) (O : Fin 2 × E → Reply E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    {A τ G R : ℝ} (status : Status E) (hi : Completion p f A τ G status)
    (hr : FinishedRadius p R status) :
    let out := (LongTails.Algorithms.MonotoneCurvatureStage.finish p status).eval O
    Faithful f out ∧
      ((∃ w, WitnessInvariant p f A τ w ∧
          out.x = LongTails.Algorithms.MonotoneCurvatureStage.witnessPoint p w) ∨
        (successful p out ∧ ‖out.x - p.center.x‖ ≤ R) ∨
        ∃ x, Faithful f x ∧ value p x ≤ p.center.value ∧ ‖x.x - p.center.x‖ ≤ τ ∧
          ‖transformedGradient p.S (gradient p x)‖ ^ 2 ≤ G ∧
          out.x = LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint p.S x) := by
  classical
  cases status with
  | running st => exact False.elim hi
  | witness w =>
    simp only [LongTails.Algorithms.MonotoneCurvatureStage.finish, QueryPlan.eval, hO, readPoint]
    exact ⟨⟨rfl, rfl⟩, Or.inl ⟨w, hi, rfl⟩⟩
  | finished x =>
    change Faithful f x ∧ (successful p x ∨ _) at hi
    simp only [LongTails.Algorithms.MonotoneCurvatureStage.finish]
    split
    · rename_i hs
      simp only [QueryPlan.eval]
      exact ⟨hi.1, Or.inr (Or.inl ⟨hs, hr⟩)⟩
    · rename_i hs
      simp only [QueryPlan.eval, hO, readPoint]
      obtain ⟨hv, hr, hg⟩ := hi.2.resolve_left hs
      exact ⟨⟨rfl, rfl⟩, Or.inr (Or.inr ⟨x, hi.1, hv, hr, hg, rfl⟩)⟩

end LongTails.Proofs.MonotoneCurvatureExecution
