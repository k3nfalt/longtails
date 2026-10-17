import LongTails.Proofs.QuarticStageEnergy
import LongTails.Proofs.QuarticWitnessEnergy
import LongTails.Proofs.ReshufflingExecution

namespace LongTails.Proofs.QuarticStageGuarantee

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open LongTails.Proofs.QuarticStageTransition
open LongTails.Proofs.QuarticStageEnergy
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Hypotheses (p : Parameters E) (f : E → ℝ) (n : ℕ) where
  A : ℝ
  τ : ℝ
  β : ℝ
  M : ℝ
  L₃ : ℝ
  Δ : ℝ
  smooth : ContDiff ℝ 3 f
  third_lipschitz : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
    fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L₃ * ‖x - y‖
  third_nonneg : 0 ≤ L₃
  gap : ∀ x, p.center.value - f x ≤ Δ
  center_faithful : Faithful f p.center
  a_nonneg : 0 ≤ p.a
  a_le_one : p.a ≤ 1
  mu_pos : 0 < p.μ
  smoothness_pos : 0 < p.L
  mu_le_smoothness : p.μ ≤ p.L
  alpha_pos : 0 < p.α
  radius_pos : 0 < p.r
  epsilon_pos : 0 < p.ε
  beta_pos : 0 < β
  metric_nonneg : 0 ≤ M
  A_nonneg : 0 ≤ A
  tau_nonneg : 0 ≤ τ
  q_nonneg : 0 ≤ p.q
  A_square : A ^ 2 = 2 * p.q / p.μ
  tau_square : p.α * τ ^ 2 = p.q
  A_guard : A ≤ p.r / 8
  q_guard : p.q ≤ p.L * p.r ^ 2 / 16
  acceleration : p.a ^ 2 * p.L = p.μ
  mu_small : p.μ ≤ 1 / 8
  mu_beta : p.μ * β ≤ p.α / 64
  interpolation_scale : 384 * L₃ * τ ^ 4 ≤ p.q
  witness_scale : 48 * L₃ * τ ^ 2 ≤ p.α / 4
  escape_small : L₃ * p.η ^ 2 ≤ p.α / 16
  escape_decrease : 15 * p.q ≤ p.α * p.η ^ 2 / 4
  escape_energy : p.μ * (8 * A ^ 2 + 40 * β * p.η ^ 2) ≤ 256 * p.q
  accuracy_scale : p.q ≤ p.ε ^ 2 / (16 * p.α)
  metric_upper : ∀ v : E, ‖p.S v‖ ^ 2 ≤ M * ‖v‖ ^ 2
  decay : M * (2 * p.L * (1 - p.a) ^ n * (Δ + 4 * p.q)) ≤ (p.ε / 2) ^ 2
  model : ∀ y next : Point E, Faithful f y → Faithful f next →
    ‖p.S (y.x - p.center.x)‖ ≤ A → next.x = trialPoint p y →
    value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
      p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2
  lower : ∀ u v : E, ‖p.S (u - p.center.x)‖ ≤ 2 * A → ‖p.S (v - p.center.x)‖ ≤ A →
    7 / 16 * ‖p.S (u - v)‖ ^ 2 - 4 * β * ‖u - v‖ ^ 2 ≤
      f u - f v - ⟪_root_.gradient f v, u - v⟫

lemma A_square_mul (p : Parameters E) (f : E → ℝ) {n : ℕ} (h : Hypotheses p f n) :
    p.μ * h.A ^ 2 = 2 * p.q := by
  have hh := (eq_div_iff h.mu_pos.ne').mp h.A_square
  nlinarith only [hh]

lemma certificate_geometry (p : Parameters E) (f : E → ℝ) {n : ℕ} (h : Hypotheses p f n)
    (st : State E) (hi : Invariant p f h.A h.τ n st) (w : Point E) (hw : Faithful f w)
    (hpoint : w.x = trialPoint p st.accepted) (hno : ¬successful p w) :
    value p w ≤ p.center.value ∧ ‖p.S (w.x - p.center.x)‖ ≤ 2 * h.A ∧ ‖w.x - p.center.x‖ ≤ h.τ := by
  have hh := QuarticStageCertificate.certificate_full p st.accepted w h.smoothness_pos h.radius_pos
    h.alpha_pos.le h.q_guard hi.accepted_value hpoint
    (h.model st.accepted w hi.accepted_faithful hw hi.accepted_radius hpoint) hno
  exact QuarticStageCertificate.certificate_geometry p st.accepted w h.smoothness_pos h.mu_pos
    h.mu_le_smoothness h.alpha_pos h.A_nonneg h.tau_nonneg h.A_square h.tau_square
    hi.accepted_value hi.accepted_radius hh.1 hh.2 hno

lemma certificate_complete (p : Parameters E) (f : E → ℝ) {n : ℕ} (h : Hypotheses p f n)
    (st : State E) (hi : Invariant p f h.A h.τ n st) (w : Point E) (hw : Faithful f w)
    (hpoint : w.x = trialPoint p st.accepted) (hno : ¬successful p w)
    (hs : ∀ plane ∈ st.history, supports p w plane.point) : successful p st.accepted := by
  have hh := QuarticStageCertificate.certificate_full p st.accepted w h.smoothness_pos h.radius_pos
    h.alpha_pos.le h.q_guard hi.accepted_value hpoint
    (h.model st.accepted w hi.accepted_faithful hw hi.accepted_radius hpoint) hno
  have hg := certificate_geometry p f h st hi w hw hpoint hno
  have hgap : p.center.value - value p w ≤ h.Δ := by
    have hraw : f w.x ≤ value p w := by
      rw [← hw.1]
      unfold value regularizedValue
      exact le_add_of_nonneg_right (mul_nonneg h.alpha_pos.le (sq_nonneg _))
    linarith [h.gap w.x]
  have hr := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hg.2.1 2) h.mu_pos.le
  have hbracket : p.center.value - value p w + p.μ * ‖p.S (w.x - p.center.x)‖ ^ 2 / 2 ≤ h.Δ + 4 * p.q := by
    have he := A_square_mul p f h
    nlinarith only [hgap, hr, he]
  exact QuarticStageCertificate.cached_success p f hi h.a_nonneg h.a_le_one h.mu_pos h.smoothness_pos
    h.alpha_pos h.epsilon_pos h.metric_nonneg h.metric_upper w hs hh.2 hbracket h.decay h.accuracy_scale

lemma witness_progress (p : Parameters E) (f : E → ℝ) {n : ℕ} (h : Hypotheses p f n)
    (w : Witness E) (hi : WitnessInvariant p f h.A h.τ w) :
    ∃ i : Fin 6, f (candidates p w i) ≤ p.center.value - p.q := by
  apply QuarticWitnessValues.candidate_progress p f w
  intro hh ht
  have hv := QuarticWitnessValues.plane_value_bound p f hi.plane_geometry h.smooth h.third_nonneg
    h.alpha_pos.le h.q_nonneg h.a_nonneg h.a_le_one h.third_lipschitz hh ht h.interpolation_scale
  exact QuarticWitnessValues.witness_escape p f hi h.smooth h.third_nonneg h.alpha_pos.le h.beta_pos
    h.mu_pos.le h.mu_small h.mu_beta h.a_nonneg h.a_le_one h.third_lipschitz
    (h.lower _ _ hi.point_radius hi.plane_geometry.point_radius) h.witness_scale h.escape_small
    h.escape_decrease h.q_nonneg hv

lemma finish_correct (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x)) {n : ℕ} (h : Hypotheses p f n)
    (status : Status E) (hi : StatusInvariant p f h.A h.τ n status) (he : StatusEnergy p status)
    (hstopped : ∀ st, status ≠ .running st) :
    Faithful f ((finish p status).eval g) ∧ successful p ((finish p status).eval g) ∧
      (‖((finish p status).eval g).gradient‖ ≤ p.ε ∨
        p.μ * ‖p.S (((finish p status).eval g).x - p.center.x)‖ ^ 2 ≤
          256 * (p.center.value - ((finish p status).eval g).value)) := by
  cases status with
  | running st => exact False.elim (hstopped st rfl)
  | finished x =>
    have hx : (finish p (.finished x)).eval g = x := by
      simp only [finish, eval_map]
    rw [hx]
    refine ⟨hi.1, hi.2, ?_⟩
    rcases he with hg | he
    · exact Or.inl hg
    · right
      have hd : 0 ≤ p.center.value - x.value := by
        have hn := mul_nonneg h.mu_pos.le (sq_nonneg ‖p.S (x.x - p.center.x)‖)
        linarith
      linarith
  | witness w =>
    have hp := witness_progress p f h w hi
    have hv : ((finish p (.witness w)).eval g).value ≤ p.center.value - p.q := by
      obtain ⟨i, hh⟩ := hp
      exact (QuarticWitnessValues.finish_witness_value p f g horacle w i).trans hh
    obtain ⟨hne, hmetric, _⟩ := QuarticWitnessValues.witness_failed_support p f hi h.alpha_pos.le
      h.beta_pos h.mu_pos.le h.mu_small h.mu_beta
      (h.lower _ _ hi.point_radius hi.plane_geometry.point_radius)
    have hc := QuarticWitnessEnergy.candidates_energy p f hi h.mu_pos.le h.A_nonneg
      (A_square_mul p f h) hne hmetric h.escape_energy
    have hw : p.μ * ‖p.S (w.point.x - p.center.x)‖ ^ 2 ≤ 256 * p.q := by
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hi.point_radius 2) h.mu_pos.le
      have heq := A_square_mul p f h
      nlinarith only [hh, heq, h.q_nonneg]
    exact ⟨QuarticWitnessValues.finish_witness_faithful p f g horacle w hi.point_faithful,
      Or.inl hv, Or.inr (QuarticWitnessEnergy.finish_witness_energy p f g horacle w hw hc hp)⟩

lemma plan_correct (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x)) (n : ℕ) (h : Hypotheses p f n) :
    Faithful f ((plan p n).eval g) ∧ successful p ((plan p n).eval g) ∧
      (‖((plan p n).eval g).gradient‖ ≤ p.ε ∨
        p.μ * ‖p.S (((plan p n).eval g).x - p.center.x)‖ ^ 2 ≤
          256 * (p.center.value - ((plan p n).eval g).value)) := by
  let initial := Status.running (State.mk p.center p.center (p.S p.center.x) [])
  have hi : StatusInvariant p f h.A h.τ 0 initial :=
    initial_invariant p f h.center_faithful h.A_nonneg h.tau_nonneg h.q_nonneg
  have hstep (k : ℕ) (status : Status E) (hs : StatusInvariant p f h.A h.τ k status) :
      StatusInvariant p f h.A h.τ (k + 1) ((step p status).eval g) :=
    step_invariant p f g horacle status hs h.center_faithful h.a_nonneg h.a_le_one h.mu_pos
      h.smoothness_pos h.alpha_pos h.radius_pos h.A_nonneg h.tau_nonneg h.q_nonneg
      h.A_square h.tau_square h.A_guard h.q_guard h.acceleration h.model
  have henergy (k : ℕ) (status : Status E) (hs : StatusInvariant p f h.A h.τ k status)
      (he : StatusEnergy p status) : StatusEnergy p ((step p status).eval g) :=
    step_energy p f g horacle status hs he h.a_nonneg h.mu_pos h.smoothness_pos h.mu_le_smoothness
      h.alpha_pos.le h.radius_pos (A_square_mul p f h) h.A_guard h.model
  have hl : StatusInvariant p f h.A h.τ n ((loop p n initial).eval g) := by
    simpa only [zero_add] using loop_invariant p f g hstep n 0 initial hi
  have hle : StatusEnergy p ((loop p n initial).eval g) := loop_energy p f g hstep henergy n 0 initial hi trivial
  have hc := QuarticStageCertificate.certificate_invariant p f g horacle _ hl
    (certificate_geometry p f h) (certificate_complete p f h)
  have hce := QuarticStageEnergy.certificate_energy p f g horacle _ hl hle hc.1 h.mu_pos h.smoothness_pos
    h.mu_le_smoothness h.alpha_pos.le h.radius_pos h.A_nonneg (A_square_mul p f h) h.A_guard h.model
  have hf := finish_correct p f g horacle h _ hc.1 hce hc.2
  simpa only [plan, OracleTemplate.RandomReshuffling.eval_cast, eval_bind, initial] using hf

end LongTails.Proofs.QuarticStageGuarantee
