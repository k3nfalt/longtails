import LongTails.Proofs.PointwiseHessianExecution

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianLedger

open OracleTemplate
open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianExecution

def PreviousFailure {p : Public} (f : p.E → ℝ) (s : State p) : Prop :=
  s.τ ≠ s.η → ∃ z, (2 / s.τ) • gradient f z + z - s.center = 0 ∧
    radiusCap p (s.τ / 2) / 2 < ‖z - s.center‖

lemma initial_trial_previousFailure {p : Public} (f : p.E → ℝ) (s : State p) (r : ℝ) :
    PreviousFailure f (startTrial s s.η r) := by
  intro h
  exact False.elim (h rfl)

lemma failedTrial_previousFailure {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hp : InnerParameters f s) (hn : NewtonReady f s) (hprev : PreviousFailure f s)
    (hfail : ¬ ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r) :
    PreviousFailure f (failedTrial s) := by
  unfold failedTrial
  split_ifs with hr
  · exact hprev
  · have hre : s.r = radiusCap p s.τ := le_antisymm hp.r_le (le_of_not_gt hr)
    obtain ⟨z, hz⟩ := PointwiseHessianProx.proximal_exists hf hc (one_div_pos.mpr hp.τ_pos) s.center
    have hcert := PointwiseHessianTrial.failed_radius_certificate p hf hc hM₀ hM₁ hT
      hp.τ_pos hp.r_pos hp.b_pos hp.b_le s.center s.x z hn.radius
      (by simpa only [hn.gradient_eq] using hn.residual) hz
      (by simpa only [hn.gradient_eq] using lt_of_not_ge hfail)
    intro _
    refine ⟨z, ?_, ?_⟩
    · change (2 / (2 * s.τ)) • gradient f z + z - s.center = 0
      have he : 2 / (2 * s.τ) = 1 / s.τ := by field_simp
      rwa [he]
    · change radiusCap p ((2 * s.τ) / 2) / 2 < ‖z - s.center‖
      simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), hre] using hcert

lemma previousFailure_transfer {p : Public} {f : p.E → ℝ} {s t : State p}
    (hprev : PreviousFailure f s) (hτ : t.τ = s.τ) (hη : t.η = s.η)
    (hc : t.center = s.center) : PreviousFailure f t := by
  simpa only [PreviousFailure, hτ, hη, hc] using hprev

lemma certified_accept_bound {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hp : InnerParameters f s) (ho : PointwiseHessianOuter.Invariant f xs s)
    (hprev : PreviousFailure f s) (ht : s.τ ≠ s.η)
    (hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    s.τ ≤ 1024 * p.M₀ * ‖s.x - s.center‖ := by
  obtain ⟨z, hz, hcert⟩ := hprev ht
  have hzr := PointwiseHessianOuter.energy_radius s xs hR.le ho.A_pos.le
    (fun x => hmin (Set.mem_univ x)) ho.energy_le
  have hcr := PointwiseHessianOuter.center_radius s xs hR.le ho.A_pos.le ho.η_pos ho.radius hzr
  exact PointwiseHessianTrial.previous_cap_accept_bound p hf hc hM₀ hR hp.τ_pos
    s.center s.x z xs hmin hcr hz hcert hres

def CertificateInvariant {p : Public} (f : p.E → ℝ) (s : State p) : Prop :=
  (s.phase = .newtonHessian ∨ s.phase = .newtonGradient) → PreviousFailure f s

lemma initial_certificateInvariant {p : Public} (f : p.E → ℝ) : CertificateInvariant f (initial p) := by
  intro h
  simp only [initial] at h
  split_ifs at h <;> simp at h

lemma accept_certificateInvariant {p : Public} (f : p.E → ℝ) (s : State p) :
    CertificateInvariant f (accept s) := by
  intro h
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · simp [accept, finish, ht] at h
  · simp [accept, ht] at h

lemma center_certificateInvariant {p : Public} (f : p.E → ℝ) (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .centerGradient) :
    CertificateInvariant f (update s reply) := by
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · intro _
    exact initial_trial_previousFailure f _ _

lemma gradient_certificateInvariant {p : Public} (f : p.E → ℝ) (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonGradient)
    (hi : CertificateInvariant f s) : CertificateInvariant f (update s reply) := by
  have hp := hi (Or.inr hs)
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · intro _
    exact previousFailure_transfer hp rfl rfl rfl
  · exact accept_certificateInvariant f _
  · intro _
    exact previousFailure_transfer hp rfl rfl rfl

lemma hessian_certificateInvariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hs : s.phase = .newtonHessian) (hi : StateInvariant f xs s) (hprev : CertificateInvariant f s) :
    CertificateInvariant f (update s (.inr (fderiv ℝ (gradient f) s.x))) := by
  have hp := hi.phase
  simp only [PhaseInvariant, hs] at hp
  have hcprev := hprev (Or.inl hs)
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r
  · rw [hessian_update_guard s _ hs hg]
    intro _
    exact previousFailure_transfer hcprev rfl rfl rfl
  · rw [hessian_update_failure s _ hs hg]
    intro _
    exact failedTrial_previousFailure s hf hc hM₀ hM₁ hT hp.1 hp.2 hcprev hg

lemma trace_certificateInvariant (p : Public) {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    CertificateInvariant f (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1 := by
  induction n with
  | zero => exact initial_certificateInvariant f
  | succ n ih =>
    have hi := trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
      (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ n
    let s := (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1
    change CertificateInvariant f (update s (O.answer _ (query s) _))
    change CertificateInvariant f s at ih
    change StateInvariant f xs s at hi
    cases hs : s.phase with
    | centerGradient => exact center_certificateInvariant f s _ hs
    | newtonGradient => exact gradient_certificateInvariant f s _ hs ih
    | newtonHessian =>
      rw [show query s = (1, s.x) by simp [query, hs], hHess]
      exact hessian_certificateInvariant s xs hf hc hM₀ hM₁ hT hs hi ih
    | finished =>
      rw [PointwiseHessianOuter.finished_output s _ hs]
      exact ih

def Accepted {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : Prop :=
  s.phase = .newtonGradient ∧ ¬ ‖readGradient reply‖ ≤ gradientThreshold p ∧
    ¬ s.b < 1 / s.τ ∧ ‖s.b • readGradient reply + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2

lemma accepted_update {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (h : Accepted s reply) : update s reply = accept { s with g := readGradient reply } := by
  obtain ⟨hp, hg, hb, hm⟩ := h
  simp only [update, hp, hg, hb, hm, ite_true, ite_false]

lemma nonaccepted_energy {p : Public} (f : p.E → ℝ) (xs : p.E) (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (h : ¬ Accepted s reply) :
    PointwiseHessianOuter.energy f (update s reply) xs = PointwiseHessianOuter.energy f s xs := by
  cases hp : s.phase with
  | finished => simp [update, hp]
  | centerGradient =>
    simp only [update, hp]
    split_ifs <;> rfl
  | newtonHessian =>
    simp only [update, hp]
    split_ifs
    · rfl
    · unfold failedTrial
      split_ifs <;> rfl
  | newtonGradient =>
    simp only [update, hp]
    split_ifs with hg hb hm
    · rfl
    · rfl
    · exact False.elim (h ⟨hp, hg, hb, hm⟩)
    · rfl

lemma accepted_energy {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hi : StateInvariant f xs s) (h : Accepted s (.inl (gradient f s.x))) :
    PointwiseHessianOuter.energy f (update s (.inl (gradient f s.x))) xs +
      (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 ≤ PointwiseHessianOuter.energy f s xs := by
  have hp := hi.phase
  simp only [PhaseInvariant, h.1] at hp
  have hb : s.b = 1 / s.τ := le_antisymm hp.1.b_le (le_of_not_gt h.2.2.1)
  rw [accepted_update s _ h]
  apply PointwiseHessianOuter.accept_energy hf hc { s with g := gradient f s.x } xs
    hi.outer.A_pos.le hi.outer.η_pos hp.1.η_le rfl
  simpa [readGradient, hb, State.center, State.a] using h.2.2.2

noncomputable def loss {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) : ℝ := by
  classical
  exact if Accepted s reply then (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 else 0

lemma update_energy {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (hi : StateInvariant f xs s)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hg : s.phase = .newtonGradient → reply = .inl (gradient f s.x)) :
    PointwiseHessianOuter.energy f (update s reply) xs + loss s reply ≤
      PointwiseHessianOuter.energy f s xs := by
  classical
  by_cases h : Accepted s reply
  · have he := hg h.1
    subst reply
    simpa only [loss, ite_eq_left h] using accepted_energy s xs hf hc hi h
  · rw [loss, ite_eq_right h, nonaccepted_energy f xs s reply h, add_zero]

lemma path_energy {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ i < N, StateInvariant f xs (s i))
    (hs : ∀ i < N, s (i + 1) = update (s i) (reply i))
    (hg : ∀ i < N, (s i).phase = .newtonGradient → reply i = .inl (gradient f (s i).x)) :
    PointwiseHessianOuter.energy f (s N) xs + (∑ i ∈ Finset.range N, loss (s i) (reply i)) ≤
      PointwiseHessianOuter.energy f (s 0) xs := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun i h => hi i (by omega)) (fun i h => hs i (by omega)) (fun i h => hg i (by omega))
    have hu := update_energy (s N) xs hf hc (hi N (by omega)) (reply N) (hg N (by omega))
    rw [← hs N (by omega)] at hu
    rw [Finset.sum_range_succ]
    linarith

lemma trace_loss_bound (p : Public) {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (N : ℕ) :
    (∑ i ∈ Finset.range N, loss (executeIndexedState O (algorithm p) seed ξ i).1
      (executeAnswerAt O (algorithm p) seed ξ i (query (executeIndexedState O (algorithm p) seed ξ i).1))) ≤ p.R ^ 2 := by
  let s := fun i => (executeIndexedState O (algorithm p) seed ξ i).1
  let reply := fun i => executeAnswerAt O (algorithm p) seed ξ i (query (s i))
  have hi (i : ℕ) : StateInvariant f xs (s i) := trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
    (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ i
  have hh := path_energy s xs hf hc reply N (fun i _ => hi i)
    (fun _ _ => rfl) (by
      intro i _ hs
      dsimp [reply, executeAnswerAt]
      rw [show query (s i) = (0, (s i).x) by simp [query, hs]]
      exact hgrad _ _ _)
  have hn := PointwiseHessianOuter.energy_nonneg (s N) xs (hi N).outer.A_pos.le
    (fun x => hmin (Set.mem_univ x))
  have h0 := (hi 0).outer.energy_le
  change (∑ i ∈ Finset.range N, loss (s i) (reply i)) ≤ p.R ^ 2
  linarith

lemma accepted_displacement_charge {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : PointwiseHessianOuter.Invariant f xs s) :
    (if Accepted s reply then ‖s.x - s.center‖ ^ 2 else 0) ≤ (8 / 3 : ℝ) * loss s reply := by
  classical
  unfold loss
  split_ifs
  · have ha : 0 < s.a := PointwiseHessianTuning.weight_pos hi.A_pos.le hi.η_pos
    have hweight : 1 ≤ (s.A + s.a) * s.η := by
      nlinarith [hi.scale, mul_pos ha hi.η_pos]
    have hh := mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖s.x - s.center‖)
    nlinarith
  · simp

lemma path_displacement_sum {p : Public} {f : p.E → ℝ} {xs : p.E}
    (s : ℕ → State p) (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ i < N, PointwiseHessianOuter.Invariant f xs (s i))
    (hloss : (∑ i ∈ Finset.range N, loss (s i) (reply i)) ≤ p.R ^ 2) :
    (∑ i ∈ Finset.range N, if Accepted (s i) (reply i) then ‖(s i).x - (s i).center‖ ^ 2 else 0) ≤
      (8 / 3 : ℝ) * p.R ^ 2 := by
  classical
  have hh := Finset.sum_le_sum (fun i (h : i ∈ Finset.range N) =>
    accepted_displacement_charge (s i) (reply i) (hi i (Finset.mem_range.mp h)))
  rw [← Finset.mul_sum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hloss (by norm_num))

lemma loss_nonneg {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : PointwiseHessianOuter.Invariant f xs s) :
    0 ≤ loss s reply := by
  have ha : 0 < s.a := PointwiseHessianTuning.weight_pos hi.A_pos.le hi.η_pos
  have hA := hi.A_pos
  have hη := hi.η_pos
  unfold loss
  split_ifs <;> positivity

lemma damped_event_charge {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hi : StateInvariant f xs s) (hcert : CertificateInvariant f s)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hg : s.phase = .newtonGradient → reply = .inl (gradient f s.x)) :
    (if Accepted s reply ∧ s.τ ≠ s.η then s.A * s.η ^ 3 else 0) ≤
      (8 / 3 : ℝ) * (1024 * p.M₀) ^ 2 * loss s reply := by
  by_cases h : Accepted s reply ∧ s.τ ≠ s.η
  · rw [ite_eq_left h]
    have he := hg h.1.1
    subst reply
    have hp := hi.phase
    simp only [PhaseInvariant, h.1.1] at hp
    have hb : s.b = 1 / s.τ := le_antisymm hp.1.b_le (le_of_not_gt h.1.2.2.1)
    have hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2 := by
      simpa only [readGradient, hb] using h.1.2.2.2
    have hτ := certified_accept_bound s xs hf hc hM₀ hR hmin hp.1 hi.outer
      (hcert (Or.inr h.1.1)) h.2 hres
    have hh := PointwiseHessianOuter.damped_charge hi.outer.A_pos.le
      (PointwiseHessianTuning.weight_pos hi.outer.A_pos.le hi.outer.η_pos).le hi.outer.η_pos.le
      (hp.1.η_le.trans hτ)
    rw [loss, ite_eq_left h.1]
    dsimp only [State.a]
    nlinarith only [hh]
  · rw [ite_eq_right h]
    exact mul_nonneg (by positivity) (loss_nonneg s reply hi.outer)

lemma path_damped_sum {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ i < N, StateInvariant f xs (s i))
    (hcert : ∀ i < N, CertificateInvariant f (s i))
    (hg : ∀ i < N, (s i).phase = .newtonGradient → reply i = .inl (gradient f (s i).x))
    (hloss : (∑ i ∈ Finset.range N, loss (s i) (reply i)) ≤ p.R ^ 2) :
    (∑ i ∈ Finset.range N, if Accepted (s i) (reply i) ∧ (s i).τ ≠ (s i).η
      then (s i).A * (s i).η ^ 3 else 0) ≤ (2048 * p.M₀ * p.R) ^ 2 := by
  have hh := Finset.sum_le_sum (fun i (h : i ∈ Finset.range N) =>
    damped_event_charge (s i) xs hf hc hM₀ hR hmin (hi i (Finset.mem_range.mp h))
      (hcert i (Finset.mem_range.mp h)) (reply i) (hg i (Finset.mem_range.mp h)))
  rw [← Finset.mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left hloss
    (show 0 ≤ (8 / 3 : ℝ) * (1024 * p.M₀) ^ 2 by positivity)
  nlinarith [sq_nonneg (p.M₀ * p.R)]

lemma nonaccepted_outer_fields {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (h : ¬ Accepted s reply) :
    ((update s reply).A, (update s reply).η, (update s reply).w, (update s reply).z) =
      (s.A, s.η, s.w, s.z) := by
  cases hp : s.phase with
  | finished => simp [update, hp]
  | centerGradient =>
    simp only [update, hp]
    split_ifs <;> rfl
  | newtonHessian =>
    simp only [update, hp]
    split_ifs
    · rfl
    · unfold failedTrial
      split_ifs <;> rfl
  | newtonGradient =>
    simp only [update, hp]
    split_ifs with hg hb hm
    · rfl
    · rfl
    · exact False.elim (h ⟨hp, hg, hb, hm⟩)
    · rfl

lemma accepted_scales {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (h : Accepted s reply) :
    ((update s reply).A, (update s reply).η) = ((accept s).A, (accept s).η) := by
  rw [accepted_update s reply h]
  rw [(PointwiseHessianOuter.accept_fields _).1, (PointwiseHessianOuter.accept_fields s).1,
    (PointwiseHessianOuter.accept_fields _).2.2.2, (PointwiseHessianOuter.accept_fields s).2.2.2]
  rfl

lemma path_constant_outer {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (j n : ℕ)
    (hs : ∀ k < n, s (j + k + 1) = update (s (j + k)) (reply (j + k)))
    (hn : ∀ k < n, ¬ Accepted (s (j + k)) (reply (j + k))) :
    ((s (j + n)).A, (s (j + n)).η, (s (j + n)).w, (s (j + n)).z) =
      ((s j).A, (s j).η, (s j).w, (s j).z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun k hk => hs k (by omega)) (fun k hk => hn k (by omega))
    rw [show j + (n + 1) = j + n + 1 by omega, hs n (by omega),
      nonaccepted_outer_fields _ _ (hn n (by omega))]
    exact hh

lemma consecutive_accept_scales {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {i j : ℕ} (hij : i < j)
    (hs : ∀ k, i ≤ k → k < j → s (k + 1) = update (s k) (reply k))
    (hi : Accepted (s i) (reply i))
    (hn : ∀ k, i < k → k < j → ¬ Accepted (s k) (reply k)) :
    ((s j).A, (s j).η) = ((accept (s i)).A, (accept (s i)).η) := by
  have hh := path_constant_outer s reply (i + 1) (j - (i + 1))
    (fun k hk => hs (i + 1 + k) (by omega) (by omega))
    (fun k hk => hn (i + 1 + k) (by omega) (by omega))
  rw [Nat.add_sub_of_le (by omega : i + 1 ≤ j)] at hh
  have hpair := congrArg (fun t : ℝ × ℝ × p.E × p.E => (t.1, t.2.1)) hh
  dsimp only at hpair
  rw [hs i le_rfl hij, accepted_scales (s i) (reply i) hi] at hpair
  exact hpair

lemma update_weight_mono {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : StateInvariant f xs s) : s.A ≤ (update s reply).A := by
  by_cases h : Accepted s reply
  · have hp := hi.phase
    simp only [PhaseInvariant, h.1] at hp
    have he := congrArg Prod.fst (accepted_scales s reply h)
    dsimp only at he
    rw [he]
    exact (PointwiseHessianOuter.accepted_weight_bounds s hi.outer.A_pos hi.outer.η_pos
      hp.1.η_le hi.outer.scale).1.le
  · have he := congrArg Prod.fst (nonaccepted_outer_fields s reply h)
    dsimp only at he
    rw [he]

lemma path_weight_mono {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k < N, StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : (s i).A ≤ (s j).A := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have hh := update_weight_mono (s j) (reply j) (hi j (by omega))
    rw [← hs j (by omega)] at hh
    exact (ih (by omega)).trans hh

lemma update_fraction_potential {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : StateInvariant f xs s) :
    (if Accepted s reply then PointwiseHessianOuter.fraction s else 0) +
      6 * PointwiseHessianOuter.fraction (update s reply) - 6 * PointwiseHessianOuter.fraction s ≤
      4 * (Real.log (update s reply).A - Real.log s.A) := by
  by_cases ha : Accepted s reply
  · rw [ite_eq_left ha]
    have hp := hi.phase
    simp only [PhaseInvariant, ha.1] at hp
    have hh := PointwiseHessianOuter.fraction_accept_potential s hi.outer.A_pos hi.outer.η_pos
      hp.1.η_le hi.outer.scale
    have he := accepted_scales s reply ha
    have hA := congrArg Prod.fst he
    have hη := congrArg Prod.snd he
    dsimp only at hA hη
    simpa only [PointwiseHessianOuter.fraction, State.a, hA, hη] using hh
  · rw [ite_eq_right ha]
    have he := nonaccepted_outer_fields s reply ha
    have hA := congrArg Prod.fst he
    have hη := congrArg (fun v : ℝ × ℝ × p.E × p.E => v.2.1) he
    dsimp only at hA hη
    simp only [PointwiseHessianOuter.fraction, State.a, hA, hη]
    ring_nf
    exact le_rfl

lemma path_fraction_potential {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k < N, StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then PointwiseHessianOuter.fraction (s k) else 0) +
      6 * PointwiseHessianOuter.fraction (s N) ≤ 6 * PointwiseHessianOuter.fraction (s 0) +
      4 * (Real.log (s N).A - Real.log (s 0).A) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun k hk => hi k (by omega)) (fun k hk => hs k (by omega))
    have hu := update_fraction_potential (s N) (reply N) (hi N (by omega))
    rw [← hs N (by omega)] at hu
    rw [Finset.sum_range_succ]
    linarith

lemma path_fraction_sum {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then PointwiseHessianOuter.fraction (s k) else 0) +
      PointwiseHessianOuter.fraction (s N) ≤ 6 + 4 * (Real.log (s N).A - Real.log (s 0).A) := by
  have hh := path_fraction_potential s reply N (fun k hk => hi k hk.le) hs
  have h0 := (hi 0 (Nat.zero_le _)).outer
  have hn := (hi N le_rfl).outer
  have hb := PointwiseHessianOuter.fraction_le (s 0) h0.A_pos.le h0.η_pos h0.scale
  have hp := PointwiseHessianOuter.fraction_pos (s N) hn.A_pos.le hn.η_pos
  linarith

lemma path_center_displacement_sum {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hR : 0 < p.R) (hmin : ∀ x, f xs ≤ f x)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then ‖(s k).center - (s k).w‖ else 0) +
      ‖(s N).center - (s N).w‖ ≤ 6 * p.R * (6 + 4 * (Real.log (s N).A - Real.log (s 0).A)) := by
  have hb (k : ℕ) (hk : k ≤ N) :
      ‖(s k).center - (s k).w‖ ≤ 6 * p.R * PointwiseHessianOuter.fraction (s k) := by
    have ho := (hi k hk).outer
    exact PointwiseHessianOuter.center_displacement (s k) xs ho.A_pos.le ho.η_pos ho.radius
      (PointwiseHessianOuter.energy_radius (s k) xs hR.le ho.A_pos.le hmin ho.energy_le)
  have hsum : (∑ k ∈ Finset.range N,
      if Accepted (s k) (reply k) then ‖(s k).center - (s k).w‖ else 0) ≤
      6 * p.R * (∑ k ∈ Finset.range N,
        if Accepted (s k) (reply k) then PointwiseHessianOuter.fraction (s k) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with ha
    · exact hb k (Finset.mem_range.mp hk).le
    · simp
  have hh := mul_le_mul_of_nonneg_left (path_fraction_sum s reply N hi hs) (by positivity : 0 ≤ 6 * p.R)
  have hn := hb N le_rfl
  nlinarith

lemma update_query_balance {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E)) :
    (if s.phase = .newtonHessian then (1 : ℝ) else 0) =
      (if s.phase = .newtonGradient then (1 : ℝ) else 0) +
      (if s.phase = .newtonHessian ∧ (update s reply).phase ≠ .newtonGradient then (1 : ℝ) else 0) +
      (if (update s reply).phase = .newtonGradient then (1 : ℝ) else 0) -
      (if s.phase = .newtonGradient then (1 : ℝ) else 0) := by
  cases hp : s.phase <;>
    simp only [update, hp] <;>
    split_ifs <;> simp_all [finish, startTrial, failedTrial, accept]
  split_ifs at *

lemma path_query_balance {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian then (1 : ℝ) else 0) +
      (if (s 0).phase = .newtonGradient then (1 : ℝ) else 0) =
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian ∧
        (s (k + 1)).phase ≠ .newtonGradient then (1 : ℝ) else 0) +
      (if (s N).phase = .newtonGradient then (1 : ℝ) else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun k hk => hs k (by omega))
    have hu := update_query_balance (s N) (reply N)
    rw [← hs N (by omega)] at hu
    simp only [Finset.sum_range_succ]
    linarith

lemma path_hessian_count {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian then (1 : ℝ) else 0) ≤
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian ∧
        (s (k + 1)).phase ≠ .newtonGradient then (1 : ℝ) else 0) + 1 := by
  have hh := path_query_balance s reply N hs
  split_ifs at hh <;> linarith

def RadiusCertificate {p : Public} (f : p.E → ℝ) (s : State p) : Prop :=
  initialRadius p s.τ < s.r → ∃ z, (1 / s.τ) • gradient f z + z - s.center = 0 ∧
    s.r < 4 * ‖z - s.center‖

lemma startTrial_radiusCertificate {p : Public} (f : p.E → ℝ) (s : State p) (τ : ℝ) :
    RadiusCertificate f (startTrial s τ (initialRadius p τ)) := by
  intro h
  exact False.elim (lt_irrefl _ h)

lemma failedTrial_radiusCertificate {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hp : InnerParameters f s) (hn : NewtonReady f s)
    (hfail : ¬ ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r) :
    RadiusCertificate f (failedTrial s) := by
  unfold failedTrial
  split_ifs with hr
  · obtain ⟨z, hz⟩ := PointwiseHessianProx.proximal_exists hf hc (one_div_pos.mpr hp.τ_pos) s.center
    have hcert := PointwiseHessianTrial.failed_radius_certificate p hf hc hM₀ hM₁ hT
      hp.τ_pos hp.r_pos hp.b_pos hp.b_le s.center s.x z hn.radius
      (by simpa only [hn.gradient_eq] using hn.residual) hz
      (by simpa only [hn.gradient_eq] using lt_of_not_ge hfail)
    intro _
    refine ⟨z, hz, ?_⟩
    change min (2 * s.r) (radiusCap p s.τ) < 4 * ‖z - s.center‖
    exact (min_le_left _ _).trans_lt (by linarith)
  · exact startTrial_radiusCertificate f s _

lemma radiusCertificate_transfer {p : Public} {f : p.E → ℝ} {s t : State p}
    (hcert : RadiusCertificate f s) (hτ : t.τ = s.τ) (hr : t.r = s.r)
    (hc : t.center = s.center) : RadiusCertificate f t := by
  simpa only [RadiusCertificate, hτ, hr, hc] using hcert

def RadiusInvariant {p : Public} (f : p.E → ℝ) (s : State p) : Prop :=
  (s.phase = .newtonHessian ∨ s.phase = .newtonGradient) → RadiusCertificate f s

lemma initial_radiusInvariant {p : Public} (f : p.E → ℝ) : RadiusInvariant f (initial p) := by
  intro h
  simp only [initial] at h
  split_ifs at h <;> simp at h

lemma accept_radiusInvariant {p : Public} (f : p.E → ℝ) (s : State p) :
    RadiusInvariant f (accept s) := by
  intro h
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · simp [accept, finish, ht] at h
  · simp [accept, ht] at h

lemma center_radiusInvariant {p : Public} (f : p.E → ℝ) (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .centerGradient) :
    RadiusInvariant f (update s reply) := by
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · intro _
    exact startTrial_radiusCertificate f _ _

lemma gradient_radiusInvariant {p : Public} (f : p.E → ℝ) (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonGradient)
    (hi : RadiusInvariant f s) : RadiusInvariant f (update s reply) := by
  have hp := hi (Or.inr hs)
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · intro _
    exact radiusCertificate_transfer hp rfl rfl rfl
  · exact accept_radiusInvariant f _
  · intro _
    exact radiusCertificate_transfer hp rfl rfl rfl

lemma hessian_radiusInvariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hs : s.phase = .newtonHessian) (hi : StateInvariant f xs s) (hprev : RadiusInvariant f s) :
    RadiusInvariant f (update s (.inr (fderiv ℝ (gradient f) s.x))) := by
  have hp := hi.phase
  simp only [PhaseInvariant, hs] at hp
  have hcprev := hprev (Or.inl hs)
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r
  · rw [hessian_update_guard s _ hs hg]
    intro _
    exact radiusCertificate_transfer hcprev rfl rfl rfl
  · rw [hessian_update_failure s _ hs hg]
    intro _
    exact failedTrial_radiusCertificate s hf hc hM₀ hM₁ hT hp.1 hp.2 hg

lemma trace_radiusInvariant (p : Public) {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    RadiusInvariant f (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1 := by
  induction n with
  | zero => exact initial_radiusInvariant f
  | succ n ih =>
    have hi := trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
      (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ n
    let s := (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1
    change RadiusInvariant f (update s (O.answer _ (query s) _))
    change RadiusInvariant f s at ih
    change StateInvariant f xs s at hi
    cases hs : s.phase with
    | centerGradient => exact center_radiusInvariant f s _ hs
    | newtonGradient => exact gradient_radiusInvariant f s _ hs ih
    | newtonHessian =>
      rw [show query s = (1, s.x) by simp [query, hs], hHess]
      exact hessian_radiusInvariant s xs hf hc hM₀ hM₁ hT hs hi ih
    | finished =>
      rw [PointwiseHessianOuter.finished_output s _ hs]
      exact ih

lemma certified_radius_accept_bound {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hp : InnerParameters f s) (hcert : RadiusCertificate f s)
    (hstop : gradientThreshold p < ‖gradient f s.x‖)
    (hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    s.r ≤ 6 * ‖s.x - s.center‖ := by
  by_cases hr : initialRadius p s.τ < s.r
  · obtain ⟨z, hz, hzr⟩ := hcert hr
    have hd := PointwiseHessianProx.relative_radius
      (PointwiseHessianGeometry.gradient_monotone hf hc) (one_div_pos.mpr hp.τ_pos).le
      s.center s.x z hz hres
    linarith
  · have hbg : (1 / s.τ) * ‖gradient f s.x‖ ≤ 3 * ‖s.x - s.center‖ / 2 := by
      have hh := norm_sub_le ((1 / s.τ) • gradient f s.x + s.x - s.center) (s.x - s.center)
      have he : (1 / s.τ) • gradient f s.x + s.x - s.center - (s.x - s.center) =
          (1 / s.τ) • gradient f s.x := by abel
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp.τ_pos)] at hh
      linarith
    have hinit : initialRadius p s.τ ≤ (1 / s.τ) * gradientThreshold p := by
      simpa only [initialRadius, div_eq_inv_mul, one_div, mul_one] using
        (min_le_left (gradientThreshold p / s.τ) (radiusCap p s.τ))
    have hg := mul_lt_mul_of_pos_left hstop (one_div_pos.mpr hp.τ_pos)
    have hrr := le_of_not_gt hr
    nlinarith [norm_nonneg (s.x - s.center)]


lemma radiusCap_double_of_small {p : Public} {τ : ℝ} (hR : 0 < p.R)
    (hsmall : radiusCap p τ < 8 * p.R) : radiusCap p (2 * τ) = 2 * radiusCap p τ := by
  by_cases hzero : p.M₀ = 0
  · simp only [radiusCap, hzero, ite_true] at hsmall
    linarith
  · have hquot : τ / (64 * p.M₀) < 8 * p.R := by
      simp only [radiusCap, hzero, ite_false] at hsmall
      exact (min_lt_iff.mp hsmall).resolve_left (by linarith)
    have hd : 2 * τ / (64 * p.M₀) = 2 * (τ / (64 * p.M₀)) := by ring
    simp only [radiusCap, hzero, ite_false, hd,
      min_eq_right (show τ / (64 * p.M₀) ≤ 16 * p.R by linarith),
      min_eq_right (show 2 * (τ / (64 * p.M₀)) ≤ 16 * p.R by linarith)]


lemma certified_previous_radius_accept_bound {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hτ : 0 < s.τ) (hprev : PreviousFailure f s) (ht : s.τ ≠ s.η)
    (hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    radiusCap p (s.τ / 2) < 6 * ‖s.x - s.center‖ := by
  obtain ⟨z, hz, hcert⟩ := hprev ht
  have hm := PointwiseHessianGeometry.gradient_monotone hf hc
  obtain ⟨zn, hzn⟩ := PointwiseHessianProx.proximal_exists hf hc (one_div_pos.mpr hτ) s.center
  have hhalf := PointwiseHessianProx.radius_half hm (one_div_pos.mpr hτ) s.center zn z hzn
    (by simpa [div_eq_mul_inv] using hz)
  have hrel := PointwiseHessianProx.relative_radius hm (one_div_pos.mpr hτ).le s.center s.x zn hzn hres
  linarith

lemma previous_cap_half {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hp : InnerParameters f s) (ho : PointwiseHessianOuter.Invariant f xs s)
    (hprev : PreviousFailure f s) (ht : s.τ ≠ s.η) :
    radiusCap p (s.τ / 2) = radiusCap p s.τ / 2 := by
  obtain ⟨z, hz, hcert⟩ := hprev ht
  have hzr := PointwiseHessianOuter.energy_radius s xs hR.le ho.A_pos.le
    (fun x => hmin (Set.mem_univ x)) ho.energy_le
  have hcr := PointwiseHessianOuter.center_radius s xs hR.le ho.A_pos.le ho.η_pos ho.radius hzr
  have hτ := hp.τ_pos
  have hroot := PointwiseHessianProx.root_radius
    (PointwiseHessianGeometry.gradient_monotone hf hc) (show 0 ≤ 2 / s.τ by positivity)
    s.center z xs (PointwiseHessianGeometry.minimizer_gradient hmin) hz
  have hcsq := pow_le_pow_left₀ (norm_nonneg _) hcr 2
  have hdist : ‖z - s.center‖ ≤ 4 * p.R := by
    nlinarith [sq_nonneg ‖z - xs‖, norm_nonneg (z - s.center)]
  have hsmall : radiusCap p (s.τ / 2) < 8 * p.R := by linarith
  have hd := radiusCap_double_of_small hR hsmall
  have he : 2 * (s.τ / 2) = s.τ := by ring
  rw [he] at hd
  linarith


end LongTails.Proofs.PointwiseHessianLedger
