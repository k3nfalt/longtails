import LongTails.Proofs.HystereticHessianDescent

namespace LongTails.Proofs.HystereticHessianLedger

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianDescent HystereticHessianTransport HystereticHessianMoments HystereticHessianTracking
open HystereticHessianPhases

noncomputable def finePotential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) : ℝ :=
  if s.fine then max 0 (‖g s.point‖ ^ 2 - c.radius ^ 2 / 4) else 0

lemma finePotential_nonneg (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) :
    0 ≤ finePotential p c g s := by
  unfold finePotential
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma finePotential_initial (p : Params) (c : Config) (g : Space p → Space p) :
    finePotential p c g (initial p c) = 0 := by simp [finePotential, initial]

lemma positive_part_growth {x y d : ℝ} (hd : 0 ≤ d) (hxy : y - x ≤ d) :
    max 0 y - max 0 x ≤ d := by
  have hx0 : 0 ≤ max 0 x := le_max_left _ _
  have hxx : x ≤ max 0 x := le_max_right _ _
  have hy : max 0 y ≤ max 0 x + d := max_le (by linarith) (by linarith)
  linarith

lemma pilot_entry_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (v : Space p) (hU : 0 ≤ c.radius)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256)
    (he : ‖v‖ ≤ c.radius / 4) :
    finePotential p c g { s with fine := true } = 0 := by
  have hh := norm_le_norm_sub_add (g s.point) v
  rw [norm_sub_rev] at hh
  have hr : ‖g s.point‖ ≤ c.radius / 2 := by linarith
  have hs : ‖g s.point‖ ^ 2 - c.radius ^ 2 / 4 ≤ 0 := by
    nlinarith [norm_nonneg (g s.point)]
  simp [finePotential, max_eq_left hs]

lemma pilot_exit_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (v : Space p) (hU : 0 ≤ c.radius) (hf : s.fine = true)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256)
    (he : 3 * c.radius ≤ ‖v‖) :
    15 * c.radius ^ 2 / 4 ≤ finePotential p c g s := by
  have hh := norm_le_norm_sub_add v (g s.point)
  have hr : 2 * c.radius ≤ ‖g s.point‖ := by linarith
  have hs : 15 * c.radius ^ 2 / 4 ≤ ‖g s.point‖ ^ 2 - c.radius ^ 2 / 4 := by
    nlinarith
  exact hs.trans (by simp only [finePotential, hf, ite_true]; exact le_max_right _ _)

lemma fine_potential_growth (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hU : 0 ≤ c.radius) (hη : 0 ≤ c.fineStep)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4)
    (s : State p c) (hmode : s.fine = true) (hm : MoveValid p c s)
    (ht : transportQuery p c s = 1) (hregion : ‖g s.point‖ ≤ 4 * c.radius)
    (hshort : 2 * (p.L0 + 4 * p.L1 * c.radius) * c.fineStep ≤ ‖g s.point‖)
    (hcharge : c.fineStep * ‖g s.point‖ ≤ 4 * (f s.point - f (s.point + s.move))) :
    finePotential p c g { s with point := s.point + s.move } - finePotential p c g s ≤
      24 * (p.L0 + 4 * p.L1 * c.radius) * (f s.point - f (s.point + s.move)) := by
  have hmove : ‖s.point + s.move - s.point‖ ≤ c.fineStep := by
    simp only [add_sub_cancel_left]
    rw [move_eq_fine p c s hm ht]
    exact fine_displacement_bound p c s hη
  have hcurv : 0 ≤ 2 * (p.L0 + 4 * p.L1 * c.radius) := by positivity
  have hdescent : ‖g s.point‖ * ‖s.point + s.move - s.point‖ ≤
      4 * (f s.point - f (s.point + s.move)) := by
    nlinarith [mul_le_mul_of_nonneg_left hmove (norm_nonneg (g s.point))]
  have hgrowth := AffineTransportCrossings.local_squared_growth hL0 hL1 hU hg hH
    s.point (s.point + s.move) hregion
    ((mul_le_mul_of_nonneg_left hmove hL1).trans hsmall)
    ((mul_le_mul_of_nonneg_left hmove hcurv).trans hshort) hdescent
  have hdrop : 0 ≤ f s.point - f (s.point + s.move) := by
    nlinarith [mul_nonneg hη (norm_nonneg (g s.point))]
  have hpos : 0 ≤ 24 * (p.L0 + 4 * p.L1 * c.radius) * (f s.point - f (s.point + s.move)) := by
    positivity
  simp only [finePotential, hmode, ite_true]
  apply positive_part_growth hpos
  linarith

def modeExit (p : Params) (c : Config) (s t : State p c) : Bool := s.fine && !t.fine

lemma finishPilot_banking (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (v : Space p) {C : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ c.radius)
    (hsafe : ‖v‖ ≤ c.guardThreshold)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256)
    (hc : c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point) :
    finePotential p c g (finishPilot p c s v) +
      (if modeExit p c s (finishPilot p c s v) then 15 * c.radius ^ 2 / 4 else 0) ≤
        finePotential p c g s + C * (f s.point - f (finishPilot p c s v).point) := by
  unfold finishPilot
  rw [ite_eq_right (not_lt.mpr hsafe)]
  cases hf : s.fine with
  | true =>
    simp only [ite_true]
    by_cases he : 3 * c.radius ≤ ‖v‖
    · simp only [he, ite_true]
      have hh := pilot_exit_potential p c g s v hU hf hv he
      simpa [finePotential, modeExit, hf] using hh
    · simp only [he, ite_false]
      by_cases hi : s.inner = 0
      · simp [hi, finePotential, modeExit, hf]
      · simp only [hi, ite_false]
        unfold beginFineStep
        split_ifs <;> simp_all [finePotential, modeExit]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    by_cases he : ‖v‖ ≤ c.radius / 4
    · simp only [he, ite_true]
      have hh := pilot_entry_potential p c g s v hU hv he
      simpa [finePotential, modeExit, hf] using hh.le
    · simp only [he, ite_false]
      have hh := mul_nonneg hC (sub_nonneg.mpr (hc (lt_of_not_ge he)))
      simpa [finePotential, modeExit, hf] using hh

lemma raw_update_banking (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (reply : Space p) {M C : ℝ}
    (hM : 0 ≤ M) (hUM : c.radius ≤ M) (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hC : 0 ≤ C) (hU : 0 ≤ c.radius) (hx : ‖g s.point‖ ≤ M)
    (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 →
      finePotential p c g { s with point := s.point + s.move } - finePotential p c g s ≤
        C * (f s.point - f (s.point + s.move))) :
    finePotential p c g (rawUpdate p c s reply) +
      (if modeExit p c s (rawUpdate p c s reply) then 15 * c.radius ^ 2 / 4 else 0) ≤
        finePotential p c g s + C * (f s.point - f (rawUpdate p c s reply).point) := by
  unfold rawUpdate
  cases ha : s.active with
  | false => simp [finePotential, modeExit]
  | true =>
    simp only [ite_true]
    cases he : s.phase with
    | padding => simp [finePotential, modeExit]
    | transport i sum =>
      dsimp only
      by_cases hi : i < c.transportBatch
      · simp [hi, finePotential, modeExit]
      · simp only [hi, ite_false]
        have hh := ht (by simp [transportQuery, ha, he])
        simpa [finePotential, modeExit, sub_le_iff_le_add, add_comm] using hh
    | gradient refresh j i sum values =>
      dsimp only
      by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
      · simp [hi, finePotential, modeExit]
      · simp only [hi, ite_false]
        by_cases hj : j.val + 1 < c.groups + 1
        · simp [hj, finePotential, modeExit]
        · simp only [hj, dite_false]
          cases refresh with
          | true =>
            simp only [ite_true]
            unfold beginFineStep
            split_ifs <;> simp_all [finePotential, modeExit]
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have hv := hp ha j i sum values he (by simpa using hi) (by omega)
            exact finishPilot_banking p c f g s _ hC hU
              (accurate_pilot_passes_guard p c g hM hUM hguard s.point _ hx hv) hv
              (hc _ hv)

lemma update_banking (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p) {M C : ℝ}
    (hM : 0 ≤ M) (hUM : c.radius ≤ M) (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hC : 0 ≤ C) (hU : 0 ≤ c.radius) (hx : ‖g s.point‖ ≤ M)
    (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 →
      finePotential p c g { s with point := s.point + s.move } - finePotential p c g s ≤
        C * (f s.point - f (s.point + s.move))) :
    finePotential p c g (update p c s u reply) +
      (if modeExit p c s (update p c s u reply) then 15 * c.radius ^ 2 / 4 else 0) ≤
        finePotential p c g s + C * (f s.point - f (update p c s u reply).point) := by
  have hh := raw_update_banking p c f g s reply hM hUM hguard hC hU hx hp hc ht
  have hpoint : (update p c s u reply).point = (rawUpdate p c s reply).point := by
    unfold update
    split_ifs <;> rfl
  have hfine : (update p c s u reply).fine = (rawUpdate p c s reply).fine := by
    unfold update
    split_ifs <;> rfl
  convert hh using 1 <;> simp [finePotential, modeExit, hpoint, hfine]

lemma fine_of_transport (p : Params) (c : Config) (s : State p c)
    (hm : ModeValid p c s) (ht : transportQuery p c s = 1) : s.fine = true := by
  cases ha : s.active <;> cases he : s.phase <;> simp_all [transportQuery, ModeValid]

lemma path_step_banking (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    (hshort : 2 * (p.L0 + 4 * p.L1 * c.radius) * c.fineStep ≤ 31 * c.accuracy / 64)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (N : ℕ)
    (hpilot : ∀ n ≤ N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n ≤ N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64) :
    let s := path p c answer (initial p c) ξ N
    let t := path p c answer (initial p c) ξ (N + 1)
    finePotential p c g t + (if modeExit p c s t then 15 * c.radius ^ 2 / 4 else 0) ≤
      finePotential p c g s + 24 * (p.L0 + 4 * p.L1 * c.radius) * (f s.point - f t.point) := by
  dsimp only
  have hs := path_sublevel p c answer f g ξ hL0 hL1 hη he hcap hU hf hg hH hsmall hbase N
    (fun n hn => hpilot n (by omega)) (fun n hn => hbound n (by omega))
  have hx := sublevel_gradient_bound p f g hL0 hL1 hf hg hH hm hM hlinear hconstant _ hs
  have hp : path p c answer (initial p c) ξ (N + 1) =
      update p c (path p c answer (initial p c) ξ N) (ξ N).1
        (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
    HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
  rw [hp]
  apply update_banking p c f g _ _ _ hM hUM hguard (by positivity) hU.le hx (hpilot N le_rfl)
  · intro v hv hl
    exact coarse_move_nonincrease p c f g hL0 hL1 hcap hU hf hg hH _ v hv hl
  · intro ht
    have hh := path_fine_move_charge p c answer f g ξ hL0 hL1 hη he hf hg hH
      hsmall hbase N ht hbound
    have hl := (localMask_bounds p c g _ (path_localMask_active p c answer g hU.le hη ξ N
      (fun n hn => hpilot n (by omega)) ht)).2.1
    have hmode := fine_of_transport p c _
      (path_mode_valid p c answer (initial p c) (by simp [ModeValid, initial]) ξ N) ht
    exact fine_potential_growth p c f g hL0 hL1 hU.le hη hg hH hsmall _ hmode
      (path_move_valid p c answer (initial p c) (by trivial) ξ N) ht hl
      (hshort.trans hh.1.le) hh.2

lemma banking_event_count (F Φ : ℕ → ℝ) (A : ℕ → Bool) {ρ C : ℝ} (N : ℕ)
    (hstep : ∀ n < N, Φ (n + 1) + (if A n then ρ else 0) ≤
      Φ n + C * (F n - F (n + 1))) :
    Φ N + ((∑ n ∈ Finset.range N, if A n then 1 else 0 : ℕ) : ℝ) * ρ ≤
      Φ 0 + C * (F 0 - F N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun n hn => hstep n (by omega))
    have hs := hstep N (by omega)
    rw [Finset.sum_range_succ]
    cases ha : A N with
    | false =>
      simp only [Bool.false_eq_true, ite_false, add_zero]
      simp only [ha, Bool.false_eq_true, ite_false, add_zero] at hs
      nlinarith
    | true =>
      simp only [ite_true, Nat.cast_add, Nat.cast_one]
      simp only [ha, ite_true] at hs
      nlinarith

lemma update_active_predecessor (p : Params) (c : Config) (s : State p c) (u : ℝ)
    (reply : Space p) (h : (update p c s u reply).active = true) : s.active = true := by
  cases ha : s.active with
  | true => rfl
  | false =>
    unfold update at h
    split_ifs at h <;> simp [rawUpdate, ha] at h

lemma path_active_prefix (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) {n N : ℕ} (hn : n ≤ N)
    (hactive : (path p c answer s ξ N).active = true) :
    (path p c answer s ξ n).active = true := by
  induction N with
  | zero => have : n = 0 := by omega
            simpa [this] using hactive
  | succ N ih =>
    by_cases heq : n = N + 1
    · simpa [heq] using hactive
    · apply ih (by omega)
      rw [path, HeavyTailedProductProcess.trajectory_succ_last] at hactive
      exact update_active_predecessor p c _ _ _ hactive

lemma beginFineStep_inner (p : Params) (c : Config) (s : State p c) :
    (beginFineStep p c s).inner = s.inner := by
  unfold beginFineStep
  split_ifs <;> rfl

lemma finishPilot_inner (p : Params) (c : Config) (s : State p c) (v : Space p) :
    (finishPilot p c s v).inner = s.inner := by
  unfold finishPilot
  split_ifs <;> first | rfl | exact beginFineStep_inner p c s

lemma raw_inner_increment (p : Params) (c : Config) (s : State p c) (reply : Space p) :
    (rawUpdate p c s reply).inner = s.inner + if fineMove p c s then 1 else 0 := by
  cases ha : s.active with
  | false => simp [rawUpdate, fineMove, ha]
  | true =>
    cases he : s.phase with
    | padding => simp [rawUpdate, fineMove, ha, he]
    | transport i sum =>
      by_cases hi : i < c.transportBatch
      · simp [rawUpdate, fineMove, ha, he, hi, show ¬c.transportBatch ≤ i by omega]
      · simp [rawUpdate, fineMove, ha, he, hi, show c.transportBatch ≤ i by omega]
    | gradient refresh j i sum values =>
      simp only [rawUpdate, fineMove, ha, he, ite_true, Bool.false_eq_true, ite_false, add_zero]
      split_ifs <;> first | rfl | exact beginFineStep_inner p c _ | exact finishPilot_inner p c s _

lemma update_inner_increment (p : Params) (c : Config) (s : State p c) (u : ℝ) (reply : Space p)
    (hc : s.slot + 1 < macroCalls c) :
    (update p c s u reply).inner = s.inner + if fineMove p c s then 1 else 0 := by
  simpa only [update, hc, ite_true] using raw_inner_increment p c s reply

lemma active_boundary_padding (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (ha : s.active = true)
    (hb : macroCalls c ≤ s.slot + 1) : s.phase = .padding := by
  by_contra hn
  have hh := work_prevents_reset p c s hf (work_pos p c s hc ha hn)
  omega

lemma path_inner_sum (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (hclock : ∀ k < n, (path p c answer s ξ k).slot + 1 < macroCalls c) :
    (path p c answer s ξ n).inner = s.inner +
      ∑ k ∈ Finset.range n, if fineMove p c (path p c answer s ξ k) then 1 else 0 := by
  induction n with
  | zero => simp [path, HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    have hh := ih (fun k hk => hclock k (by omega))
    have hp : path p c answer s ξ (n + 1) =
        update p c (path p c answer s ξ n) (ξ n).1
          (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ n _ ξ
    rw [hp, update_inner_increment p c _ _ _ (hclock n (by omega)), hh, Finset.sum_range_succ]
    omega

def modeEntry (p : Params) (c : Config) (s t : State p c) : Bool := !s.fine && t.fine

lemma boolean_transition_count (b : ℕ → Bool) (N : ℕ) :
    (∑ n ∈ Finset.range N, if !b n && b (n + 1) then 1 else 0 : ℕ) +
        (if b 0 then 1 else 0) =
      (∑ n ∈ Finset.range N, if b n && !b (n + 1) then 1 else 0 : ℕ) +
        (if b N then 1 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    cases h0 : b 0 <;> cases hN : b N <;> cases hnext : b (N + 1) <;>
      simp_all

lemma path_entries_le_exits (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (N : ℕ) :
    (∑ n ∈ Finset.range N, if modeEntry p c (path p c answer (initial p c) ξ n)
      (path p c answer (initial p c) ξ (n + 1)) then 1 else 0 : ℕ) ≤
    (∑ n ∈ Finset.range N, if modeExit p c (path p c answer (initial p c) ξ n)
      (path p c answer (initial p c) ξ (n + 1)) then 1 else 0 : ℕ) + 1 := by
  have hh := boolean_transition_count (fun n => (path p c answer (initial p c) ξ n).fine) N
  have h0 : (path p c answer (initial p c) ξ 0).fine = false := rfl
  simp only [h0, Bool.false_eq_true, ite_false, add_zero] at hh
  unfold modeEntry modeExit
  split_ifs at hh <;> omega

noncomputable def coarseMove (p : Params) (c : Config) (s : State p c) (reply : Space p) : Bool := by
  classical
  exact if s.active then if s.fine then false else
    match s.phase with
    | .gradient false j i sum values =>
      if i < c.pilotBatch then false else if j.val + 1 < c.groups + 1 then false else
        let v := OracleTemplate.MultiplicativeRobustEstimator.medoid
          (Function.update values j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))
        decide (‖v‖ ≤ c.guardThreshold ∧ c.radius / 4 < ‖v‖)
    | _ => false
  else false

lemma finishPilot_active_padding (p : Params) (c : Config) (s : State p c) (v : Space p)
    (ha : (finishPilot p c s v).active = true) (hp : (finishPilot p c s v).phase = .padding) :
    ‖v‖ ≤ c.guardThreshold ∧ (s.fine = false ∨ 3 * c.radius ≤ ‖v‖) := by
  unfold finishPilot at ha hp
  by_cases hg : c.guardThreshold < ‖v‖
  · simp [hg] at ha
  · refine ⟨le_of_not_gt hg, ?_⟩
    simp only [hg, ite_false] at ha hp
    cases hf : s.fine with
    | false => exact Or.inl rfl
    | true =>
      right
      simp only [hf, ite_true] at ha hp
      by_contra he
      simp only [he, ite_false] at ha hp
      by_cases hi : s.inner = 0
      · simp [hi] at hp
      · simp only [hi, ite_false] at ha hp
        unfold beginFineStep at ha hp
        split_ifs at ha hp

lemma finishPilot_padding_event (p : Params) (c : Config) (s : State p c) (v : Space p)
    (ha : (finishPilot p c s v).active = true) (hp : (finishPilot p c s v).phase = .padding) :
    modeEntry p c s (finishPilot p c s v) = true ∨
      modeExit p c s (finishPilot p c s v) = true ∨
        (s.fine = false ∧ ‖v‖ ≤ c.guardThreshold ∧ c.radius / 4 < ‖v‖) := by
  obtain ⟨hguard, hcase⟩ := finishPilot_active_padding p c s v ha hp
  have hg : ¬c.guardThreshold < ‖v‖ := not_lt.mpr hguard
  cases hf : s.fine with
  | true =>
    have he : 3 * c.radius ≤ ‖v‖ := by simpa [hf] using hcase
    right
    left
    simp [modeExit, finishPilot, hg, hf, he]
  | false =>
    by_cases he : ‖v‖ ≤ c.radius / 4
    · left
      simp [modeEntry, finishPilot, hg, hf, he]
    · exact Or.inr (Or.inr ⟨rfl, hguard, lt_of_not_ge he⟩)

lemma raw_padding_origin (p : Params) (c : Config) (s : State p c) (reply : Space p)
    (ha : (rawUpdate p c s reply).active = true)
    (hp : (rawUpdate p c s reply).phase = .padding) :
    s.phase = .padding ∨ c.epoch + 1 ≤ (rawUpdate p c s reply).inner ∨
      coarseMove p c s reply = true ∨ modeEntry p c s (rawUpdate p c s reply) = true ∨
        modeExit p c s (rawUpdate p c s reply) = true := by
  cases hs : s.active with
  | false => simp [rawUpdate, hs] at ha
  | true =>
    cases he : s.phase with
    | padding => exact Or.inl rfl
    | transport i sum =>
      simp only [rawUpdate, hs, he, ite_true] at hp ⊢
      by_cases hi : i < c.transportBatch
      · simp [hi] at hp
      · simp only [hi, ite_false] at hp ⊢
        by_cases hn : s.inner < c.epoch
        · simp [hn] at hp
        · right
          left
          omega
    | gradient refresh j i sum values =>
      simp only [rawUpdate, hs, he, ite_true] at ha hp ⊢
      by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
      · simp [hi] at hp
      · simp only [hi, ite_false] at ha hp ⊢
        by_cases hj : j.val + 1 < c.groups + 1
        · simp [hj] at hp
        · simp only [hj, dite_false] at ha hp ⊢
          cases refresh with
          | true =>
            simp only [ite_true] at ha hp ⊢
            unfold beginFineStep at ha hp
            split_ifs at ha hp
          | false =>
            simp only [Bool.false_eq_true, ite_false] at ha hp ⊢
            have hh := finishPilot_padding_event p c s _ ha hp
            rcases hh with hentry | hexit | ⟨hf, hg, hl⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inl hentry)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr hexit)))
            · right
              right
              left
              have hi' : ¬i < c.pilotBatch := by simpa using hi
              simp only [coarseMove, hs, hf, he, hi', hj, ite_true, Bool.false_eq_true,
                ite_false, decide_eq_true_eq]
              exact ⟨hg, hl⟩

noncomputable def stepEvents (p : Params) (c : Config) (s : State p c) (reply : Space p) : ℕ :=
  (if coarseMove p c s reply then 1 else 0) +
    (if modeEntry p c s (rawUpdate p c s reply) then 1 else 0) +
    (if modeExit p c s (rawUpdate p c s reply) then 1 else 0)

lemma raw_padding_credit (p : Params) (c : Config) (s : State p c) (reply : Space p) (R : ℕ)
    (hold : s.active = true → s.phase = .padding → c.epoch + 1 ≤ s.inner + (c.epoch + 1) * R)
    (ha : (rawUpdate p c s reply).active = true)
    (hp : (rawUpdate p c s reply).phase = .padding) :
    c.epoch + 1 ≤ (rawUpdate p c s reply).inner + (c.epoch + 1) * (R + stepEvents p c s reply) := by
  have hs : s.active = true := by
    cases hh : s.active with
    | true => rfl
    | false => simp [rawUpdate, hh] at ha
  have hi : s.inner ≤ (rawUpdate p c s reply).inner := by
    rw [raw_inner_increment]
    omega
  rcases raw_padding_origin p c s reply ha hp with hpad | hinner | hc | hentry | hexit
  · have hh := hold hs hpad
    nlinarith
  · nlinarith
  all_goals
    have hE : 1 ≤ stepEvents p c s reply := by
      unfold stepEvents
      first | rw [hc] | rw [hentry] | rw [hexit]
      simp only [ite_true]
      omega
    nlinarith

lemma path_padding_credit (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) (hstart : s.phase ≠ .padding)
    (hclock : ∀ k < n, (path p c answer s ξ k).slot + 1 < macroCalls c)
    (ha : (path p c answer s ξ n).active = true)
    (hpad : (path p c answer s ξ n).phase = .padding) :
    c.epoch + 1 ≤ (path p c answer s ξ n).inner + (c.epoch + 1) *
      ∑ k ∈ Finset.range n, stepEvents p c (path p c answer s ξ k)
        (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2) := by
  induction n with
  | zero => exact (hstart hpad).elim
  | succ n ih =>
    have hp : path p c answer s ξ (n + 1) =
        update p c (path p c answer s ξ n) (ξ n).1
          (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ n _ ξ
    have hc := hclock n (by omega)
    have hh := raw_padding_credit p c (path p c answer s ξ n)
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2)
      (∑ k ∈ Finset.range n, stepEvents p c (path p c answer s ξ k)
        (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2))
      (fun hactive hphase => ih (fun k hk => hclock k (by omega)) hactive hphase)
      (by simpa only [hp, update, hc, ite_true] using ha)
      (by simpa only [hp, update, hc, ite_true] using hpad)
    simpa only [hp, update, hc, ite_true, Finset.sum_range_succ] using hh

lemma macro_credit (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (hslot : s.slot = 0) (hinner : s.inner = 0) (hstart : s.phase ≠ .padding)
    (ha : (path p c answer s ξ (macroCalls c)).active = true) :
    c.epoch + 1 ≤
      (∑ k ∈ Finset.range (macroCalls c), if fineMove p c (path p c answer s ξ k) then 1 else 0 : ℕ) +
      (c.epoch + 1) * ∑ k ∈ Finset.range (macroCalls c), stepEvents p c (path p c answer s ξ k)
        (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2) := by
  have hM := macroCalls_pos c
  have hlen : macroCalls c - 1 + 1 = macroCalls c := by omega
  have htime (k : ℕ) (hk : k < macroCalls c) : (path p c answer s ξ k).slot = k := by
    rw [HystereticHessianBlocks.path_slot_from p c answer s ξ k hf.1, hslot, Nat.zero_add,
      Nat.mod_eq_of_lt hk]
  have hclock (k : ℕ) (hk : k < macroCalls c - 1) :
      (path p c answer s ξ k).slot + 1 < macroCalls c := by
    rw [htime k (by omega)]
    omega
  have hactive := path_active_prefix p c answer s ξ (n := macroCalls c - 1) (by omega) ha
  have hv := HystereticHessianBlocks.path_invariants p c answer s ξ (macroCalls c - 1) hc hf
  have hpad := active_boundary_padding p c _ hv.1 hv.2 hactive
    (by rw [htime _ (by omega)]; omega)
  have hh := path_padding_credit p c answer s ξ (macroCalls c - 1) hstart hclock hactive hpad
  rw [path_inner_sum p c answer s ξ (macroCalls c - 1) hclock, hinner, Nat.zero_add] at hh
  rw [← hlen, Finset.sum_range_succ, Finset.sum_range_succ]
  exact hh.trans (Nat.add_le_add (Nat.le_add_right _ _)
    (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))

lemma path_macro_shape (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (j : ℕ) :
    let s := path p c answer (initial p c) ξ (j * macroCalls c)
    s.slot = 0 ∧ s.inner = 0 ∧ s.phase = .gradient false 0 0 0 (fun _ => 0) := by
  dsimp only
  constructor
  · rw [path_slot]
    simp
  · cases j with
    | zero => simp [path, HeavyTailedProductProcess.trajectory, initial]
    | succ j =>
      have hM := macroCalls_pos c
      let n := (j + 1) * macroCalls c - 1
      have hlen : n + 1 = (j + 1) * macroCalls c := by
        dsimp [n]
        have : 0 < (j + 1) * macroCalls c := Nat.mul_pos (by omega) hM
        omega
      have hn : n = j * macroCalls c + (macroCalls c - 1) := by
        dsimp [n]
        rw [Nat.add_mul]
        omega
      have hmod : n % macroCalls c + 1 = macroCalls c := by
        rw [hn, Nat.add_mod]
        simp only [Nat.mul_mod_left, Nat.zero_add]
        rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have hclock : ¬(path p c answer (initial p c) ξ n).slot + 1 < macroCalls c := by
        rw [path_slot, hmod]
        omega
      rw [← hlen]
      simp only [path, HeavyTailedProductProcess.trajectory_succ_last]
      change (update p c (path p c answer (initial p c) ξ n) (ξ n).1 _).inner = 0 ∧
        (update p c (path p c answer (initial p c) ξ n) (ξ n).1 _).phase = _
      simp [update, hclock]

lemma trial_macro_credit (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (J : ℕ)
    (ha : (path p c answer (initial p c) ξ (J * macroCalls c)).active = true) :
    J * (c.epoch + 1) ≤
      (∑ k ∈ Finset.range (J * macroCalls c),
        if fineMove p c (path p c answer (initial p c) ξ k) then 1 else 0 : ℕ) +
      (c.epoch + 1) * ∑ k ∈ Finset.range (J * macroCalls c),
        stepEvents p c (path p c answer (initial p c) ξ k)
          (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprev := path_active_prefix p c answer (initial p c) ξ
      (n := J * macroCalls c) (Nat.mul_le_mul_right _ (Nat.le_succ J)) ha
    have hh := ih hprev
    let s := path p c answer (initial p c) ξ (J * macroCalls c)
    let ζ := fun k => ξ (J * macroCalls c + k)
    have heq (k : ℕ) : path p c answer s ζ k =
        path p c answer (initial p c) ξ (J * macroCalls c + k) :=
      (HeavyTailedSospEpochIntegration.trajectory_add _ _ _ _ _).symm
    have hv := HystereticHessianBlocks.path_invariants p c answer (initial p c) ξ
      (J * macroCalls c) (initial_counter_valid p c) (initial_phase_fits p c)
    have hshape := path_macro_shape p c answer ξ J
    have hmacro := macro_credit p c answer s ζ hv.1 hv.2 hshape.1 hshape.2.1
      (by dsimp [s]; rw [hshape.2.2]; intro h; cases h)
      (by rw [heq]; simpa only [Nat.add_mul, Nat.one_mul] using ha)
    simp only [heq, ζ] at hmacro
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul,
      Finset.sum_range_add, Finset.sum_range_add]
    nlinarith

lemma path_stepEvents_eq (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    stepEvents p c (path p c answer s ξ n)
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) =
    (if coarseMove p c (path p c answer s ξ n)
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) then 1 else 0) +
    (if modeEntry p c (path p c answer s ξ n) (path p c answer s ξ (n + 1)) then 1 else 0) +
    (if modeExit p c (path p c answer s ξ n) (path p c answer s ξ (n + 1)) then 1 else 0) := by
  have hfine : (path p c answer s ξ (n + 1)).fine =
      (rawUpdate p c (path p c answer s ξ n)
        (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2)).fine := by
    rw [path, HeavyTailedProductProcess.trajectory_succ_last]
    change (update p c (path p c answer s ξ n) (ξ n).1 _).fine = _
    unfold update
    split_ifs <;> rfl
  simp only [stepEvents, modeEntry, modeExit, hfine]
  congr 2

noncomputable def fineCount (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, if fineMove p c (path p c answer (initial p c) ξ k) then 1 else 0

noncomputable def coarseCount (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, if coarseMove p c (path p c answer (initial p c) ξ k)
    (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2) then 1 else 0

noncomputable def exitCount (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, if modeExit p c (path p c answer (initial p c) ξ k)
    (path p c answer (initial p c) ξ (k + 1)) then 1 else 0

lemma path_event_count_le (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (N : ℕ) :
    (∑ k ∈ Finset.range N, stepEvents p c (path p c answer (initial p c) ξ k)
      (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2)) ≤
      coarseCount p c answer ξ N + 2 * exitCount p c answer ξ N + 1 := by
  simp only [path_stepEvents_eq, Finset.sum_add_distrib, coarseCount, exitCount]
  have hh := path_entries_le_exits p c answer ξ N
  omega

lemma active_macro_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (J : ℕ)
    (ha : (path p c answer (initial p c) ξ (J * macroCalls c)).active = true) :
    J * (c.epoch + 1) ≤ fineCount p c answer ξ (J * macroCalls c) + (c.epoch + 1) *
      (coarseCount p c answer ξ (J * macroCalls c) + 2 * exitCount p c answer ξ (J * macroCalls c) + 1) := by
  exact (trial_macro_credit p c answer ξ J ha).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (path_event_count_le p c answer ξ _)) _)

lemma coarse_uniform_charge (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hU : 0 < c.radius) {M : ℝ} (hUM : c.radius ≤ M)
    (hD : 0 < p.L0 + p.L1 * c.radius)
    (hcap : M / (256 * (p.L0 + p.L1 * M)) ≤ c.coarseCap)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (x v : Space p) (herror : ‖v - g x‖ ≤ (c.radius + ‖g x‖) / 256)
    (hlarge : c.radius / 4 < ‖v‖) :
    c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius)) ≤
      f x - f (x + coarseDisplacement p c v) := by
  have hM : 0 < M := hU.trans_le hUM
  have hDM : 0 < p.L0 + p.L1 * M := by nlinarith
  have hDv : 0 < p.L0 + p.L1 * ‖v‖ := by nlinarith
  have hcap0 : 0 ≤ c.coarseCap := (by positivity : 0 ≤ M / (256 * (p.L0 + p.L1 * M))).trans hcap
  have hh := coarse_move_charge p c f g hL0 hL1 hcap0 hU hf hg hH x v herror hlarge hDv
  have ht := coarse_step_lower hL0 hL1 hU hUM hlarge.le hD hcap
  have ht0 : 0 ≤ min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖))) := by positivity
  have hprod := mul_le_mul ht hh.1.le (by positivity : 0 ≤ c.radius / 8) ht0
  have heq : c.radius / (256 * (p.L0 + p.L1 * c.radius)) * (c.radius / 8) =
      4 * (c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius))) := by
    field_simp
    ring
  rw [heq] at hprod
  linarith

lemma coarseMove_point_accuracy (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p)
    (hp : PilotReplyAccurate p c g s reply) (hc : coarseMove p c s reply = true) :
    ∃ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 ∧ c.radius / 4 < ‖v‖ ∧
      (update p c s u reply).point = s.point + coarseDisplacement p c v := by
  cases ha : s.active with
  | false => simp [coarseMove, ha] at hc
  | true =>
    cases hf : s.fine with
    | true => simp [coarseMove, ha, hf] at hc
    | false =>
      cases he : s.phase with
      | padding => simp [coarseMove, ha, hf, he] at hc
      | transport i sum => simp [coarseMove, ha, hf, he] at hc
      | gradient refresh j i sum values =>
        cases refresh with
        | true => simp [coarseMove, ha, hf, he] at hc
        | false =>
          simp only [coarseMove, ha, hf, he, ite_true, Bool.false_eq_true, ite_false] at hc
          by_cases hi : i < c.pilotBatch
          · simp [hi] at hc
          · simp only [hi, ite_false] at hc
            by_cases hj : j.val + 1 < c.groups + 1
            · simp [hj] at hc
            · simp only [hj, ite_false, decide_eq_true_eq] at hc
              let v := OracleTemplate.MultiplicativeRobustEstimator.medoid
                (Function.update values j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))
              have hv : ‖v‖ ≤ c.guardThreshold ∧ c.radius / 4 < ‖v‖ := hc
              refine ⟨v, hp ha j i sum values he (by omega) (by omega), hv.2, ?_⟩
              have hr : (rawUpdate p c s reply).point = s.point + coarseDisplacement p c v := by
                simp only [rawUpdate, ha, he, ite_true, Bool.false_eq_true, ite_false, hi, hj, dite_false]
                change (finishPilot p c s v).point = _
                simp [finishPilot, not_lt.mpr hv.1, hf, not_le.mpr hv.2]
              unfold update
              split_ifs <;> exact hr

lemma fine_count_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (N : ℕ)
    (hpilot : ∀ n < N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n < N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64) :
    (fineCount p c answer ξ N : ℝ) * (31 * c.accuracy * c.fineStep / 256) ≤ f p.x0 - m := by
  have hmono (n : ℕ) (hn : n < N) := path_step_nonincrease p c answer f g ξ
    hL0 hL1 hη he hcap hU hf hg hH hsmall hbase hm hM hUM hguard hlinear hconstant n
    (fun k hk => hpilot k (by omega)) (fun k hk => hbound k (by omega))
  have hpath (n : ℕ) : path p c answer (initial p c) ξ (n + 1) =
      update p c (path p c answer (initial p c) ξ n) (ξ n).1
        (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2) :=
    HeavyTailedProductProcess.trajectory_succ_last _ n _ ξ
  have hcharge (n : ℕ) (hn : n < N) (ht : fineMove p c (path p c answer (initial p c) ξ n) = true) :
      31 * c.accuracy * c.fineStep / 256 ≤
        f (path p c answer (initial p c) ξ n).point - f (path p c answer (initial p c) ξ (n + 1)).point := by
    rw [hpath]
    exact fine_completed_charge p c f g hL0 hL1 hη he hf hg hH hsmall hbase _ _ _
      (path_move_valid p c answer (initial p c) (by trivial) ξ n) ht
      (path_direction_accurate p c answer g ξ n (fun k hk => hbound k (by omega)))
      (path_transport_threshold p c answer ξ n (fineMove_query p c _ ht))
  have hh := descent_event_count (fun n => f (path p c answer (initial p c) ξ n).point)
    (fun n => fineMove p c (path p c answer (initial p c) ξ n)) N hmono hcharge
  change (fineCount p c answer ξ N : ℝ) * _ ≤ f p.x0 - f (path p c answer (initial p c) ξ N).point at hh
  exact hh.trans (sub_le_sub_left (hm _) _)

lemma coarse_count_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (N : ℕ)
    (hpilot : ∀ n < N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n < N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64)
    (hD : 0 < p.L0 + p.L1 * c.radius)
    (hcapLower : M / (256 * (p.L0 + p.L1 * M)) ≤ c.coarseCap) :
    (coarseCount p c answer ξ N : ℝ) * (c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius))) ≤
      f p.x0 - m := by
  have hmono (n : ℕ) (hn : n < N) := path_step_nonincrease p c answer f g ξ
    hL0 hL1 hη he hcap hU hf hg hH hsmall hbase hm hM hUM hguard hlinear hconstant n
    (fun k hk => hpilot k (by omega)) (fun k hk => hbound k (by omega))
  have hpath (n : ℕ) : path p c answer (initial p c) ξ (n + 1) =
      update p c (path p c answer (initial p c) ξ n) (ξ n).1
        (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2) :=
    HeavyTailedProductProcess.trajectory_succ_last _ n _ ξ
  have hcharge (n : ℕ) (hn : n < N)
      (ht : coarseMove p c (path p c answer (initial p c) ξ n)
        (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2) = true) :
      c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius)) ≤
        f (path p c answer (initial p c) ξ n).point - f (path p c answer (initial p c) ξ (n + 1)).point := by
    obtain ⟨v, hv, hl, hp⟩ := coarseMove_point_accuracy p c g _ (ξ n).1 _ (hpilot n hn) ht
    rw [hpath, hp]
    exact coarse_uniform_charge p c f g hL0 hL1 hU hUM hD hcapLower hf hg hH _ v hv hl
  have hh := descent_event_count (fun n => f (path p c answer (initial p c) ξ n).point)
    (fun n => coarseMove p c (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2)) N hmono hcharge
  change (coarseCount p c answer ξ N : ℝ) * _ ≤ f p.x0 - f (path p c answer (initial p c) ξ N).point at hh
  exact hh.trans (sub_le_sub_left (hm _) _)

lemma exit_count_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (N : ℕ)
    (hpilot : ∀ n < N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n < N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64)
    (hshort : 2 * (p.L0 + 4 * p.L1 * c.radius) * c.fineStep ≤ 31 * c.accuracy / 64) :
    (exitCount p c answer ξ N : ℝ) * (15 * c.radius ^ 2 / 4) ≤
      24 * (p.L0 + 4 * p.L1 * c.radius) * (f p.x0 - m) := by
  have hstep (n : ℕ) (hn : n < N) := path_step_banking p c answer f g ξ
    hL0 hL1 hη he hcap hU hf hg hH hsmall hbase hshort hm hM hUM hguard hlinear hconstant n
    (fun k hk => hpilot k (by omega)) (fun k hk => hbound k (by omega))
  have hh := banking_event_count (fun n => f (path p c answer (initial p c) ξ n).point)
    (fun n => finePotential p c g (path p c answer (initial p c) ξ n))
    (fun n => modeExit p c (path p c answer (initial p c) ξ n)
      (path p c answer (initial p c) ξ (n + 1))) N hstep
  change finePotential p c g (path p c answer (initial p c) ξ N) +
    (exitCount p c answer ξ N : ℝ) * (15 * c.radius ^ 2 / 4) ≤
      0 + 24 * (p.L0 + 4 * p.L1 * c.radius) *
        (f p.x0 - f (path p c answer (initial p c) ξ N).point) at hh
  have hC : 0 ≤ 24 * (p.L0 + 4 * p.L1 * c.radius) := by positivity
  have hd := mul_le_mul_of_nonneg_left (sub_le_sub_left (hm (path p c answer (initial p c) ξ N).point) (f p.x0)) hC
  have hΦ := finePotential_nonneg p c g (path p c answer (initial p c) ξ N)
  linarith

end LongTails.Proofs.HystereticHessianLedger
