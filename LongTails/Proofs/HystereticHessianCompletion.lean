import LongTails.Proofs.HystereticHessianLedger
import LongTails.Proofs.HystereticHessianCertificates

namespace LongTails.Proofs.HystereticHessianCompletion

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianTransport HystereticHessianMoments HystereticHessianTracking
open HystereticHessianDescent HystereticHessianLedger

noncomputable def SuccessValid (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) : Prop :=
  s.active = false → s.success = true ∧ ‖g s.point‖ ≤ c.accuracy

lemma initial_success_valid (p : Params) (c : Config) (g : Space p → Space p) :
    SuccessValid p c g (initial p c) := by simp [SuccessValid, initial]

lemma beginFineStep_success_valid (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (ha : s.active = true) (he : 0 ≤ c.accuracy)
    (herror : ‖s.estimate - g s.point‖ ≤ c.accuracy / 64) :
    SuccessValid p c g (beginFineStep p c s) := by
  unfold beginFineStep
  by_cases hs : ‖s.estimate‖ ≤ c.accuracy / 2
  · simp only [hs, ite_true, SuccessValid, true_implies, true_and]
    have hh := norm_le_norm_sub_add (g s.point) s.estimate
    rw [norm_sub_rev] at hh
    linarith
  · simp [hs, SuccessValid, ha]

lemma finishPilot_success_valid (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (v : Space p) (ha : s.active = true) (he : 0 ≤ c.accuracy)
    (hsafe : ‖v‖ ≤ c.guardThreshold)
    (herror : s.fine = true → 0 < s.inner → ‖s.estimate - g s.point‖ ≤ c.accuracy / 64) :
    SuccessValid p c g (finishPilot p c s v) := by
  unfold finishPilot
  rw [ite_eq_right (not_lt.mpr hsafe)]
  by_cases hf : s.fine = true
  · rw [ite_eq_left hf]
    by_cases hx : 3 * c.radius ≤ ‖v‖
    · simp [hx, SuccessValid, ha]
    · rw [ite_eq_right hx]
      by_cases hi : s.inner = 0
      · simp [hi, SuccessValid, ha]
      · rw [ite_eq_right hi]
        exact beginFineStep_success_valid p c g s ha he (herror hf (by omega))
  · rw [ite_eq_right hf]
    split_ifs <;> simp [SuccessValid, ha]

lemma raw_success_valid (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (reply : Space p) {M : ℝ}
    (he : 0 ≤ c.accuracy) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold) (hx : ‖g s.point‖ ≤ M)
    (hs : SuccessValid p c g s) (hp : PilotReplyAccurate p c g s reply)
    (hr : RefreshReplyAccurate p c g (c.accuracy / 64) s reply)
    (htrack : ‖trackedError p c g s‖ ≤ c.accuracy / 64) :
    SuccessValid p c g (rawUpdate p c s reply) := by
  cases ha : s.active with
  | false => simpa [rawUpdate, ha] using hs
  | true =>
    cases ht : s.phase with
    | padding => simpa [rawUpdate, ha, ht] using hs
    | transport i sum =>
      simp only [rawUpdate, ha, ht, ite_true]
      split_ifs <;> simp [SuccessValid]
    | gradient refresh j i sum values =>
      simp only [rawUpdate, ha, ht, ite_true]
      by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
      · simp [hi, SuccessValid]
      · simp only [hi, ite_false]
        by_cases hj : j.val + 1 < c.groups + 1
        · simp [hj, SuccessValid]
        · simp only [hj, dite_false]
          cases refresh with
          | true =>
            simp only [ite_true]
            apply beginFineStep_success_valid p c g _ rfl he
            exact hr ha j i sum values ht (by simpa using hi) (by omega)
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have hv := hp ha j i sum values ht (by simpa using hi) (by omega)
            apply finishPilot_success_valid p c g s _ ha he
              (accurate_pilot_passes_guard p c g hM hUM hguard s.point _ hx hv)
            intro hf hin
            simpa [trackedError, trackingReady, trackerError, ha, hf, ht, hin] using htrack

lemma update_success_valid (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p) {M : ℝ}
    (he : 0 ≤ c.accuracy) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold) (hx : ‖g s.point‖ ≤ M)
    (hs : SuccessValid p c g s) (hp : PilotReplyAccurate p c g s reply)
    (hr : RefreshReplyAccurate p c g (c.accuracy / 64) s reply)
    (htrack : ‖trackedError p c g s‖ ≤ c.accuracy / 64) :
    SuccessValid p c g (update p c s u reply) := by
  have hh := raw_success_valid p c g s reply he hM hUM hguard hx hs hp hr htrack
  unfold update
  split_ifs <;> simpa only [SuccessValid] using hh

lemma path_success_valid (p : Params) (c : Config) {Ω : Type}
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
    (hrefresh : ∀ n < N, RefreshReplyAccurate p c g (c.accuracy / 64)
      (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2)) :
    SuccessValid p c g (path p c answer (initial p c) ξ N) := by
  induction N with
  | zero => exact initial_success_valid p c g
  | succ N ih =>
    have hs := path_sublevel p c answer f g ξ hL0 hL1 hη he hcap hU hf hg hH hsmall hbase N
      (fun n hn => hpilot n (by omega)) (fun n hn => hbound n (by omega))
    have hx := sublevel_gradient_bound p f g hL0 hL1 hf hg hH hm hM hlinear hconstant _ hs
    have hpath : path p c answer (initial p c) ξ (N + 1) =
        update p c (path p c answer (initial p c) ξ N) (ξ N).1
          (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
    rw [hpath]
    exact update_success_valid p c g _ _ _ he hM hUM hguard hx
      (ih (fun n hn => hpilot n (by omega)) (fun n hn => hbound n (by omega))
        (fun n hn => hrefresh n (by omega)))
      (hpilot N (by omega)) (hrefresh N (by omega)) (hbound N (by omega))

lemma output_accuracy_of_inactive (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (hs : SuccessValid p c g s) (ha : s.active = false) :
    ‖g (output p c s)‖ ≤ c.accuracy := by
  obtain ⟨htrue, hacc⟩ := hs ha
  simpa only [output, htrue, ite_true] using hacc

lemma inactive_of_event_bounds (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (ξ : ℕ → ℝ × Ω) (J : ℕ)
    {a b d Δ E : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hF : (fineCount p c answer ξ (J * macroCalls c) : ℝ) * a ≤ Δ)
    (hC : (coarseCount p c answer ξ (J * macroCalls c) : ℝ) * b ≤ Δ)
    (hX : (exitCount p c answer ξ (J * macroCalls c) : ℝ) * d ≤ E)
    (hbudget : Δ / a + (c.epoch + 1 : ℕ) * (Δ / b + 2 * (E / d) + 1) <
      (J : ℝ) * (c.epoch + 1 : ℕ)) :
    (path p c answer (initial p c) ξ (J * macroCalls c)).active = false := by
  apply Bool.eq_false_iff.mpr
  intro hactive
  have hstruct := active_macro_bound p c answer ξ J hactive
  have hreal : (J : ℝ) * (c.epoch + 1 : ℕ) ≤
      (fineCount p c answer ξ (J * macroCalls c) : ℝ) + (c.epoch + 1 : ℕ) *
        ((coarseCount p c answer ξ (J * macroCalls c) : ℝ) +
          2 * (exitCount p c answer ξ (J * macroCalls c) : ℝ) + 1) := by
    exact_mod_cast hstruct
  have hf := (le_div_iff₀ ha).mpr hF
  have hc := (le_div_iff₀ hb).mpr hC
  have hx := (le_div_iff₀ hd).mpr hX
  have hcounts : (coarseCount p c answer ξ (J * macroCalls c) : ℝ) +
      2 * (exitCount p c answer ξ (J * macroCalls c) : ℝ) + 1 ≤ Δ / b + 2 * (E / d) + 1 := by
    linarith
  have hw := mul_le_mul_of_nonneg_left hcounts (by positivity : (0 : ℝ) ≤ (c.epoch + 1 : ℕ))
  linarith

lemma good_path_accuracy (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 < c.fineStep) (he : 0 < c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (J : ℕ)
    (hpilot : ∀ n < J * macroCalls c, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n < J * macroCalls c, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64)
    (hrefresh : ∀ n < J * macroCalls c, RefreshReplyAccurate p c g (c.accuracy / 64)
      (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hD : 0 < p.L0 + p.L1 * c.radius)
    (hcapLower : M / (256 * (p.L0 + p.L1 * M)) ≤ c.coarseCap)
    (hshort : 2 * (p.L0 + 4 * p.L1 * c.radius) * c.fineStep ≤ 31 * c.accuracy / 64)
    (hbudget : (f p.x0 - m) / (31 * c.accuracy * c.fineStep / 256) + (c.epoch + 1 : ℕ) *
      ((f p.x0 - m) / (c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius))) +
        2 * (24 * (p.L0 + 4 * p.L1 * c.radius) * (f p.x0 - m) / (15 * c.radius ^ 2 / 4)) + 1) <
      (J : ℝ) * (c.epoch + 1 : ℕ)) :
    ‖g (output p c (path p c answer (initial p c) ξ (J * macroCalls c)))‖ ≤ c.accuracy := by
  have hF := fine_count_bound p c answer f g ξ hL0 hL1 hη.le he.le hcap hU hf hg hH
    hsmall hbase hm hM hUM hguard hlinear hconstant (J * macroCalls c) hpilot hbound
  have hC := coarse_count_bound p c answer f g ξ hL0 hL1 hη.le he.le hcap hU hf hg hH
    hsmall hbase hm hM hUM hguard hlinear hconstant (J * macroCalls c) hpilot hbound hD hcapLower
  have hX := exit_count_bound p c answer f g ξ hL0 hL1 hη.le he.le hcap hU hf hg hH
    hsmall hbase hm hM hUM hguard hlinear hconstant (J * macroCalls c) hpilot hbound hshort
  have hstop := inactive_of_event_bounds p c answer ξ J (by positivity) (by positivity)
    (by positivity) hF hC hX hbudget
  have hvalid := path_success_valid p c answer f g ξ hL0 hL1 hη.le he.le hcap hU hf hg hH
    hsmall hbase hm hM hUM hguard hlinear hconstant (J * macroCalls c) hpilot hbound hrefresh
  exact output_accuracy_of_inactive p c g _ hvalid hstop

open HystereticHessianCertificates HystereticHessianAnchorBlocks HystereticHessianBlocks
open OracleTemplate.StochasticGeneralized

lemma good_trial_accuracy (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (Q : MeasureTheory.Measure (ℝ × Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 < c.fineStep) (he : 0 < c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    {m M a d : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M) (hUM : c.radius ≤ M)
    (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hae : a ≤ c.accuracy / 64)
    (htrack : 3 * a + (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d ≤ c.accuracy / 64)
    (hb : ∀ t : State p c, ‖transportBias p c Q answer g t‖ ≤ d)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c, ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (hD : 0 < p.L0 + p.L1 * c.radius)
    (hcapLower : M / (256 * (p.L0 + p.L1 * M)) ≤ c.coarseCap)
    (hshort : 2 * (p.L0 + 4 * p.L1 * c.radius) * c.fineStep ≤ 31 * c.accuracy / 64)
    (hbudget : (f p.x0 - m) / (31 * c.accuracy * c.fineStep / 256) + (c.epoch + 1 : ℕ) *
      ((f p.x0 - m) / (c.radius ^ 2 / (8192 * (p.L0 + p.L1 * c.radius))) +
        2 * (24 * (p.L0 + 4 * p.L1 * c.radius) * (f p.x0 - m) / (15 * c.radius ^ 2 / 4)) + 1) <
      ((c.macros + 1 : ℕ) : ℝ) * (c.epoch + 1 : ℕ)) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let bad := fun n (t : BlockState p c g M) w => gradientBlockBad p c answer g a n t.val w
    let start : BlockState p c g M := ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
    (∀ k < blockCap c, blockBad cost next bad start ξ k = false) →
    (∀ j < c.macros + 1, (path p c answer (initial p c) ξ (j * macroCalls c),
      fun k => ξ (j * macroCalls c + k)) ∉ HystereticHessianConcentration.macroBad p c Q answer g a) →
    ‖g (output p c (path p c answer (initial p c) ξ (trialCalls c)))‖ ≤ c.accuracy := by
  intro cost next bad start hgood hnoise
  have hp := good_blocks_pilot_accuracy p c answer g M a hcoarse hfine ξ hgood
  have hr := good_blocks_refresh_accuracy p c answer g M a hU.le hcoarse hfine ξ hgood
  have ht := good_blocks_tracked_accuracy p c Q answer g M a d hU.le hη.le ha hd hb
    hcoarse hfine ξ hgood hnoise
  apply good_path_accuracy p c answer f g ξ hL0 hL1 hη he hcap hU hf hg hH hsmall hbase
    hm hM hUM hguard hlinear hconstant (c.macros + 1) hp
    (fun n hn => (ht n hn).trans htrack) ?_ hD hcapLower hshort hbudget
  intro n hn hactive j i sum values hphase hi hj
  exact (hr n hn hactive j i sum values hphase hi hj).trans hae

end LongTails.Proofs.HystereticHessianCompletion
