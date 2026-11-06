import LongTails.Proofs.HystereticHessianTracking
import LongTails.Proofs.AffineTransportCrossings

namespace LongTails.Proofs.HystereticHessianDescent

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianTransport HystereticHessianMoments HystereticHessianTracking

lemma move_eq_fine (p : Params) (c : Config) (s : State p c)
    (hm : MoveValid p c s) (ht : transportQuery p c s = 1) :
    s.move = fineDisplacement p c s := by
  cases ha : s.active with
  | false => simp [transportQuery, ha] at ht
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he] at ht
    | padding => simp [transportQuery, ha, he] at ht
    | transport i sum => simpa [MoveValid, he] using hm

lemma fine_move_charge (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    (s : State p c) (hm : MoveValid p c s) (ht : transportQuery p c s = 1)
    (herror : DirectionAccurate p c g (c.accuracy / 64) s)
    (hlarge : c.accuracy / 2 < ‖s.estimate‖) :
    31 * c.accuracy / 64 < ‖g s.point‖ ∧
      c.fineStep * ‖g s.point‖ ≤ 4 * (f s.point - f (s.point + s.move)) := by
  have hh := AffineTransportCrossings.threshold_step_charge hL0 hL1 hη he hf hg hH
    hsmall s.point s.estimate (herror ht) hlarge hbase
  rw [move_eq_fine p c s hm ht]
  simpa only [fineDisplacement, sub_eq_add_neg] using hh

lemma path_fine_move_charge (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    (N : ℕ) (ht : transportQuery p c (path p c answer (initial p c) ξ N) = 1)
    (hbound : ∀ n ≤ N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64) :
    let s := path p c answer (initial p c) ξ N
    31 * c.accuracy / 64 < ‖g s.point‖ ∧
      c.fineStep * ‖g s.point‖ ≤ 4 * (f s.point - f (s.point + s.move)) := by
  apply fine_move_charge p c f g hL0 hL1 hη he hf hg hH hsmall hbase
  · exact path_move_valid p c answer (initial p c) (by trivial) ξ N
  · exact ht
  · exact path_direction_accurate p c answer g ξ N hbound
  · exact path_transport_threshold p c answer ξ N ht

lemma coarse_move_charge (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (x v : Space p) (herror : ‖v - g x‖ ≤ (c.radius + ‖g x‖) / 256)
    (hlarge : c.radius / 4 < ‖v‖) (hcurv : 0 < p.L0 + p.L1 * ‖v‖) :
    c.radius / 8 < ‖g x‖ ∧
      min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖))) * ‖g x‖ ≤
        4 * (f x - f (x + coarseDisplacement p c v)) := by
  have htri := norm_le_norm_sub_add v (g x)
  have hrel : ‖v - g x‖ ≤ ‖g x‖ / 16 := by linarith
  have hv : 0 < ‖v‖ := by linarith
  let t := min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖)))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hprod : t * (64 * (p.L0 + p.L1 * ‖v‖)) ≤ ‖v‖ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hmul0 := mul_nonneg ht hL0
  have hmul1 := mul_nonneg ht hL1
  have hsmall : p.L1 * t ≤ 1 / 4 := by nlinarith
  have hbase : p.L0 * t ≤ ‖g x‖ / 8 := by
    nlinarith [mul_nonneg hmul1 (norm_nonneg v)]
  have hd := AffineTransportCrossings.normalized_step_charge hL0 hL1 ht hf hg hH
    hsmall x v (by simpa only [norm_sub_rev] using hrel) hbase
  refine ⟨by linarith, ?_⟩
  simpa only [t, coarseDisplacement, sub_eq_add_neg] using hd

lemma coarse_step_lower {L0 L1 U M v : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hU : 0 < U) (hM : U ≤ M)
    (hv : U / 4 ≤ v) (hD : 0 < L0 + L1 * U)
    {cap : ℝ} (hcap : M / (256 * (L0 + L1 * M)) ≤ cap) :
    U / (256 * (L0 + L1 * U)) ≤ min cap (v / (64 * (L0 + L1 * v))) := by
  have hDM : 0 < L0 + L1 * M := by nlinarith
  have hDv : 0 < L0 + L1 * v := by nlinarith
  apply le_min
  · apply le_trans _ hcap
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hM)]
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg hL0 (show 0 ≤ 4 * v - U by linarith),
      mul_nonneg hL1 (mul_nonneg hU.le (show 0 ≤ v by linarith))]

lemma coarse_move_nonincrease (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (x v : Space p) (herror : ‖v - g x‖ ≤ (c.radius + ‖g x‖) / 256)
    (hlarge : c.radius / 4 < ‖v‖) : f (x + coarseDisplacement p c v) ≤ f x := by
  by_cases hD : 0 < p.L0 + p.L1 * ‖v‖
  · have hh := (coarse_move_charge p c f g hL0 hL1 hcap hU hf hg hH x v herror hlarge hD).2
    have ht : 0 ≤ min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖))) := by positivity
    nlinarith [mul_nonneg ht (norm_nonneg (g x))]
  · have hz : p.L0 + p.L1 * ‖v‖ = 0 := by
      nlinarith [mul_nonneg hL1 (norm_nonneg v)]
    simp [coarseDisplacement, hz, min_eq_right hcap]

lemma finishPilot_sublevel (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (v : Space p) (hs : f s.point ≤ f p.x0)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point) :
    f (finishPilot p c s v).point ≤ f p.x0 := by
  unfold finishPilot
  split_ifs with hguard hf hexit hi hentry
  · exact le_rfl
  · exact hs
  · exact hs
  · unfold beginFineStep
    split_ifs <;> exact hs
  · exact hs
  · exact (hc v hv (by simpa using hentry)).trans hs

lemma raw_update_sublevel (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (reply : Space p) (hs : f s.point ≤ f p.x0)
    (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 → f (s.point + s.move) ≤ f s.point) :
    f (rawUpdate p c s reply).point ≤ f p.x0 := by
  unfold rawUpdate
  cases ha : s.active with
  | false => simpa using hs
  | true =>
    simp only [ite_true]
    cases he : s.phase with
    | padding => exact hs
    | transport i sum =>
      dsimp only
      split_ifs <;> first | exact hs | exact (ht (by simp [transportQuery, ha, he])).trans hs
    | gradient refresh j i sum values =>
      dsimp only
      by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
      · simp only [hi, ite_true]
        exact hs
      · simp only [hi, ite_false]
        by_cases hj : j.val + 1 < c.groups + 1
        · simp only [hj, dite_true]
          exact hs
        · simp only [hj, dite_false]
          cases refresh with
          | true =>
            simp only [ite_true]
            unfold beginFineStep
            split_ifs <;> exact hs
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            apply finishPilot_sublevel p c f g s _ hs _ hc
            exact hp ha j i sum values he (by simpa using hi) (by omega)

lemma update_sublevel (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p) (hs : f s.point ≤ f p.x0)
    (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 → f (s.point + s.move) ≤ f s.point) :
    f (update p c s u reply).point ≤ f p.x0 := by
  have hh := raw_update_sublevel p c f g s reply hs hp hc ht
  unfold update
  split_ifs <;> exact hh

lemma path_sublevel (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hcap : 0 ≤ c.coarseCap) (hU : 0 < c.radius)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    (N : ℕ)
    (hpilot : ∀ n < N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n < N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64) :
    f (path p c answer (initial p c) ξ N).point ≤ f p.x0 := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    have hp : path p c answer (initial p c) ξ (N + 1) =
        update p c (path p c answer (initial p c) ξ N) (ξ N).1
          (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
    rw [hp]
    apply update_sublevel p c f g _ _ _
      (ih (fun n hn => hpilot n (by omega)) (fun n hn => hbound n (by omega)))
      (hpilot N (by omega))
    · intro v hv hl
      exact coarse_move_nonincrease p c f g hL0 hL1 hcap hU hf hg hH _ v hv hl
    · intro ht
      have hh := (path_fine_move_charge p c answer f g ξ hL0 hL1 hη he hf hg hH
        hsmall hbase N ht (fun n hn => hbound n (by omega))).2
      nlinarith [mul_nonneg hη (norm_nonneg (g (path p c answer (initial p c) ξ N).point))]

lemma sublevel_gradient_bound (p : Params) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m M : ℝ} (hm : ∀ x, m ≤ f x) (hM : 0 ≤ M)
    (hlinear : 16 * p.L1 * (f p.x0 - m) ≤ M)
    (hconstant : 16 * p.L0 * (f p.x0 - m) ≤ M ^ 2)
    (x : Space p) (hs : f x ≤ f p.x0) : ‖g x‖ ≤ M := by
  have hh := GuardedGeneralizedGeometry.gradient_gap_exact hL0 hL1 hf hg hH hm x
  have hcurv : 0 ≤ 8 * (p.L0 + p.L1 * ‖g x‖) := by positivity
  have hgap : ‖g x‖ ^ 2 ≤ 8 * (p.L0 + p.L1 * ‖g x‖) * (f p.x0 - m) :=
    hh.trans (mul_le_mul_of_nonneg_left (by linarith) hcurv)
  exact GuardedGeneralizedGeometry.norm_bound_of_gap (norm_nonneg _) hM hgap hlinear hconstant

lemma accurate_pilot_passes_guard (p : Params) (c : Config) (g : Space p → Space p)
    {M : ℝ} (hM : 0 ≤ M) (hU : c.radius ≤ M) (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (x v : Space p) (hx : ‖g x‖ ≤ M)
    (hv : ‖v - g x‖ ≤ (c.radius + ‖g x‖) / 256) : ‖v‖ ≤ c.guardThreshold := by
  have hh := norm_le_norm_sub_add v (g x)
  linarith

lemma zero_curvature_gradient (p : Params) (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ 0) {m : ℝ} (hm : ∀ x, m ≤ f x)
    (x : Space p) : g x = 0 := by
  have hh := GuardedGeneralizedGeometry.gradient_gap_exact (L0 := 0) (L1 := 0)
    (by norm_num) (by norm_num) hf hg (by simpa using hH) hm x
  have hn := norm_nonneg (g x)
  have hz : ‖g x‖ = 0 := by nlinarith
  exact norm_eq_zero.mp hz

lemma finishPilot_nonincrease (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (v : Space p) (hsafe : ‖v‖ ≤ c.guardThreshold)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point) :
    f (finishPilot p c s v).point ≤ f s.point := by
  unfold finishPilot
  rw [ite_eq_right (not_lt.mpr hsafe)]
  split_ifs with hf hexit hi hentry
  · exact le_rfl
  · exact le_rfl
  · unfold beginFineStep
    split_ifs <;> exact le_rfl
  · exact le_rfl
  · exact hc v hv (by simpa using hentry)

lemma raw_update_nonincrease (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (reply : Space p) {M : ℝ}
    (hM : 0 ≤ M) (hU : c.radius ≤ M) (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hx : ‖g s.point‖ ≤ M) (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 → f (s.point + s.move) ≤ f s.point) :
    f (rawUpdate p c s reply).point ≤ f s.point := by
  unfold rawUpdate
  cases ha : s.active with
  | false => simp
  | true =>
    simp only [ite_true]
    cases he : s.phase with
    | padding => exact le_rfl
    | transport i sum =>
      dsimp only
      split_ifs <;> first | exact le_rfl | exact ht (by simp [transportQuery, ha, he])
    | gradient refresh j i sum values =>
      dsimp only
      by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
      · simp only [hi, ite_true]
        exact le_rfl
      · simp only [hi, ite_false]
        by_cases hj : j.val + 1 < c.groups + 1
        · simp only [hj, dite_true]
          exact le_rfl
        · simp only [hj, dite_false]
          cases refresh with
          | true =>
            simp only [ite_true]
            unfold beginFineStep
            split_ifs <;> exact le_rfl
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have hv := hp ha j i sum values he (by simpa using hi) (by omega)
            exact finishPilot_nonincrease p c f g s _
              (accurate_pilot_passes_guard p c g hM hU hguard s.point _ hx hv) hv hc

lemma update_nonincrease (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p) {M : ℝ}
    (hM : 0 ≤ M) (hU : c.radius ≤ M) (hguard : 3 * M / 2 ≤ c.guardThreshold)
    (hx : ‖g s.point‖ ≤ M) (hp : PilotReplyAccurate p c g s reply)
    (hc : ∀ v, ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256 →
      c.radius / 4 < ‖v‖ → f (s.point + coarseDisplacement p c v) ≤ f s.point)
    (ht : transportQuery p c s = 1 → f (s.point + s.move) ≤ f s.point) :
    f (update p c s u reply).point ≤ f s.point := by
  have hh := raw_update_nonincrease p c f g s reply hM hU hguard hx hp hc ht
  unfold update
  split_ifs <;> exact hh

lemma path_step_nonincrease (p : Params) (c : Config) {Ω : Type}
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
    (hpilot : ∀ n ≤ N, PilotReplyAccurate p c g (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2))
    (hbound : ∀ n ≤ N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ c.accuracy / 64) :
    f (path p c answer (initial p c) ξ (N + 1)).point ≤
      f (path p c answer (initial p c) ξ N).point := by
  have hs := path_sublevel p c answer f g ξ hL0 hL1 hη he hcap hU hf hg hH hsmall hbase N
    (fun n hn => hpilot n (by omega)) (fun n hn => hbound n (by omega))
  have hx := sublevel_gradient_bound p f g hL0 hL1 hf hg hH hm hM hlinear hconstant _ hs
  have hp : path p c answer (initial p c) ξ (N + 1) =
      update p c (path p c answer (initial p c) ξ N) (ξ N).1
        (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
    HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
  rw [hp]
  apply update_nonincrease p c f g _ _ _ hM hUM hguard hx (hpilot N le_rfl)
  · intro v hv hl
    exact coarse_move_nonincrease p c f g hL0 hL1 hcap hU hf hg hH _ v hv hl
  · intro ht
    have hh := (path_fine_move_charge p c answer f g ξ hL0 hL1 hη he hf hg hH
      hsmall hbase N ht hbound).2
    nlinarith [mul_nonneg hη (norm_nonneg (g (path p c answer (initial p c) ξ N).point))]

def fineMove (p : Params) (c : Config) (s : State p c) : Bool :=
  if s.active then match s.phase with
    | .transport i _ => decide (c.transportBatch ≤ i)
    | _ => false
  else false

lemma fineMove_query (p : Params) (c : Config) (s : State p c) (ht : fineMove p c s = true) :
    transportQuery p c s = 1 := by
  cases ha : s.active with
  | false => simp [fineMove, ha] at ht
  | true =>
    cases he : s.phase <;> simp_all [fineMove, transportQuery]

lemma fineMove_point (p : Params) (c : Config) (s : State p c) (u : ℝ) (reply : Space p)
    (ht : fineMove p c s = true) : (update p c s u reply).point = s.point + s.move := by
  have hr : (rawUpdate p c s reply).point = s.point + s.move := by
    cases ha : s.active with
    | false => simp [fineMove, ha] at ht
    | true =>
      cases he : s.phase with
      | gradient refresh j i sum values => simp [fineMove, ha, he] at ht
      | padding => simp [fineMove, ha, he] at ht
      | transport i sum =>
        have hi : c.transportBatch ≤ i := by simpa [fineMove, ha, he] using ht
        simp [rawUpdate, ha, he, show ¬i < c.transportBatch by omega]
  unfold update
  split_ifs <;> exact hr

lemma fine_completed_charge (p : Params) (c : Config) (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.fineStep) (he : 0 ≤ c.accuracy)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.accuracy / 512)
    (s : State p c) (u : ℝ) (reply : Space p) (hm : MoveValid p c s)
    (ht : fineMove p c s = true) (herror : DirectionAccurate p c g (c.accuracy / 64) s)
    (hlarge : c.accuracy / 2 < ‖s.estimate‖) :
    31 * c.accuracy * c.fineStep / 256 ≤
      f s.point - f (update p c s u reply).point := by
  have hh := fine_move_charge p c f g hL0 hL1 hη he hf hg hH hsmall hbase s hm
    (fineMove_query p c s ht) herror hlarge
  rw [fineMove_point p c s u reply ht]
  nlinarith [mul_le_mul_of_nonneg_left hh.1.le hη]

lemma descent_event_count (F : ℕ → ℝ) (A : ℕ → Bool) {ρ : ℝ} (N : ℕ)
    (hmono : ∀ n < N, F (n + 1) ≤ F n)
    (hcharge : ∀ n < N, A n = true → ρ ≤ F n - F (n + 1)) :
    ((∑ n ∈ Finset.range N, if A n then 1 else 0 : ℕ) : ℝ) * ρ ≤ F 0 - F N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun n hn => hmono n (by omega)) (fun n hn => hcharge n (by omega))
    rw [Finset.sum_range_succ]
    cases ha : A N with
    | false => simp only [Bool.false_eq_true, ite_false, add_zero]
               linarith [hmono N (by omega)]
    | true => simp only [ite_true, Nat.cast_add, Nat.cast_one]
              have hc := hcharge N (by omega) ha
              nlinarith

end LongTails.Proofs.HystereticHessianDescent
