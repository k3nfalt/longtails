import LongTails.Proofs.HystereticHessianConcentration

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianTracking

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianTransport HystereticHessianPhases HystereticHessianMoments

noncomputable def trackerError (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) : Space p :=
  s.estimate - g s.point + match s.phase with
    | .transport i sum => ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
        (sum - (i : ℝ) • (g (s.point + s.move) - g s.point))
    | _ => 0

lemma corrected_sum_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : ℝ) (i : ℕ) (sum z δ : E) :
    b⁻¹ • (sum + z - ((i + 1 : ℕ) : ℝ) • δ) =
      b⁻¹ • (sum - (i : ℝ) • δ) + b⁻¹ • (z - δ) := by
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, smul_sub, smul_add]
  abel

lemma corrected_sum_last {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (sum z δ : E) :
    ((n + 1 : ℕ) : ℝ)⁻¹ • (sum - (n : ℝ) • δ) +
      ((n + 1 : ℕ) : ℝ)⁻¹ • (z - δ) =
        ((n + 1 : ℕ) : ℝ)⁻¹ • (sum + z) - δ := by
  rw [← corrected_sum_step]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

lemma raw_transport_error (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (reply : Space p) (i : ℕ) (sum : Space p)
    (ha : s.active = true) (he : s.phase = .transport i sum) (hi : i ≤ c.transportBatch) :
    trackerError p c g (rawUpdate p c s reply) = trackerError p c g s +
      ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
        (OracleTemplate.clip c.clipThreshold reply - (g (s.point + s.move) - g s.point)) := by
  simp only [rawUpdate, ha, he, ite_true]
  by_cases hb : i < c.transportBatch
  · rw [ite_eq_left hb]
    simp only [trackerError, he]
    rw [corrected_sum_step]
    abel
  · rw [ite_eq_right hb]
    have hie : i = c.transportBatch := by omega
    by_cases hn : s.inner < c.epoch
    all_goals simp only [hn, ite_true, ite_false, trackerError, he, hie, add_zero]
    all_goals rw [add_assoc, corrected_sum_last]
    all_goals abel

lemma update_transport_error (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (reply : Space p) (u : ℝ)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (ht : transportQuery p c s = 1) :
    trackerError p c g (update p c s u reply) = trackerError p c g s +
      ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
        (OracleTemplate.clip c.clipThreshold reply - (g (s.point + s.move) - g s.point)) := by
  have hclock : s.slot + 1 < macroCalls c := by
    by_contra h
    have hh := transport_query_before_reset p c s hc hf h
    omega
  simp only [update, hclock, ite_true]
  cases ha : s.active with
  | false => simp [transportQuery, ha] at ht
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he] at ht
    | padding => simp [transportQuery, ha, he] at ht
    | transport i sum =>
      have hh : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hc.2
      exact raw_transport_error p c g s reply i sum ha he hh.2

noncomputable def transportBias (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) : Space p :=
  if localMask p c g s then ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
    ((∫ w, OracleTemplate.clip c.clipThreshold (answer (query p c s w.1) w.2) ∂Q) -
      (g (s.point + s.move) - g s.point))
  else 0

lemma update_transport_error_split (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (z : ℝ × Ω)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (hm : localMask p c g s = true) :
    trackerError p c g (update p c s z.1 (answer (query p c s z.1) z.2)) =
      trackerError p c g s + transportNoise p c Q answer g s z + transportBias p c Q answer g s := by
  rw [update_transport_error p c g s _ z.1 hc hf (localMask_transport p c g s hm)]
  simp only [transportNoise, transportBias, hm, ite_true, smul_sub]
  abel

lemma restarted_error_bound {E : Type*} [NormedAddCommGroup E]
    (err noise bias : ℕ → E) (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (hinit : err 0 = 0)
    (hstep : ∀ k < N, ‖err (k + 1)‖ ≤ a ∨ err (k + 1) = err k + noise k + bias k)
    (hnoise : ∀ k ≤ N, ‖∑ i ∈ Finset.range k, noise i‖ ≤ a) :
    ‖err N‖ ≤ 3 * a + ∑ i ∈ Finset.range N, ‖bias i‖ := by
  have haux : ∀ n ≤ N, ‖err n - ∑ i ∈ Finset.range n, noise i‖ ≤
      2 * a + ∑ i ∈ Finset.range n, ‖bias i‖ := by
    intro n
    induction n with
    | zero => simp [hinit, ha]
    | succ n ih =>
      intro hn
      rcases hstep n (by omega) with hr | he
      · have hb := norm_sub_le (err (n + 1)) (∑ i ∈ Finset.range (n + 1), noise i)
        have hs := hnoise (n + 1) hn
        have hpos : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖bias i‖ :=
          Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        linarith
      · have hh := ih (by omega)
        rw [Finset.sum_range_succ, he]
        have heq : err n + noise n + bias n - ((∑ i ∈ Finset.range n, noise i) + noise n) =
            (err n - ∑ i ∈ Finset.range n, noise i) + bias n := by abel
        rw [heq, Finset.sum_range_succ]
        have hb := norm_add_le (err n - ∑ i ∈ Finset.range n, noise i) (bias n)
        linarith
  have hh := haux N le_rfl
  have hs := hnoise N le_rfl
  have hb := norm_le_norm_sub_add (err N) (∑ i ∈ Finset.range N, noise i)
  linarith

lemma transportBias_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hq : 1 ≤ p.q) (hq2 : p.q ≤ 2)
    (hσ : 0 ≤ p.σh) (hα : 0 ≤ p.αh) (hU : 0 < c.radius) (hη : 0 ≤ c.fineStep)
    (hτ : 0 < c.clipThreshold) {K : ℝ}
    (hK : p.L0 + p.L1 * (4 * c.radius) + p.σh + p.αh * (4 * c.radius) ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hi : ∀ y v, Integrable (answer (y, some v)) P)
    (hm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (hsmall : p.L1 * c.fineStep ≤ 1 / 4) (hbase : p.L0 * c.fineStep ≤ c.radius)
    (s : State p c) :
    let Q := (LongTails.Algorithms.GuardedHessianTransport.uniformLaw : Measure ℝ).prod P
    ‖transportBias p c Q answer g s‖ ≤
      ((512 * K * c.fineStep) ^ p.q / (c.clipThreshold / 2) ^ (p.q - 1)) /
        ((c.transportBatch + 1 : ℕ) : ℝ) := by
  intro Q
  have hK0 : 0 ≤ K := by
    nlinarith [mul_nonneg hL1 (by positivity : 0 ≤ 4 * c.radius),
      mul_nonneg hα (by positivity : 0 ≤ 4 * c.radius)]
  by_cases hmask : localMask p c g s = true
  · have hs := localMask_bounds p c g s hmask
    let H := fun (yv : Space p × Space p) (ω : Ω) => answer (yv.1, some yv.2) ω
    have hHm : Measurable (Function.uncurry H) :=
      ha.comp ((measurable_fst.fst.prodMk
        (HystereticHessianMeasurable.measurable_some.comp measurable_fst.snd)).prodMk measurable_snd)
    have hc := local_segment_clipping hL0 hL1 hq hq2 hσ hα
      (by positivity : 0 < 4 * c.radius) hη hK hg hD hH H hHm hi hm hpi hb
      s.point s.move hs.2.1 hs.2.2 hsmall (by nlinarith [hbase]) hτ
    have hclip : ‖(∫ w : ℝ × Ω, OracleTemplate.clip c.clipThreshold
        (answer (s.point + w.1 • s.move, some s.move) w.2) ∂Q) -
          (g (s.point + s.move) - g s.point)‖ ≤
        (512 * K * c.fineStep) ^ p.q / (c.clipThreshold / 2) ^ (p.q - 1) := hc.1
    have hinv : 0 ≤ ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ := by positivity
    simp only [transportBias, hmask, ite_true, query_of_transport p c s hs.1,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hclip hinv
  · have hf : localMask p c g s = false := Bool.eq_false_iff.mpr hmask
    simp only [transportBias, hf, Bool.false_eq_true, ite_false, norm_zero]
    positivity

def ModeValid (p : Params) (c : Config) (s : State p c) : Prop :=
  match s.phase with
    | .transport _ _ => s.fine = true
    | .gradient refresh _ _ _ _ => (refresh = true → s.fine = true) ∧ (0 < s.inner → s.fine = true)
    | .padding => True

lemma beginFineStep_mode_valid (p : Params) (c : Config) (s : State p c)
    (hf : s.fine = true) : ModeValid p c (beginFineStep p c s) := by
  unfold beginFineStep
  split_ifs <;> simp [ModeValid, hf]

lemma finishPilot_mode_valid (p : Params) (c : Config) (s : State p c) (v : Space p) :
    ModeValid p c (finishPilot p c s v) := by
  unfold finishPilot
  split_ifs
  all_goals first
    | apply beginFineStep_mode_valid; assumption
    | simp_all [ModeValid]

lemma raw_mode_valid (p : Params) (c : Config) (s : State p c)
    (hs : ModeValid p c s) (reply : Space p) : ModeValid p c (rawUpdate p c s reply) := by
  cases ha : s.active with
  | false => simpa [rawUpdate, ha] using hs
  | true =>
    cases he : s.phase with
    | padding => simpa [rawUpdate, ha, he] using hs
    | transport i sum =>
      have hf : s.fine = true := by simpa [ModeValid, he] using hs
      simp only [rawUpdate, ha, he, ite_true]
      split_ifs <;> simp [ModeValid, hf]
    | gradient refresh j i sum values =>
      have hf : (refresh = true → s.fine = true) ∧ (0 < s.inner → s.fine = true) := by
        simpa [ModeValid, he] using hs
      simp only [rawUpdate, ha, he, ite_true]
      cases refresh with
      | true =>
        have hft : s.fine = true := hf.1 rfl
        simp only [ite_true]
        split_ifs
        all_goals first
          | exact beginFineStep_mode_valid p c _ hft
          | simp [ModeValid, hft]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        split_ifs
        all_goals first
          | exact finishPilot_mode_valid p c s _
          | simpa only [ModeValid, Bool.false_eq_true, false_implies, true_and] using hf.2

lemma update_mode_valid (p : Params) (c : Config) (s : State p c)
    (hs : ModeValid p c s) (u : ℝ) (reply : Space p) : ModeValid p c (update p c s u reply) := by
  unfold update
  split_ifs
  · exact raw_mode_valid p c s hs reply
  · simp [ModeValid]

lemma path_mode_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (hs : ModeValid p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    ModeValid p c (path p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact hs
  | succ n ih => exact ih _ (update_mode_valid p c s hs (ξ 0).1 _) _

def trackingReady (p : Params) (c : Config) (s : State p c) : Bool :=
  if s.active then if s.fine then match s.phase with
    | .transport _ _ => true
    | _ => decide (0 < s.inner)
  else false else false

noncomputable def trackedError (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) : Space p :=
  if trackingReady p c s then trackerError p c g s else 0

lemma trackedError_initial (p : Params) (c : Config) (g : Space p → Space p) :
    trackedError p c g (initial p c) = 0 := by
  simp [trackedError, trackingReady, initial]

lemma beginFineStep_trackerError (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) :
    trackerError p c g (beginFineStep p c s) = s.estimate - g s.point := by
  unfold beginFineStep
  split_ifs <;> simp [trackerError]

lemma beginFineStep_tracked_bound (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    {a : ℝ} (ha : 0 ≤ a) (he : ‖s.estimate - g s.point‖ ≤ a) :
    ‖trackedError p c g (beginFineStep p c s)‖ ≤ a := by
  unfold trackedError
  split_ifs
  · rw [beginFineStep_trackerError]
    exact he
  · simpa only [norm_zero] using ha

lemma finishPilot_tracked (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (v : Space p) (j : Fin (c.groups + 1)) (i : ℕ)
    (sum : Space p) (values : Fin (c.groups + 1) → Space p)
    (he : s.phase = .gradient false j i sum values) (ha : s.active = true) (hm : ModeValid p c s) :
    trackedError p c g (finishPilot p c s v) = trackedError p c g s ∨
      trackedError p c g (finishPilot p c s v) = 0 := by
  have hinner : 0 < s.inner → s.fine = true := by
    have hh : (false = true → s.fine = true) ∧ (0 < s.inner → s.fine = true) := by
      simpa [ModeValid, he] using hm
    exact hh.2
  unfold finishPilot
  by_cases hguard : c.guardThreshold < ‖v‖
  · rw [ite_eq_left hguard]
    right
    simp [trackedError, trackingReady]
  · rw [ite_eq_right hguard]
    by_cases hf : s.fine = true
    · rw [ite_eq_left hf]
      by_cases hx : 3 * c.radius ≤ ‖v‖
      · rw [ite_eq_left hx]
        right
        simp [trackedError, trackingReady, ha]
      · rw [ite_eq_right hx]
        by_cases hi : s.inner = 0
        · rw [ite_eq_left hi]
          right
          simp [trackedError, trackingReady, ha, hf, hi]
        · rw [ite_eq_right hi]
          have hp : 0 < s.inner := by omega
          unfold beginFineStep
          split_ifs
          · right
            simp [trackedError, trackingReady]
          · left
            simp [trackedError, trackingReady, trackerError, ha, hf, he, hp]
    · rw [ite_eq_right hf]
      have hi : s.inner = 0 := by
        by_contra hn
        exact hf (hinner (by omega))
      split_ifs
      all_goals right
      all_goals simp [trackedError, trackingReady, ha, hf, hi]

lemma trackingReady_of_transport (p : Params) (c : Config) (s : State p c)
    (hm : ModeValid p c s) (ht : transportQuery p c s = 1) : trackingReady p c s = true := by
  cases ha : s.active with
  | false => simp [transportQuery, ha] at ht
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he] at ht
    | padding => simp [transportQuery, ha, he] at ht
    | transport i sum =>
      have hf : s.fine = true := by simpa [ModeValid, he] using hm
      simp [trackingReady, ha, hf, he]

lemma trackingReady_after_transport (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (hm : ModeValid p c s)
    (ht : transportQuery p c s = 1) (u : ℝ) (reply : Space p) :
    trackingReady p c (update p c s u reply) = true := by
  have hclock : s.slot + 1 < macroCalls c := by
    by_contra hn
    have hh := transport_query_before_reset p c s hc hf hn
    omega
  cases ha : s.active with
  | false => simp [transportQuery, ha] at ht
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he] at ht
    | padding => simp [transportQuery, ha, he] at ht
    | transport i sum =>
      have hfi : s.fine = true := by simpa [ModeValid, he] using hm
      simp only [update, hclock, ite_true, rawUpdate, ha, he]
      split_ifs <;> simp [trackingReady, hfi]

lemma noise_bias_zero (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (ht : transportQuery p c s = 0) (z : ℝ × Ω) :
    transportNoise p c Q answer g s z = 0 ∧ transportBias p c Q answer g s = 0 := by
  have hm : localMask p c g s = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hq := localMask_transport p c g s hh
    omega
  simp [transportNoise, transportBias, hm]

def RefreshReplyAccurate (p : Params) (c : Config) (g : Space p → Space p) (a : ℝ)
    (s : State p c) (reply : Space p) : Prop :=
  s.active = true → ∀ j i sum values, s.phase = .gradient true j i sum values →
    c.resetBatch ≤ i → c.groups ≤ j.val →
      ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (Function.update values j (((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply))) - g s.point‖ ≤ a

lemma tracked_update_dichotomy (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (z : ℝ × Ω) {a : ℝ} (ha0 : 0 ≤ a)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (hm : ModeValid p c s)
    (hl : transportQuery p c s = 1 → localMask p c g s = true)
    (hr : RefreshReplyAccurate p c g a s (answer (query p c s z.1) z.2)) :
    ‖trackedError p c g (update p c s z.1 (answer (query p c s z.1) z.2))‖ ≤ a ∨
      trackedError p c g (update p c s z.1 (answer (query p c s z.1) z.2)) =
        trackedError p c g s + transportNoise p c Q answer g s z + transportBias p c Q answer g s := by
  by_cases ht : transportQuery p c s = 1
  · right
    have hbefore := trackingReady_of_transport p c s hm ht
    have hafter := trackingReady_after_transport p c s hc hf hm ht z.1 (answer (query p c s z.1) z.2)
    simp only [trackedError, hbefore, hafter, ite_true]
    exact update_transport_error_split p c Q answer g s z hc hf (hl ht)
  · have ht0 : transportQuery p c s = 0 := by
      cases ha : s.active <;> cases he : s.phase <;> simp_all [transportQuery]
    have hz := noise_bias_zero p c Q answer g s ht0 z
    rw [hz.1, hz.2, add_zero, add_zero]
    by_cases hclock : s.slot + 1 < macroCalls c
    · simp only [update, hclock, ite_true]
      change ‖trackedError p c g (rawUpdate p c s (answer (query p c s z.1) z.2))‖ ≤ a ∨
        trackedError p c g (rawUpdate p c s (answer (query p c s z.1) z.2)) = trackedError p c g s
      cases ha : s.active with
      | false =>
        right
        simp [rawUpdate, ha]
      | true =>
        cases he : s.phase with
        | transport i sum => simp [transportQuery, ha, he] at ht0
        | padding =>
          right
          simp [rawUpdate, ha, he]
        | gradient refresh j i sum values =>
          simp only [rawUpdate, ha, he, ite_true]
          cases refresh with
          | true =>
            simp only [ite_true]
            by_cases hi : i < c.resetBatch
            · rw [ite_eq_left hi]
              right
              simp [trackedError, trackingReady, trackerError, he, ha]
            · rw [ite_eq_right hi]
              by_cases hj : j.val + 1 < c.groups + 1
              · rw [dite_eq_left hj]
                right
                simp [trackedError, trackingReady, trackerError, he, ha]
              · rw [dite_eq_right hj]
                left
                exact beginFineStep_tracked_bound p c g _ ha0
                  (hr ha j i sum values he (by omega) (by omega))
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            by_cases hi : i < c.pilotBatch
            · rw [ite_eq_left hi]
              right
              simp [trackedError, trackingReady, trackerError, he, ha]
            · rw [ite_eq_right hi]
              by_cases hj : j.val + 1 < c.groups + 1
              · rw [dite_eq_left hj]
                right
                simp [trackedError, trackingReady, trackerError, he, ha]
              · rw [dite_eq_right hj]
                rcases finishPilot_tracked p c g s _ j i sum values he ha hm with hh | hh
                · exact Or.inr hh
                · left
                  rw [hh, norm_zero]
                  exact ha0
    · left
      simp [update, hclock, trackedError, trackingReady, ha0]

lemma macro_bias_sum_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (ξ : ℕ → ℝ × Ω)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ t : State p c, ‖transportBias p c Q answer g t‖ ≤ d)
    (n : ℕ) (hn : n ≤ macroCalls c - s.slot) :
    (∑ k ∈ Finset.range n, ‖transportBias p c Q answer g (path p c answer s ξ k)‖) ≤
      (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d := by
  have hpoint (t : State p c) : ‖transportBias p c Q answer g t‖ ≤ (transportQuery p c t : ℝ) * d := by
    by_cases ht : transportQuery p c t = 1
    · simpa only [ht, Nat.cast_one, one_mul] using hb t
    · have ht0 : transportQuery p c t = 0 := by
        cases ha : t.active <;> cases he : t.phase <;> simp_all [transportQuery]
      have hm : localMask p c g t = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        have hh' := localMask_transport p c g t hh
        omega
      simp [transportBias, hm, ht0]
  have hcount : ((∑ k ∈ Finset.range (macroCalls c - s.slot),
      transportQuery p c (path p c answer s ξ k) : ℕ) : ℝ) ≤
        (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) := by
    exact_mod_cast macro_transport_count p c answer s ξ hc hf
  calc
    _ ≤ ∑ k ∈ Finset.range (macroCalls c - s.slot),
        ‖transportBias p c Q answer g (path p c answer s ξ k)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ k ∈ Finset.range (macroCalls c - s.slot),
        (transportQuery p c (path p c answer s ξ k) : ℝ) * d :=
      Finset.sum_le_sum (fun k _ => hpoint _)
    _ = ((∑ k ∈ Finset.range (macroCalls c - s.slot),
        transportQuery p c (path p c answer s ξ k) : ℕ) : ℝ) * d := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hd

lemma path_tracked_error_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (ξ : ℕ → ℝ × Ω)
    (hc : CounterValid p c s) (hf : PhaseFits p c s) (hm : ModeValid p c s)
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hinit : trackedError p c g s = 0)
    (hb : ∀ t : State p c, ‖transportBias p c Q answer g t‖ ≤ d)
    (n : ℕ) (hn : n ≤ macroCalls c - s.slot)
    (hl : ∀ k < n, transportQuery p c (path p c answer s ξ k) = 1 →
      localMask p c g (path p c answer s ξ k) = true)
    (hr : ∀ k < n, RefreshReplyAccurate p c g a (path p c answer s ξ k)
      (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2))
    (hnoise : ∀ k ≤ n, ‖∑ i ∈ Finset.range k,
      transportNoise p c Q answer g (path p c answer s ξ i) (ξ i)‖ ≤ a) :
    ‖trackedError p c g (path p c answer s ξ n)‖ ≤
      3 * a + (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d := by
  have hstep (k : ℕ) (hk : k < n) := tracked_update_dichotomy p c Q answer g
    (path p c answer s ξ k) (ξ k) ha
    (HystereticHessianBlocks.path_invariants p c answer s ξ k hc hf).1
    (HystereticHessianBlocks.path_invariants p c answer s ξ k hc hf).2
    (path_mode_valid p c answer s hm ξ k) (hl k hk) (hr k hk)
  have hpath (k : ℕ) : path p c answer s ξ (k + 1) =
      update p c (path p c answer s ξ k) (ξ k).1
        (answer (query p c (path p c answer s ξ k) (ξ k).1) (ξ k).2) :=
    HeavyTailedProductProcess.trajectory_succ_last _ k s ξ
  have hh := restarted_error_bound (fun k => trackedError p c g (path p c answer s ξ k))
    (fun k => transportNoise p c Q answer g (path p c answer s ξ k) (ξ k))
    (fun k => transportBias p c Q answer g (path p c answer s ξ k)) n ha hinit
    (fun k hk => by simpa only [hpath] using hstep k hk) hnoise
  have hsum := macro_bias_sum_bound p c Q answer g s ξ hc hf hd hb n hn
  linarith

lemma trackedError_at_macro_boundary (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ξ : ℕ → ℝ × Ω) (j : ℕ) :
    trackedError p c g (path p c answer (initial p c) ξ (j * macroCalls c)) = 0 := by
  cases j with
  | zero => simpa [path, HeavyTailedProductProcess.trajectory] using trackedError_initial p c g
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
    change trackedError p c g (update p c (path p c answer (initial p c) ξ n) (ξ n).1 _) = 0
    simp [update, hclock, trackedError, trackingReady]

lemma trackedError_transport_entry (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (ha : s.active = true) (hf : s.fine = true)
    (he : s.phase = .transport 0 0) :
    trackedError p c g s = s.estimate - g s.point := by
  simp [trackedError, trackingReady, trackerError, ha, hf, he]

lemma transport_prefix_stored_error (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (ha : s.active = true) (hn : n ≤ c.transportBatch) (hclock : s.slot + n < macroCalls c) :
    let t := path p c answer { s with phase := .transport 0 0 } ξ n
    t.estimate - g t.point = s.estimate - g s.point := by
  dsimp only
  rw [HystereticHessianBlocks.transport_prefix p c s answer ξ n ha hn hclock]

lemma trial_tracked_error_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ξ : ℕ → ℝ × Ω)
    (hU : 0 ≤ c.radius) (hstep : 0 ≤ c.fineStep)
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hb : ∀ t : State p c, ‖transportBias p c Q answer g t‖ ≤ d)
    (j n : ℕ) (hn : n ≤ macroCalls c)
    (hp : ∀ k < j * macroCalls c + n,
      PilotReplyAccurate p c g (path p c answer (initial p c) ξ k)
        (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2))
    (hr : ∀ k < j * macroCalls c + n,
      RefreshReplyAccurate p c g a (path p c answer (initial p c) ξ k)
        (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2))
    (hnoise : ∀ k ≤ n, ‖∑ i ∈ Finset.range k,
      transportNoise p c Q answer g
        (path p c answer (initial p c) ξ (j * macroCalls c + i)) (ξ (j * macroCalls c + i))‖ ≤ a) :
    ‖trackedError p c g (path p c answer (initial p c) ξ (j * macroCalls c + n))‖ ≤
      3 * a + (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d := by
  let s := path p c answer (initial p c) ξ (j * macroCalls c)
  let ζ := fun k => ξ (j * macroCalls c + k)
  have heq (k : ℕ) : path p c answer s ζ k =
      path p c answer (initial p c) ξ (j * macroCalls c + k) :=
    (HeavyTailedSospEpochIntegration.trajectory_add _ _ _ _ _).symm
  have hs : s.slot = 0 := by
    dsimp [s]
    rw [path_slot]
    simp
  have hv := HystereticHessianBlocks.path_invariants p c answer (initial p c) ξ
    (j * macroCalls c) (initial_counter_valid p c) (initial_phase_fits p c)
  have hm := path_mode_valid p c answer (initial p c) (by simp [ModeValid, initial]) ξ
    (j * macroCalls c)
  have hh := path_tracked_error_bound p c Q answer g s ζ hv.1 hv.2 hm ha hd
    (trackedError_at_macro_boundary p c answer g ξ j) hb n (by simpa [hs] using hn)
    (fun k hk ht => by
      rw [heq] at ht ⊢
      exact path_localMask_active p c answer g hU hstep ξ _
        (fun i hi => hp i (by omega)) ht)
    (fun k hk => by
      simpa only [heq] using hr (j * macroCalls c + k) (by omega))
    (fun k hk => by
      simpa only [heq] using hnoise k hk)
  simpa only [heq] using hh

def DirectionAccurate (p : Params) (c : Config) (g : Space p → Space p) (a : ℝ)
    (s : State p c) : Prop :=
  transportQuery p c s = 1 → ‖s.estimate - g s.point‖ ≤ a

lemma update_transport_direction (p : Params) (c : Config) (s : State p c)
    (u : ℝ) (reply : Space p)
    (ht : transportQuery p c (update p c s u reply) = 1) :
    (transportQuery p c s = 1 ∧
      (update p c s u reply).estimate = s.estimate ∧
      (update p c s u reply).point = s.point) ∨
      ((update p c s u reply).phase = .transport 0 0 ∧
        c.accuracy / 2 < ‖(update p c s u reply).estimate‖) := by
  unfold update at ht ⊢
  split_ifs at ht ⊢ with hclock
  · cases ha : s.active with
    | false => simp [rawUpdate, ha, transportQuery] at ht
    | true =>
      cases he : s.phase with
      | padding => simp [rawUpdate, ha, he, transportQuery] at ht
      | transport i sum =>
        simp only [rawUpdate, ha, he, ite_true] at ht ⊢
        by_cases hi : i < c.transportBatch
        · simp only [hi, ite_true] at ht ⊢
          left
          simp [transportQuery, ha, he]
        · by_cases hh : s.inner < c.epoch <;> simp [hi, hh, transportQuery] at ht
      | gradient refresh j i sum values =>
        simp only [rawUpdate, ha, he, ite_true] at ht ⊢
        by_cases hi : i < if refresh then c.resetBatch else c.pilotBatch
        · simp [hi, transportQuery] at ht
        · simp only [hi, ite_false] at ht ⊢
          by_cases hj : j.val + 1 < c.groups + 1
          · simp [hj, transportQuery] at ht
          · simp only [hj, dite_false] at ht ⊢
            right
            cases refresh <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ht ⊢
            · unfold finishPilot at ht ⊢
              split_ifs at ht ⊢ <;> try simp [transportQuery] at ht
              all_goals unfold beginFineStep at ht ⊢
              all_goals (split_ifs at ht ⊢; simp_all)
            · unfold beginFineStep at ht ⊢
              split_ifs at ht ⊢ <;> simp_all [transportQuery]
  · simp [transportQuery] at ht

lemma update_direction_accurate (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (u : ℝ) (reply : Space p) {a : ℝ}
    (hs : DirectionAccurate p c g a s) (hm : ModeValid p c (update p c s u reply))
    (hn : ‖trackedError p c g (update p c s u reply)‖ ≤ a) :
    DirectionAccurate p c g a (update p c s u reply) := by
  intro ht
  rcases update_transport_direction p c s u reply ht with ⟨hold, he, hp⟩ | ⟨he, _⟩
  · rw [he, hp]
    exact hs hold
  · have ha : (update p c s u reply).active = true := by
      cases hh : (update p c s u reply).active <;> simp_all [transportQuery]
    have hf : (update p c s u reply).fine = true := by simpa [ModeValid, he] using hm
    rwa [trackedError_transport_entry p c g _ ha hf he] at hn

lemma path_direction_accurate (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ξ : ℕ → ℝ × Ω) {a : ℝ} (N : ℕ)
    (hbound : ∀ n ≤ N, ‖trackedError p c g (path p c answer (initial p c) ξ n)‖ ≤ a) :
    DirectionAccurate p c g a (path p c answer (initial p c) ξ N) := by
  induction N with
  | zero => simp [DirectionAccurate, path, HeavyTailedProductProcess.trajectory, initial, transportQuery]
  | succ N ih =>
    have hp : path p c answer (initial p c) ξ (N + 1) =
        update p c (path p c answer (initial p c) ξ N) (ξ N).1
          (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
    rw [hp]
    apply update_direction_accurate p c g _ _ _ (ih (fun n hn => hbound n (by omega)))
    · rw [← hp]
      exact path_mode_valid p c answer (initial p c) (by simp [ModeValid, initial]) ξ (N + 1)
    · simpa only [hp] using hbound (N + 1) (by omega)

lemma path_transport_threshold (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (N : ℕ)
    (ht : transportQuery p c (path p c answer (initial p c) ξ N) = 1) :
    c.accuracy / 2 < ‖(path p c answer (initial p c) ξ N).estimate‖ := by
  induction N with
  | zero => simp [path, HeavyTailedProductProcess.trajectory, initial, transportQuery] at ht
  | succ N ih =>
    have hp : path p c answer (initial p c) ξ (N + 1) =
        update p c (path p c answer (initial p c) ξ N) (ξ N).1
          (answer (query p c (path p c answer (initial p c) ξ N) (ξ N).1) (ξ N).2) :=
      HeavyTailedProductProcess.trajectory_succ_last _ N _ ξ
    rw [hp] at ht ⊢
    rcases update_transport_direction p c _ _ _ ht with ⟨hold, he, _⟩ | ⟨_, hlarge⟩
    · rw [he]
      exact ih hold
    · exact hlarge

end LongTails.Proofs.HystereticHessianTracking
