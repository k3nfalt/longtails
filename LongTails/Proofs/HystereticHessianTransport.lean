import LongTails.Proofs.HystereticHessianBlocks
import LongTails.Proofs.AffineTransportConcentration
import LongTails.Proofs.GuardedHessianNoise
import LongTails.Proofs.HystereticHessianMeasurable

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianTransport

lemma local_segment_raw_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : E → E} {L0 L1 q σ α M η K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M) (hη : 0 ≤ η)
    (hK : L0 + L1 * M + σ + α * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (H : (E × E) → Ω → E) (hHm : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (H (y, v)) P)
    (hm : ∀ y v, (∫ ω, H (y, v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q) P)
    (hb : ∀ y v, (∫ ω, ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q ∂P) ≤
      (σ ^ q + α ^ q * ‖g y‖ ^ q) * ‖v‖ ^ q)
    (x v : E) (hx : ‖g x‖ ≤ M) (hv : ‖v‖ ≤ η)
    (hsmall : L1 * η ≤ 1 / 4) (hbase : L0 * η ≤ M / 4) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let F := fun w : ℝ × Ω => H (x + w.1 • v, v) w.2
    Integrable F Q ∧ (∫ w, F w ∂Q) = g (x + v) - g x ∧
      Integrable (fun w => ‖F w‖ ^ q) Q ∧
      (∫ w, ‖F w‖ ^ q ∂Q) ≤ (512 * K * η) ^ q := by
  intro Q F
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  have : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  have ht := GuardedHessianNoise.affine_random_segment_transport hL0 hL1 hq hq2
    hσ hα hM hη hK hg hD hH H hHm hi hm hpi hb x v hv hsmall hbase
  have hmax : max (‖g x‖ / M) 1 = 1 := max_eq_right ((div_le_one hM).mpr hx)
  have hcentral : (∫ w, ‖F w - (g (x + v) - g x)‖ ^ q ∂Q) ≤ 64 * (K * η) ^ q := by
    simpa only [hmax, Real.one_rpow, mul_one] using ht.2.2.2
  have hcenter : Integrable (fun w => ‖F w - ∫ z, F z ∂Q‖ ^ q) Q := by
    rw [ht.2.1]
    exact ht.2.2.1
  have hr := AffineTransportConcentration.raw_moment_from_centered ht.1 hq hq2 hcenter
  have hK0 : 0 ≤ K := by nlinarith [mul_nonneg hL1 hM.le, mul_nonneg hα hM.le]
  have hcurv : L0 + L1 * ‖g x‖ ≤ K := by
    nlinarith [mul_le_mul_of_nonneg_left hx hL1, mul_nonneg hα hM.le]
  have hd : ‖g (x + v) - g x‖ ≤ 2 * (K * η) := by
    have h := GuardedGeneralizedGeometry.short_gradient_difference hL0 hL1 hg hH x (x + v)
      (by simpa only [add_sub_cancel_left] using (mul_le_mul_of_nonneg_left hv hL1).trans hsmall)
    simp only [add_sub_cancel_left] at h
    have hc0 : 0 ≤ L0 + L1 * ‖g x‖ := by positivity
    nlinarith [mul_le_mul hcurv hv (norm_nonneg v) hK0]
  have h2q : (2 : ℝ) ^ q ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq2
    norm_num at h ⊢
    exact h
  have hmean : ‖∫ z, F z ∂Q‖ ^ q ≤ 4 * (K * η) ^ q := by
    rw [ht.2.1]
    calc
      _ ≤ (2 * (K * η)) ^ q := Real.rpow_le_rpow (norm_nonneg _) hd (by linarith)
      _ = (2 : ℝ) ^ q * (K * η) ^ q := Real.mul_rpow (by norm_num) (mul_nonneg hK0 hη)
      _ ≤ _ := mul_le_mul_of_nonneg_right h2q (Real.rpow_nonneg (mul_nonneg hK0 hη) _)
  have h512 : (512 : ℝ) ≤ (512 : ℝ) ^ q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 512) hq
  refine ⟨ht.1, ht.2.1, hr.1, ?_⟩
  have hraw : (∫ w, ‖F w‖ ^ q ∂Q) ≤ ‖g (x + v) - g x‖ ^ q +
      6 * ∫ w, ‖F w - (g (x + v) - g x)‖ ^ q ∂Q := by
    simpa only [ht.2.1] using hr.2
  rw [ht.2.1] at hmean
  calc
    _ ≤ 388 * (K * η) ^ q := by linarith [hraw]
    _ ≤ (512 : ℝ) ^ q * (K * η) ^ q :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (mul_nonneg hK0 hη) _)
    _ = _ := by rw [mul_assoc, Real.mul_rpow (by norm_num) (mul_nonneg hK0 hη)]

lemma local_segment_clipping {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : E → E} {L0 L1 q σ α M η K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M) (hη : 0 ≤ η)
    (hK : L0 + L1 * M + σ + α * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (H : (E × E) → Ω → E) (hHm : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (H (y, v)) P)
    (hm : ∀ y v, (∫ ω, H (y, v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q) P)
    (hb : ∀ y v, (∫ ω, ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q ∂P) ≤
      (σ ^ q + α ^ q * ‖g y‖ ^ q) * ‖v‖ ^ q)
    (x v : E) (hx : ‖g x‖ ≤ M) (hv : ‖v‖ ≤ η)
    (hsmall : L1 * η ≤ 1 / 4) (hbase : L0 * η ≤ M / 4) {C : ℝ} (hC : 0 < C) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let F := fun w : ℝ × Ω => H (x + w.1 • v, v) w.2
    let μ := ∫ w, OracleTemplate.clip C (F w) ∂Q
    let Y := fun w => OracleTemplate.clip C (F w) - μ
    ‖μ - (g (x + v) - g x)‖ ≤ (512 * K * η) ^ q / (C / 2) ^ (q - 1) ∧
      Measurable Y ∧ Integrable Y Q ∧ Integrable (fun w => ‖Y w‖ ^ 2) Q ∧
      (∫ w, Y w ∂Q) = 0 ∧ (∀ w, ‖Y w‖ ≤ 2 * C) ∧
      (∫ w, ‖Y w‖ ^ 2 ∂Q) ≤ (2 * C) ^ (2 - q) * (512 * K * η) ^ q := by
  intro Q F μ Y
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  have : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  have hr := local_segment_raw_moment hL0 hL1 hq hq2 hσ hα hM hη hK hg hD hH
    H hHm hi hm hpi hb x v hx hv hsmall hbase
  have hF : Measurable F :=
    hHm.comp (((measurable_const.add (measurable_fst.smul_const v)).prodMk
      measurable_const).prodMk measurable_snd)
  have hclip := AffineTransportConcentration.centered_clipping_moments hF
    (by linarith : 0 ≤ q) hq2 hC.le hr.2.2.1 hr.2.2.2
  refine ⟨?_, ((OracleTemplate.measurable_clip C).comp hF).sub_const μ, hclip⟩
  have h := AffineTransportConcentration.raw_clipping_bias hF hr.1 hq hC hr.2.2.1 hr.2.2.2
  change ‖μ - ∫ w, F w ∂Q‖ ≤ _ at h
  rw [show (∫ w, F w ∂Q) = g (x + v) - g x from hr.2.1] at h
  exact h

lemma centered_average_identity {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (hn : 0 < n) (X : ℕ → E) (μ : E) :
    (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, X k) =
      (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (X k - μ)) + μ := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  exact (sub_add_cancel _ _).symm

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMoments HystereticHessianBlocks

lemma transport_error_recursion (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (g : Space p → Space p) (μ : Space p)
    (ha : s.active = true) (ht : s.slot + (c.transportBatch + 1) < macroCalls c) :
    let t := path p c answer { s with phase := .transport 0 0 } ξ (c.transportBatch + 1)
    t.estimate - g t.point = (s.estimate - g s.point) +
      ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
        (∑ k ∈ Finset.range (c.transportBatch + 1),
          (OracleTemplate.clip c.clipThreshold
            (answer (s.point + (ξ k).1 • s.move, some s.move) (ξ k).2) - μ)) +
      (μ - (g (s.point + s.move) - g s.point)) := by
  dsimp only
  rw [transport_pass p c s answer ξ ha ht]
  dsimp only
  rw [centered_average_identity (c.transportBatch + 1) (by omega) _ μ]
  abel

open HystereticHessianPhases

def transportReserve (c : Config) (inner : ℕ) : ℕ :=
  (c.epoch + 1 - inner) * (c.transportBatch + 1)

def transportQuery (p : Params) (c : Config) (s : State p c) : ℕ :=
  if s.active then match s.phase with
    | .transport _ _ => 1
    | _ => 0
  else 0

def remainingTransport (p : Params) (c : Config) (s : State p c) : ℕ :=
  if s.active then match s.phase with
    | .gradient _ _ _ _ _ => transportReserve c s.inner
    | .transport i _ => c.transportBatch + 1 - i + (c.epoch - s.inner) * (c.transportBatch + 1)
    | .padding => 0
  else 0

lemma transportReserve_expand (c : Config) {inner : ℕ} (hi : inner ≤ c.epoch) :
    transportReserve c inner = c.transportBatch + 1 +
      (c.epoch - inner) * (c.transportBatch + 1) := by
  have he : c.epoch + 1 - inner = c.epoch - inner + 1 := by omega
  simp only [transportReserve, he, Nat.add_mul, one_mul]
  omega

lemma transportReserve_succ (c : Config) (inner : ℕ) :
    transportReserve c (inner + 1) = (c.epoch - inner) * (c.transportBatch + 1) := by
  simp [transportReserve]

lemma beginFineStep_transport_le (p : Params) (c : Config) (s : State p c)
    (hi : s.inner ≤ c.epoch) :
    remainingTransport p c (beginFineStep p c s) ≤ transportReserve c s.inner := by
  unfold beginFineStep
  split_ifs
  · simp [remainingTransport]
  · cases s.active <;> simp [remainingTransport, transportReserve_expand c hi]

lemma finishPilot_transport_le (p : Params) (c : Config) (s : State p c) (v : Space p)
    (hi : s.inner ≤ c.epoch) :
    remainingTransport p c (finishPilot p c s v) ≤ transportReserve c s.inner := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_transport_le p c s hi
    | cases s.active <;> simp [remainingTransport]

lemma raw_transport_decreases (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (reply : Space p) :
    remainingTransport p c (rawUpdate p c s reply) + transportQuery p c s ≤
      remainingTransport p c s := by
  cases ha : s.active with
  | false => simp [rawUpdate, transportQuery, remainingTransport, ha]
  | true =>
    cases he : s.phase with
    | padding => simp [rawUpdate, transportQuery, remainingTransport, ha, he]
    | transport i sum =>
      have hv : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hs.2
      simp only [rawUpdate, ha, he, ite_true]
      by_cases hi : i < c.transportBatch
      · rw [ite_eq_left hi]
        simp only [remainingTransport, transportQuery, ha, he, ite_true]
        omega
      · rw [ite_eq_right hi]
        by_cases hn : s.inner < c.epoch
        · rw [ite_eq_left hn]
          simp only [remainingTransport, transportQuery, ha, he, ite_true, transportReserve_succ]
          omega
        · rw [ite_eq_right hn]
          simp only [remainingTransport, transportQuery, ha, he, ite_true]
          omega
    | gradient refresh j i sum values =>
      have hv : s.inner ≤ c.epoch ∧ i ≤ if refresh then c.resetBatch else c.pilotBatch := by
        simpa [he] using hs.2
      have hr : remainingTransport p c s = transportReserve c s.inner := by
        simp [remainingTransport, ha, he]
      simp only [rawUpdate, transportQuery, ha, he, ite_true, Nat.add_zero]
      rw [hr]
      split_ifs
      all_goals first
        | exact beginFineStep_transport_le p c _ hv.1
        | exact finishPilot_transport_le p c s _ hv.1
        | simp [remainingTransport]

lemma update_transport_decreases (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (u : ℝ) (reply : Space p)
    (hclock : s.slot + 1 < macroCalls c) :
    remainingTransport p c (update p c s u reply) + transportQuery p c s ≤
      remainingTransport p c s := by
  simp only [update, hclock, ite_true]
  exact raw_transport_decreases p c s hs reply

lemma transport_query_before_reset (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (hclock : ¬s.slot + 1 < macroCalls c) : transportQuery p c s = 0 := by
  cases ha : s.active with
  | false => simp [transportQuery, ha]
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he]
    | padding => simp [transportQuery, ha, he]
    | transport i sum =>
      have hv : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hc.2
      have hw : 0 < remainingWork p c s := by
        simp only [remainingWork, ha, he, ite_true]
        omega
      exact (hclock (work_prevents_reset p c s hf hw)).elim

lemma remainingTransport_le (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) :
    remainingTransport p c s ≤ (c.epoch + 1) * (c.transportBatch + 1) := by
  have hr : transportReserve c s.inner ≤ (c.epoch + 1) * (c.transportBatch + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  cases ha : s.active with
  | false => simp [remainingTransport, ha]
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simpa [remainingTransport, ha, he] using hr
    | padding => simp [remainingTransport, ha, he]
    | transport i sum =>
      have hv : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hc.2
      rw [transportReserve_expand c hv.1] at hr
      simp only [remainingTransport, ha, he, ite_true]
      omega

lemma path_transport_prefix (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (n : ℕ) (hn : s.slot + n < macroCalls c) :
    (∑ k ∈ Finset.range n, transportQuery p c (path p c answer s ξ k)) +
      remainingTransport p c (path p c answer s ξ n) ≤ remainingTransport p c s := by
  induction n with
  | zero => simp [path, HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    have hprev := ih (by omega)
    have hv := path_invariants p c answer s ξ n hc hf
    have hslot : (path p c answer s ξ n).slot = s.slot + n := by
      rw [path_slot_from p c answer s ξ n hf.1, Nat.mod_eq_of_lt (by omega)]
    have hdec := update_transport_decreases p c (path p c answer s ξ n) hv.1 (ξ n).1
      (answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2) (by rw [hslot]; omega)
    have hnext : remainingTransport p c (path p c answer s ξ (n + 1)) +
        transportQuery p c (path p c answer s ξ n) ≤
          remainingTransport p c (path p c answer s ξ n) := by
      simpa only [path, HeavyTailedProductProcess.trajectory_succ_last] using hdec
    rw [Finset.sum_range_succ]
    omega

lemma macro_transport_count (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s) :
    (∑ k ∈ Finset.range (macroCalls c - s.slot),
      transportQuery p c (path p c answer s ξ k)) ≤
        (c.epoch + 1) * (c.transportBatch + 1) := by
  let n := macroCalls c - s.slot - 1
  have hn : s.slot + n < macroCalls c := by dsimp [n]; have := hf.1; omega
  have hlen : macroCalls c - s.slot = n + 1 := by dsimp [n]; have := hf.1; omega
  have hp := path_transport_prefix p c answer s ξ hc hf n hn
  have hv := path_invariants p c answer s ξ n hc hf
  have hslot : (path p c answer s ξ n).slot = s.slot + n := by
    rw [path_slot_from p c answer s ξ n hf.1, Nat.mod_eq_of_lt hn]
  have hz := transport_query_before_reset p c (path p c answer s ξ n) hv.1 hv.2
    (by rw [hslot]; dsimp [n]; have := hf.1; omega)
  rw [hlen, Finset.sum_range_succ, hz, Nat.add_zero]
  have hr := remainingTransport_le p c s hc
  omega

lemma transportQuery_eq_query (p : Params) (c : Config) (s : State p c) (u : ℝ) :
    transportQuery p c s = if (query p c s u).2.isSome then 1 else 0 := by
  cases ha : s.active <;> cases hp : s.phase <;> simp [transportQuery, query, ha, hp]

open HystereticHessianMeasurable

lemma measurable_transportQuery (p : Params) (c : Config) : Measurable (transportQuery p c) := by
  let F := fun (ph : Phase p c) (s : State p c) => transportQuery p c { s with phase := ph }
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, transportQuery, ite_self]
      exact measurable_const
    · simp only [F, transportQuery]
      exact Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd) measurable_const) measurable_const measurable_const
    · simp only [F, transportQuery, ite_self]
      exact measurable_const
  have hh := hm.comp ((measurable_phase p c).prodMk measurable_id)
  convert hh using 1
  funext s
  cases s
  rfl

noncomputable def historyState (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (n : ℕ) (h : Fin n → ℝ × Ω) : State p c :=
  finiteRun (fun s z => update p c s z.1 (answer (query p c s z.1) z.2)) n s h

lemma historyState_eq_path (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    historyState p c answer s n (fun i => ξ i) = path p c answer s ξ n :=
  finiteRun_eq_trajectory _ n s ξ

lemma measurable_advance (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) :
    Measurable (Function.uncurry (fun (s : State p c) (z : ℝ × Ω) =>
      update p c s z.1 (answer (query p c s z.1) z.2))) := by
  have hreply : Measurable (fun w : State p c × (ℝ × Ω) =>
      answer (query p c w.1 w.2.1) w.2.2) :=
    ha.comp (((measurable_query p c).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  exact (measurable_update p c).comp (measurable_fst.prodMk hreply)

lemma measurable_historyState (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (s : State p c) (n : ℕ) :
    Measurable (historyState p c answer s n) :=
  (finiteRun_measurable _ (measurable_advance p c answer ha) n).comp
    (measurable_const.prodMk measurable_id)

lemma macro_masked_transport_count (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    (A : (n : ℕ) → (Fin n → ℝ × Ω) → Bool)
    (hA : ∀ k h, A k h = true → transportQuery p c (historyState p c answer s k h) = 1) :
    AffineTransportConcentration.historyActiveCount A (macroCalls c - s.slot) (fun i => ξ i) ≤
      (c.epoch + 1) * (c.transportBatch + 1) := by
  rw [AffineTransportConcentration.historyActiveCount_eq]
  apply le_trans _ (macro_transport_count p c answer s ξ hc hf)
  apply Finset.sum_le_sum
  intro k _
  by_cases ha : A k (fun i => ξ i) = true
  · have hh := hA k (fun i => ξ i) ha
    rw [historyState_eq_path] at hh
    simp only [ha, ite_true, hh, le_refl]
  · simp [ha]

def LocalTransport (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) : Prop :=
  s.active = true → match s.phase with
    | .gradient true _ _ _ _ => ‖g s.point‖ ≤ 4 * c.radius
    | .transport _ _ => ‖g s.point‖ ≤ 4 * c.radius
    | _ => True

def PilotReplyAccurate (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (reply : Space p) : Prop :=
  s.active = true → ∀ j i sum values, s.phase = .gradient false j i sum values →
    c.pilotBatch ≤ i → c.groups ≤ j.val →
      ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (Function.update values j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply))) - g s.point‖ ≤
          (c.radius + ‖g s.point‖) / 256

lemma beginFineStep_local (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (hs : ‖g s.point‖ ≤ 4 * c.radius) : LocalTransport p c g (beginFineStep p c s) := by
  unfold beginFineStep
  split_ifs <;> simp [LocalTransport, hs]

lemma finishPilot_local (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (v : Space p) (hU : 0 ≤ c.radius)
    (hv : ‖v - g s.point‖ ≤ (c.radius + ‖g s.point‖) / 256) :
    LocalTransport p c g (finishPilot p c s v) := by
  have hbound (hstay : ‖v‖ < 3 * c.radius) : ‖g s.point‖ ≤ 4 * c.radius := by
    have hn := norm_le_norm_sub_add (g s.point) v
    rw [norm_sub_rev] at hn
    linarith
  unfold finishPilot
  by_cases hguard : c.guardThreshold < ‖v‖
  · simp [hguard, LocalTransport]
  · rw [ite_eq_right hguard]
    by_cases hf : s.fine = true
    · rw [ite_eq_left hf]
      by_cases he : 3 * c.radius ≤ ‖v‖
      · simp [he, LocalTransport]
      · rw [ite_eq_right he]
        have hb := hbound (lt_of_not_ge he)
        by_cases hi : s.inner = 0
        · simp [hi, LocalTransport, hb]
        · rw [ite_eq_right hi]
          exact beginFineStep_local p c g s hb
    · rw [ite_eq_right hf]
      split_ifs <;> simp [LocalTransport]

lemma raw_local_transport (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (hU : 0 ≤ c.radius) (hs : LocalTransport p c g s) (reply : Space p)
    (hp : PilotReplyAccurate p c g s reply) : LocalTransport p c g (rawUpdate p c s reply) := by
  cases ha : s.active with
  | false => simpa [rawUpdate, ha] using hs
  | true =>
    cases he : s.phase with
    | padding => simpa [rawUpdate, ha, he] using hs
    | transport i sum =>
      have hb : ‖g s.point‖ ≤ 4 * c.radius := by simpa [LocalTransport, ha, he] using hs
      simp only [rawUpdate, ha, he, ite_true]
      split_ifs <;> simp [LocalTransport, hb]
    | gradient refresh j i sum values =>
      cases refresh with
      | true =>
        have hb : ‖g s.point‖ ≤ 4 * c.radius := by simpa [LocalTransport, ha, he] using hs
        simp only [rawUpdate, ha, he, ite_true]
        split_ifs
        all_goals first
          | exact beginFineStep_local p c g _ hb
          | simp [LocalTransport, hb]
      | false =>
        simp only [rawUpdate, ha, he, ite_true, Bool.false_eq_true, ite_false]
        by_cases hi : i < c.pilotBatch
        · simp [hi, LocalTransport]
        · rw [ite_eq_right hi]
          by_cases hj : j.val + 1 < c.groups + 1
          · simp [hj, LocalTransport]
          · rw [dite_eq_right hj]
            exact finishPilot_local p c g s _ hU (hp ha j i sum values he (by omega) (by omega))

lemma update_local_transport (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (hU : 0 ≤ c.radius) (hs : LocalTransport p c g s) (u : ℝ) (reply : Space p)
    (hp : PilotReplyAccurate p c g s reply) : LocalTransport p c g (update p c s u reply) := by
  unfold update
  split_ifs
  · exact raw_local_transport p c g s hU hs reply hp
  · simp [LocalTransport]

lemma path_local_transport (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hU : 0 ≤ c.radius) (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (hp : ∀ k < n, PilotReplyAccurate p c g (path p c answer (initial p c) ξ k)
      (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2)) :
    LocalTransport p c g (path p c answer (initial p c) ξ n) := by
  induction n with
  | zero => simp [path, HeavyTailedProductProcess.trajectory, initial, LocalTransport]
  | succ n ih =>
    have hh := update_local_transport p c g (path p c answer (initial p c) ξ n) hU
      (ih (fun k hk => hp k (by omega))) (ξ n).1 _ (hp n (by omega))
    simpa only [path, HeavyTailedProductProcess.trajectory_succ_last] using hh

noncomputable def localMask (p : Params) (c : Config) (g : Space p → Space p) (s : State p c) : Bool :=
  if transportQuery p c s = 1 ∧ ‖g s.point‖ ≤ 4 * c.radius ∧ ‖s.move‖ ≤ c.fineStep then true else false

lemma measurable_localMask (p : Params) (c : Config) (g : Space p → Space p) (hg : Measurable g) :
    Measurable (localMask p c g) := by
  unfold localMask
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_eq_fun (measurable_transportQuery p c) measurable_const).inter
    ((measurableSet_le (hg.comp (measurable_point p c)).norm measurable_const).inter
      (measurableSet_le (measurable_move p c).norm measurable_const))

lemma localMask_transport (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (h : localMask p c g s = true) : transportQuery p c s = 1 := by
  unfold localMask at h
  split_ifs at h with hh
  · exact hh.1

lemma localMask_of_local (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (hl : LocalTransport p c g s) (hm : MoveValid p c s) (hstep : 0 ≤ c.fineStep)
    (ht : transportQuery p c s = 1) : localMask p c g s = true := by
  cases ha : s.active with
  | false => simp [transportQuery, ha] at ht
  | true =>
    cases he : s.phase with
    | gradient refresh j i sum values => simp [transportQuery, ha, he] at ht
    | padding => simp [transportQuery, ha, he] at ht
    | transport i sum =>
      have hp : ‖g s.point‖ ≤ 4 * c.radius := by simpa [LocalTransport, ha, he] using hl
      have hv : s.move = fineDisplacement p c s := by simpa [MoveValid, he] using hm
      have hb : ‖s.move‖ ≤ c.fineStep := by rw [hv]; exact fine_displacement_bound p c s hstep
      simp [localMask, ht, hp, hb]

lemma path_move_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (hs : MoveValid p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    MoveValid p c (path p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact hs
  | succ n ih =>
    exact ih _ (update_move_valid p c s hs (ξ 0).1 _) _

lemma path_localMask_active (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hU : 0 ≤ c.radius) (hstep : 0 ≤ c.fineStep)
    (ξ : ℕ → ℝ × Ω) (n : ℕ)
    (hp : ∀ k < n, PilotReplyAccurate p c g (path p c answer (initial p c) ξ k)
      (answer (query p c (path p c answer (initial p c) ξ k) (ξ k).1) (ξ k).2))
    (ht : transportQuery p c (path p c answer (initial p c) ξ n) = 1) :
    localMask p c g (path p c answer (initial p c) ξ n) = true :=
  localMask_of_local p c g _ (path_local_transport p c answer g hU ξ n hp)
    (path_move_valid p c answer (initial p c) (by trivial) ξ n) hstep ht

noncomputable def transportNoise (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (z : ℝ × Ω) : Space p :=
  if localMask p c g s then ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ •
    (OracleTemplate.clip c.clipThreshold (answer (query p c s z.1) z.2) -
      ∫ w, OracleTemplate.clip c.clipThreshold (answer (query p c s w.1) w.2) ∂Q)
  else 0

lemma measurable_transportNoise (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [SFinite Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g) :
    Measurable (Function.uncurry (transportNoise p c Q answer g)) := by
  have hreply : Measurable (fun w : State p c × (ℝ × Ω) =>
      OracleTemplate.clip c.clipThreshold (answer (query p c w.1 w.2.1) w.2.2)) :=
    (OracleTemplate.measurable_clip c.clipThreshold).comp
      (ha.comp (((measurable_query p c).comp
        (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  have hmean : Measurable (fun s : State p c =>
      ∫ w, OracleTemplate.clip c.clipThreshold (answer (query p c s w.1) w.2) ∂Q) :=
    hreply.stronglyMeasurable.integral_prod_right.measurable
  exact ((hreply.sub (hmean.comp measurable_fst)).const_smul
      (((c.transportBatch + 1 : ℕ) : ℝ)⁻¹)).ite
    (measurableSet_eq_fun ((measurable_localMask p c g hg).comp measurable_fst) measurable_const)
    measurable_const

lemma transportNoise_inactive (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (h : localMask p c g s = false) (z : ℝ × Ω) :
    transportNoise p c Q answer g s z = 0 := by
  simp [transportNoise, h]

lemma localMask_bounds (p : Params) (c : Config) (g : Space p → Space p) (s : State p c)
    (h : localMask p c g s = true) :
    transportQuery p c s = 1 ∧ ‖g s.point‖ ≤ 4 * c.radius ∧ ‖s.move‖ ≤ c.fineStep := by
  unfold localMask at h
  split_ifs at h with hh
  exact hh

lemma query_of_transport (p : Params) (c : Config) (s : State p c)
    (ht : transportQuery p c s = 1) (u : ℝ) :
    query p c s u = (s.point + u • s.move, some s.move) := by
  cases ha : s.active <;> cases he : s.phase <;> simp_all [transportQuery, query]

lemma transportNoise_moments (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
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
    let Y := transportNoise p c Q answer g s
    Integrable Y Q ∧ Integrable (fun z => ‖Y z‖ ^ 2) Q ∧
      (∫ z, Y z ∂Q) = 0 ∧
      (∀ z, ‖Y z‖ ≤ 2 * c.clipThreshold / ((c.transportBatch + 1 : ℕ) : ℝ)) ∧
      (∫ z, ‖Y z‖ ^ 2 ∂Q) ≤
        (2 * c.clipThreshold) ^ (2 - p.q) * (512 * K * c.fineStep) ^ p.q /
          ((c.transportBatch + 1 : ℕ) : ℝ) ^ 2 := by
  intro Q Y
  have hK0 : 0 ≤ K := by
    nlinarith [mul_nonneg hL1 (by positivity : 0 ≤ 4 * c.radius),
      mul_nonneg hα (by positivity : 0 ≤ 4 * c.radius)]
  by_cases hmask : localMask p c g s = true
  · have hs := localMask_bounds p c g s hmask
    let H := fun (yv : Space p × Space p) (ω : Ω) => answer (yv.1, some yv.2) ω
    have hHm : Measurable (Function.uncurry H) :=
      ha.comp ((measurable_fst.fst.prodMk (measurable_some.comp measurable_fst.snd)).prodMk
        measurable_snd)
    have hc := local_segment_clipping hL0 hL1 hq hq2 hσ hα
      (by positivity : 0 < 4 * c.radius) hη hK hg hD hH H hHm hi hm hpi hb
      s.point s.move hs.2.1 hs.2.2 hsmall (by nlinarith [hbase]) hτ
    let Z := fun z : ℝ × Ω =>
      OracleTemplate.clip c.clipThreshold (answer (s.point + z.1 • s.move, some s.move) z.2) -
        ∫ w, OracleTemplate.clip c.clipThreshold (answer (s.point + w.1 • s.move, some s.move) w.2) ∂Q
    have hc' : Integrable Z Q ∧ Integrable (fun z => ‖Z z‖ ^ 2) Q ∧
        (∫ z, Z z ∂Q) = 0 ∧ (∀ z, ‖Z z‖ ≤ 2 * c.clipThreshold) ∧
        (∫ z, ‖Z z‖ ^ 2 ∂Q) ≤
          (2 * c.clipThreshold) ^ (2 - p.q) * (512 * K * c.fineStep) ^ p.q := hc.2.2
    have hscaled := AffineTransportConcentration.scaled_centered_moments
      (by positivity : (0 : ℝ) < ((c.transportBatch + 1 : ℕ) : ℝ))
      hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2.1 hc'.2.2.2.2
    have heq : Y = fun z => ((c.transportBatch + 1 : ℕ) : ℝ)⁻¹ • Z z := by
      funext z
      simp only [Y, transportNoise, hmask, ite_true, query_of_transport p c s hs.1, Z]
    rw [heq]
    exact hscaled
  · have hf : localMask p c g s = false := Bool.eq_false_iff.mpr hmask
    have heq : Y = fun _ => 0 := by
      funext z
      exact transportNoise_inactive p c Q answer g s hf z
    rw [heq]
    refine ⟨integrable_const _, ?_, ?_, ?_, ?_⟩
    · simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact integrable_const _
    · simp
    · intro z
      simp only [norm_zero]
      positivity
    · simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero]
      positivity

end LongTails.Proofs.HystereticHessianTransport
