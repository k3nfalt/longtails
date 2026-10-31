import LongTails.Proofs.HeavyTailedSospDetectionIntegration
import LongTails.Proofs.MixedNoiseSelectors
import LongTails.Proofs.HeavyTailedSospForecastIntegration

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSospOutput

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedProductProcess HeavyTailedSospExecution HeavyTailedSospReset

lemma completeTransport_phase_irrelevant (p : Params) (c : Config) (s : State p)
    (ph : Phase p) (v z : Space p) (after : Resume p) :
    completeTransport p c {s with phase := ph} v z after = completeTransport p c s v z after := by
  unfold completeTransport
  dsimp only
  split
  · rfl
  · exact resume_phase_irrelevant p c
      {s with point := s.point + v, estimate := s.estimate + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • z, virtualIndex := s.virtualIndex + 1} ph after

lemma transport_prefix (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (v : Space p) (after : Resume p) (ξ : ℕ → Aux p c × p.Ω)
    (n : ℕ) (hn : n < max 1 c.transportBatch) :
    trajectory (sampleStep p c g H) n {s with phase := .transport v 0 0 after} ξ =
      {s with phase := .transport v n (∑ k ∈ Finset.range n, H (s.point + (ξ k).1.1 • v) (ξ k).2 v) after} := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory_succ_last, ih (by omega)]
    simp [sampleStep, query, update, transportReply, hn, Finset.sum_range_succ]

lemma transport_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (v : Space p) (after : Resume p) (ξ : ℕ → Aux p c × p.Ω) :
    trajectory (sampleStep p c g H) (max 1 c.transportBatch)
      {s with phase := .transport v 0 0 after} ξ =
      completeTransport p c s v
        (∑ k ∈ Finset.range (max 1 c.transportBatch), H (s.point + (ξ k).1.1 • v) (ξ k).2 v) after := by
  have hb : max 1 c.transportBatch - 1 + 1 = max 1 c.transportBatch := by omega
  conv_lhs => rw [← hb, trajectory_succ_last]
  rw [transport_prefix p c g H s v after ξ _ (by omega)]
  simp only [sampleStep, query, update, transportReply, hb, lt_self_iff_false, ↓reduceIte]
  rw [completeTransport_phase_irrelevant]
  congr 1
  rw [← Finset.sum_range_succ, hb]

lemma transport_detect_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (v : Space p) (ξ : ℕ → Aux p c × p.Ω) :
    let K := max 1 c.transportBatch +
      if (s.virtualIndex + 1) % max 1 c.epoch = 0 then max 1 c.resetBatch else 0
    let sn := trajectory (sampleStep p c g H) K {s with phase := .transport v 0 0 .detect} ξ
    sn.phase = .probeInit 0 none ∧ sn.point = s.point + v ∧ sn.cycleIndex = s.cycleIndex := by
  intro K sn
  by_cases hr : (s.virtualIndex + 1) % max 1 c.epoch = 0
  · dsimp only [sn, K]
    rw [ite_eq_left hr, HeavyTailedSospEpochIntegration.trajectory_add, transport_complete]
    simp only [completeTransport, hr, ↓reduceIte]
    rw [reset_complete p c g H
      {s with point := s.point + v, estimate := s.estimate + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • (∑ k ∈ Finset.range (max 1 c.transportBatch), H (s.point + (ξ k).1.1 • v) (ξ k).2 v), virtualIndex := s.virtualIndex + 1}
      .detect]
    simp [resume]
  · dsimp only [sn, K]
    rw [ite_eq_right hr, Nat.add_zero, transport_complete]
    simp [completeTransport, hr, resume]

lemma marked_transport (p : Params) (s : State p)
    (hm : HeavyTailedSospInvariants.markCharge p s.phase = 1)
    (hz : HeavyTailedSospEstimator.ZeroPartial p s.phase) :
    ∃ v, s.phase = .transport v 0 0 .detect := by
  cases hp : s.phase <;> simp only [hp, HeavyTailedSospInvariants.markCharge] at hm
  case transport v i z r =>
    cases r <;> dsimp only at hm
    case detect =>
      have hi : i = 0 := by split_ifs at hm; omega
      subst i
      have hz' : z = 0 := by simpa only [hp, HeavyTailedSospEstimator.ZeroPartial, true_implies] using hz
      subst z
      exact ⟨v, rfl⟩
    all_goals contradiction
  all_goals contradiction

lemma marked_detector_pair (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω)
    (hm : HeavyTailedSospInvariants.markCharge p s.phase = 1)
    (hz : HeavyTailedSospEstimator.ZeroPartial p s.phase)
    (hb : HeavyTailedSospGeometry.PhaseBound p c.h s.phase) :
    let K := max 1 c.transportBatch +
      if (s.virtualIndex + 1) % max 1 c.epoch = 0 then max 1 c.resetBatch else 0
    let sn := trajectory (sampleStep p c g H) K s ξ
    sn.phase = .probeInit 0 none ∧ ‖sn.point - s.point‖ ≤ c.h ∧ sn.cycleIndex = s.cycleIndex := by
  intro K sn
  obtain ⟨v, hv⟩ := marked_transport p s hm hz
  have hs : {s with phase := .transport v 0 0 .detect} = s := by rw [← hv]
  have hc := transport_detect_complete p c g H s v ξ
  dsimp only at hc
  rw [hs] at hc
  refine ⟨hc.1, ?_, hc.2.2⟩
  have hvnorm : ‖v‖ ≤ c.h := by simpa [hv, HeavyTailedSospGeometry.PhaseBound, HeavyTailedSospGeometry.ResumeBound] using hb
  change ‖(trajectory (sampleStep p c g H) K s ξ).point - s.point‖ ≤ c.h
  rw [hc.2.1, add_sub_cancel_left]
  exact hvnorm

lemma trajectory_marked_detector_pair (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target k N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
    ∃ j, k < j ∧ j < N ∧ (X j).phase = .probeInit 0 none ∧
      ‖(X j).point - (X k).point‖ ≤ c.h ∧ (X j).cycleIndex = (X k).cycleIndex := by
  intro X
  let K := max 1 c.transportBatch +
    if ((X k).virtualIndex + 1) % max 1 c.epoch = 0 then max 1 c.resetBatch else 0
  have hK : 0 < K := by dsimp only [K]; omega
  have hz := HeavyTailedSospEstimator.trajectory_zeroPartial p c g H (initial p target)
    (by simp [initial, HeavyTailedSospEstimator.ZeroPartial]) k ξ
  have hb := HeavyTailedSospGeometry.trajectory_bound p c g H hd hh hs hseg (initial p target)
    (HeavyTailedSospGeometry.initial_bound p c target) k ξ
  have hp := marked_detector_pair p c g H (X k) (fun i => ξ (k + i)) hm hz hb
  change (trajectory (sampleStep p c g H) K (X k) (fun i => ξ (k + i))).phase = _ ∧ _ at hp
  have he : X (k + K) = trajectory (sampleStep p c g H) K (X k) (fun i => ξ (k + i)) :=
    HeavyTailedSospEpochIntegration.trajectory_add _ _ _ _ _
  rw [← he] at hp
  have hjN : k + K < N := by
    by_contra hn
    have hNk : N ≤ k + K := by omega
    have ha := completion_absorbing p c g H (initial p target) ξ N (k + K - N) hdone
    rw [Nat.add_sub_of_le hNk] at ha
    have hdj : (X (k + K)).phase = .done := by
      change (trajectory (sampleStep p c g H) (k + K) (initial p target) ξ).phase = .done
      rw [ha]
      exact hdone
    have hf := hp.1
    rw [hdj] at hf
    contradiction
  exact ⟨k + K, by omega, hjN, hp⟩

lemma strictBadCurvature_transfer (p : Params) (A : Space p → Space p →L[ℝ] Space p)
    {ρ h γ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (hρh : ρ * h ≤ γ) (x y : Space p) (hd : ‖y - x‖ ≤ h)
    (hx : x ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-5 * γ)) :
    y ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-4 * γ) := by
  obtain ⟨v, hv, hbad⟩ := hx
  refine ⟨v, hv, ?_⟩
  have hb := ((A y - A x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hLip y x) (norm_nonneg v))
  have hi := real_inner_le_norm v ((A y - A x) v)
  simp only [hv, one_mul, mul_one, sub_apply, inner_sub_right] at hb hi
  have hh := mul_le_mul_of_nonneg_left hd hρ
  linarith

lemma marked_cycleIndex (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target k : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1) :
    (trajectory (sampleStep p c g H) k (initial p target) ξ).cycleIndex =
      ∑ n ∈ Finset.range k, HeavyTailedSospInvariants.markCharge p
        (trajectory (sampleStep p c g H) n (initial p target) ξ).phase := by
  have hz := HeavyTailedSospEstimator.trajectory_zeroPartial p c g H (initial p target)
    (by simp [initial, HeavyTailedSospEstimator.ZeroPartial]) k ξ
  obtain ⟨v, hv⟩ := marked_transport p _ hm hz
  have hc := HeavyTailedSospInvariants.trajectory_cycleProgress p c g H (initial p target) k ξ
  unfold HeavyTailedSospInvariants.cycleProgress at hc
  rw [hv] at hc
  simpa only [
    HeavyTailedSospInvariants.phaseCycleFlag, ↓reduceIte, Nat.add_zero,
    initial, HeavyTailedSospInvariants.resumeCycleFlag, Nat.zero_add] using hc

lemma marked_cycleIndex_injective (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target i j : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hi : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) i (initial p target) ξ).phase = 1)
    (hj : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) j (initial p target) ξ).phase = 1)
    (he : (trajectory (sampleStep p c g H) i (initial p target) ξ).cycleIndex =
      (trajectory (sampleStep p c g H) j (initial p target) ξ).cycleIndex) : i = j := by
  apply HeavyTailedSospStopped.marked_ordinal_injective
    (fun n => HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) n (initial p target) ξ).phase) hi hj
  rw [← marked_cycleIndex p c g H target i ξ hi, ← marked_cycleIndex p c g H target j ξ hj, he]

def badMarkEvent (p : Params) (B : Set (Space p)) : Set (State p) :=
  {s | HeavyTailedSospInvariants.markCharge p s.phase = 1 ∧ s.point ∈ B}

lemma badMarkEvent_measurable (p : Params) (B : Set (Space p)) (hB : MeasurableSet B) :
    MeasurableSet (badMarkEvent p B) :=
  (measurableSet_eq_fun ((HeavyTailedSospStopped.measurable_markCharge p).comp
    (HeavyTailedSospMeasurable.measurable_phase p)) measurable_const).inter
      (hB.preimage (HeavyTailedSospMeasurable.measurable_point p))

lemma bad_mark_start_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (A : Space p → Space p →L[ℝ] Space p) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (hρh : ρ * c.h ≤ c.γ)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
    let B5 := HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-5 * c.γ)
    let B4 := HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-4 * c.γ)
    (∑ n ∈ Finset.range N, (badMarkEvent p B5).indicator (fun _ => (1 : ℝ)) (X n)) ≤
      ∑ n ∈ Finset.range N, (HeavyTailedSospDetectionIntegration.badStartEvent p B4).indicator
        (fun _ => (1 : ℝ)) (X n) := by
  classical
  intro X B5 B4
  let F := (Finset.range N).filter (fun n => X n ∈ badMarkEvent p B5)
  let C := fun n => (HeavyTailedSospDetectionIntegration.badStartEvent p B4).indicator (fun _ => (1 : ℝ)) (X n)
  have hpair (n : ℕ) (hn : n ∈ F) : ∃ j, j < N ∧ (X j).cycleIndex = (X n).cycleIndex ∧ C j = 1 := by
    obtain ⟨hm, hx⟩ := (Finset.mem_filter.mp hn).2
    obtain ⟨j, _, hjN, hj, hdist, hcycle⟩ :=
      trajectory_marked_detector_pair p c g H hd hh hs hseg target n N ξ hm hdone
    refine ⟨j, hjN, hcycle, ?_⟩
    have hbad := strictBadCurvature_transfer p A hρ hLip hρh (X n).point (X j).point hdist hx
    have he : X j ∈ HeavyTailedSospDetectionIntegration.badStartEvent p B4 :=
      ⟨by
        change HeavyTailedSospWork.detectorStart p
          (trajectory (sampleStep p c g H) j (initial p target) ξ).phase = 1
        rw [hj]
        rfl, hbad⟩
    exact Set.indicator_of_mem he _
  let J := fun n => if hn : n ∈ F then Classical.choose (hpair n hn) else 0
  have hJ (n : ℕ) (hn : n ∈ F) : J n < N ∧ (X (J n)).cycleIndex = (X n).cycleIndex ∧ C (J n) = 1 := by
    simpa only [J, dite_eq_left hn] using Classical.choose_spec (hpair n hn)
  have hi : ∀ n ∈ F, ∀ m ∈ F, J n = J m → n = m := by
    intro n hn m hm he
    apply marked_cycleIndex_injective p c g H target n m ξ
      (Finset.mem_filter.mp hn).2.1 (Finset.mem_filter.mp hm).2.1
    exact (hJ n hn).2.1.symm.trans ((congrArg (fun j => (X j).cycleIndex) he).trans (hJ m hm).2.1)
  have hb := HeavyTailedSospEpochIntegration.finite_sum_injection_bound F (Finset.range N)
    (fun _ => (1 : ℝ)) C J
    (fun n hn => Finset.mem_range.mpr (hJ n hn).1) hi
    (fun n hn => le_of_eq (hJ n hn).2.2.symm)
    (fun n _ => by simp only [C, Set.indicator_apply]; split_ifs <;> norm_num)
  simpa only [F, Finset.sum_filter, Set.indicator_apply, C] using hb

lemma expected_bad_mark_start_count_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (A : Space p → Space p →L[ℝ] Space p) (hA : Continuous A) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (hρh : ρ * c.h ≤ c.γ)
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun n ξ => trajectory (sampleStep p c g H) n (initial p target) ξ
    let B5 := HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-5 * c.γ)
    let B4 := HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-4 * c.γ)
    Integrable (fun ξ => ∑ n ∈ Finset.range N,
      (badMarkEvent p B5).indicator (fun _ => (1 : ℝ)) (X n ξ)) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, (badMarkEvent p B5).indicator (fun _ => (1 : ℝ)) (X n ξ) ∂P) ≤
      ∫ ξ, ∑ n ∈ Finset.range N, (HeavyTailedSospDetectionIntegration.badStartEvent p B4).indicator
        (fun _ => (1 : ℝ)) (X n ξ) ∂P := by
  intro X B5 B4
  have hX (n : ℕ) : Measurable (X n) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hm (n : ℕ) : Integrable (fun ξ => (badMarkEvent p B5).indicator (fun _ => (1 : ℝ)) (X n ξ)) P :=
    (integrable_const (1 : ℝ)).indicator ((badMarkEvent_measurable p B5
      (HeavyTailedSospDetectionIntegration.strictBadCurvature_isOpen p A hA _).measurableSet).preimage (hX n))
  have hsI (n : ℕ) : Integrable (fun ξ =>
      (HeavyTailedSospDetectionIntegration.badStartEvent p B4).indicator (fun _ => (1 : ℝ)) (X n ξ)) P :=
    (integrable_const (1 : ℝ)).indicator ((HeavyTailedSospDetectionIntegration.badStartEvent_measurable p B4
      (HeavyTailedSospDetectionIntegration.strictBadCurvature_isOpen p A hA _).measurableSet).preimage (hX n))
  have hmI := integrable_finsetSum (Finset.range N) (fun n _ => hm n)
  exact ⟨hmI, integral_mono hmI (integrable_finsetSum (Finset.range N) (fun n _ => hsI n))
    (fun ξ => bad_mark_start_count_bound p c g H A hρ hLip hρh hd hh hs hseg target N ξ (hdone ξ))⟩

def CoreEq (p : Params) (s t : State p) : Prop :=
  s.point = t.point ∧ s.estimate = t.estimate ∧ s.virtualIndex = t.virtualIndex ∧
    s.cycleIndex = t.cycleIndex ∧ s.phase = t.phase

lemma coreEq_initial (p : Params) (j k : ℕ) : CoreEq p (initial p j) (initial p k) := by
  simp [CoreEq, initial]

lemma coreEq_query (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (a : Aux p c) : query p c s a = query p c t a := by
  unfold query
  rw [h.2.2.2.2, h.1]

lemma coreEq_startCycle (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t) :
    CoreEq p (startCycle p c s) (startCycle p c t) := by
  unfold startCycle
  rw [h.2.2.2.1]
  split_ifs <;> simp_all [CoreEq]

lemma coreEq_resume (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (after : Resume p) : CoreEq p (resume p c s after) (resume p c t after) := by
  cases after with
  | startCycle => exact coreEq_startCycle p c h
  | detect => simp_all [resume, CoreEq]
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · apply coreEq_startCycle p c
      simp_all [CoreEq]
    · simp_all [CoreEq]

lemma coreEq_completeTransport (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (v z : Space p) (after : Resume p) :
    CoreEq p (completeTransport p c s v z after) (completeTransport p c t v z after) := by
  unfold completeTransport
  rw [h.2.2.1]
  dsimp only
  split_ifs
  · simp_all [CoreEq]
  · apply coreEq_resume p c
    simp_all [CoreEq]

lemma coreEq_transportReply (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (v : Space p) (n : ℕ) (z r : Space p) (after : Resume p) :
    CoreEq p (transportReply p c s v n z r after) (transportReply p c t v n z r after) := by
  unfold transportReply
  split_ifs
  · simp_all [CoreEq]
  · exact coreEq_completeTransport p c h v (z + r) after

lemma coreEq_probeReply (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (n : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (r : Space p) :
    CoreEq p (probeReply p c s n accepted probe r) (probeReply p c t n accepted probe r) := by
  unfold probeReply
  dsimp only
  split_ifs <;> simp_all [CoreEq]

lemma coreEq_update (p : Params) (c : Config) {s t : State p} (h : CoreEq p s t)
    (a : Aux p c) (r : Space p) : CoreEq p (update p c s a r) (update p c t a r) := by
  unfold update
  rw [h.2.2.2.2]
  cases t.phase with
  | reset n z after =>
    dsimp only
    split_ifs
    · simp_all [CoreEq]
    · apply coreEq_resume p c
      simp_all [CoreEq]
  | transport v n z after => exact coreEq_transportReply p c h v n z r after
  | probeInit n accepted => exact coreEq_probeReply p c h n accepted _ r
  | probe n accepted probe => exact coreEq_probeReply p c h n accepted probe r
  | validate n accepted v values =>
    dsimp only
    split_ifs
    all_goals first
      | solve | simp_all [CoreEq]
      | (split
         · apply coreEq_startCycle p c
           simp_all [CoreEq]
         · simp_all [CoreEq])
  | ncInit v => exact coreEq_transportReply p c h _ 0 0 r _
  | done => exact h

lemma coreEq_sampleStep (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    {s t : State p} (h : CoreEq p s t) (z : Aux p c × p.Ω) :
    CoreEq p (sampleStep p c g H s z) (sampleStep p c g H t z) := by
  unfold sampleStep
  rw [coreEq_query p c h z.1]
  exact coreEq_update p c h z.1 _

lemma coreEq_trajectory (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (j k N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    CoreEq p (trajectory (sampleStep p c g H) N (initial p j) ξ)
      (trajectory (sampleStep p c g H) N (initial p k) ξ) := by
  induction N with
  | zero => exact coreEq_initial p j k
  | succ n ih =>
    rw [trajectory_succ_last, trajectory_succ_last]
    exact coreEq_sampleStep p c g H ih (ξ n)

def OutputWrite (p : Params) (s t : State p) : Prop :=
  t.target = s.target ∧ t.selected =
    if HeavyTailedSospInvariants.markCharge p t.phase = 1 ∧ t.cycleIndex = s.target
    then t.point else s.selected

lemma startCycle_outputWrite (p : Params) (c : Config) (s : State p) :
    OutputWrite p s (startCycle p c s) := by
  unfold startCycle
  split_ifs <;> simp_all [OutputWrite, HeavyTailedSospInvariants.markCharge]

lemma resume_outputWrite (p : Params) (c : Config) (s : State p) (after : Resume p) :
    OutputWrite p s (resume p c s after) := by
  cases after with
  | startCycle => exact startCycle_outputWrite p c s
  | detect => simp [resume, OutputWrite, HeavyTailedSospInvariants.markCharge]
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_outputWrite p c { s with cycleIndex := s.cycleIndex + 1 }
    · simp [OutputWrite, HeavyTailedSospInvariants.markCharge]

lemma completeTransport_outputWrite (p : Params) (c : Config) (s : State p)
    (v z : Space p) (after : Resume p) : OutputWrite p s (completeTransport p c s v z after) := by
  unfold completeTransport
  dsimp only
  split_ifs
  · simp [OutputWrite, HeavyTailedSospInvariants.markCharge]
  · exact resume_outputWrite p c _ after

lemma transportReply_outputWrite (p : Params) (c : Config) (s : State p)
    (v : Space p) (n : ℕ) (z r : Space p) (after : Resume p) :
    OutputWrite p s (transportReply p c s v n z r after) := by
  unfold transportReply
  split_ifs
  · cases after <;> simp [OutputWrite, HeavyTailedSospInvariants.markCharge]
  · exact completeTransport_outputWrite p c s v (z + r) after

lemma probeReply_outputWrite (p : Params) (c : Config) (s : State p)
    (n : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (r : Space p) :
    OutputWrite p s (probeReply p c s n accepted probe r) := by
  unfold probeReply
  dsimp only
  split_ifs <;> simp_all [OutputWrite, HeavyTailedSospInvariants.markCharge]

lemma update_outputWrite (p : Params) (c : Config) (s : State p) (a : Aux p c) (r : Space p) :
    OutputWrite p s (update p c s a r) := by
  cases hp : s.phase with
  | reset n z after =>
    simp only [update, hp]
    split_ifs
    · simp [OutputWrite, HeavyTailedSospInvariants.markCharge]
    · exact resume_outputWrite p c _ after
  | transport v n z after =>
    simp only [update, hp]
    exact transportReply_outputWrite p c s v n z r after
  | probeInit n accepted =>
    simp only [update, hp]
    exact probeReply_outputWrite p c s n accepted _ r
  | probe n accepted probe =>
    simp only [update, hp]
    exact probeReply_outputWrite p c s n accepted probe r
  | validate n accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals first
      | solve | simp [OutputWrite, HeavyTailedSospInvariants.markCharge]
      | (split
         · exact startCycle_outputWrite p c _
         · simp [OutputWrite, HeavyTailedSospInvariants.markCharge])
  | ncInit v =>
    simp only [update, hp]
    exact transportReply_outputWrite p c s _ 0 0 r _
  | done => simp [update, hp, OutputWrite, HeavyTailedSospInvariants.markCharge]

lemma trajectory_target (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (trajectory (sampleStep p c g H) N (initial p target) ξ).target = target := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [trajectory_succ_last]
    exact (update_outputWrite p c _ (ξ n).1 _).1.trans ih

lemma trajectory_selected_succ (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let X := fun k => trajectory (sampleStep p c g H) k (initial p target) ξ
    (X (n + 1)).selected =
      if HeavyTailedSospInvariants.markCharge p (X (n + 1)).phase = 1 ∧
          (X (n + 1)).cycleIndex = target then (X (n + 1)).point else (X n).selected := by
  intro X
  have hw := (update_outputWrite p c (X n) (ξ n).1
    (match (query p c (X n) (ξ n).1).2 with
      | none => g (query p c (X n) (ξ n).1).1 (ξ n).2
      | some v => H (query p c (X n) (ξ n).1).1 (ξ n).2 v)).2
  change (sampleStep p c g H (X n) (ξ n)).selected =
    (if HeavyTailedSospInvariants.markCharge p (sampleStep p c g H (X n) (ξ n)).phase = 1 ∧
        (sampleStep p c g H (X n) (ξ n)).cycleIndex = (X n).target
      then (sampleStep p c g H (X n) (ξ n)).point else (X n).selected) at hw
  have he : X (n + 1) = sampleStep p c g H (X n) (ξ n) := trajectory_succ_last _ _ _ _
  rw [← he, trajectory_target p c g H target n ξ] at hw
  exact hw

lemma selected_of_unique_mark (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target k N : ℕ) (ξ : ℕ → Aux p c × p.Ω) (hkN : k ≤ N)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1)
    (hc : (trajectory (sampleStep p c g H) k (initial p target) ξ).cycleIndex = target) :
    (trajectory (sampleStep p c g H) N (initial p target) ξ).selected =
      (trajectory (sampleStep p c g H) k (initial p target) ξ).point := by
  let X := fun n => trajectory (sampleStep p c g H) n (initial p target) ξ
  have hk : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    subst k
    simp [trajectory, initial, HeavyTailedSospInvariants.markCharge] at hm
  have hbase : (X k).selected = (X k).point := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact (trajectory_selected_succ p c g H target j ξ).trans (ite_eq_left ⟨hm, hc⟩)
  have hstay (n : ℕ) : (X (k + n)).selected = (X k).point := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      rw [Nat.add_succ, trajectory_selected_succ p c g H target (k + n) ξ]
      have hn : ¬ (HeavyTailedSospInvariants.markCharge p (X (k + n + 1)).phase = 1 ∧
          (X (k + n + 1)).cycleIndex = target) := by
        intro hh
        have he := marked_cycleIndex_injective p c g H target k (k + n + 1) ξ hm hh.1
          (hc.trans hh.2.symm)
        omega
      rw [ite_eq_right hn]
      exact ih
  simpa only [Nat.add_sub_of_le hkN] using hstay (N - k)

lemma markCharge_le_one (p : Params) (ph : Phase p) :
    HeavyTailedSospInvariants.markCharge p ph ≤ 1 := by
  cases ph with
  | transport v n z after =>
    cases after <;> simp only [HeavyTailedSospInvariants.markCharge]
    all_goals solve | omega | (split_ifs <;> omega)
  | _ => simp [HeavyTailedSospInvariants.markCharge]

lemma completed_mark_exists (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N j : ℕ) (ξ : ℕ → Aux p c × p.Ω) (hj : j < c.cycles)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    ∃ k < N, HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1 ∧
      (trajectory (sampleStep p c g H) k (initial p target) ξ).cycleIndex = j := by
  have ht := HeavyTailedSospWork.completed_mark_count p c g H target N ξ hdone
  obtain ⟨k, hk, hm, hc⟩ := HeavyTailedSospEpoch.unit_charge_prefix
    (fun k => HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase)
    (fun k => markCharge_le_one p _) N j (ht.symm ▸ hj)
  exact ⟨k, hk, hm, (marked_cycleIndex p c g H target k ξ hm).trans hc⟩

lemma marked_cycleIndex_lt_cycles (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N k : ℕ) (ξ : ℕ → Aux p c × p.Ω) (hk : k < N)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (trajectory (sampleStep p c g H) k (initial p target) ξ).cycleIndex < c.cycles := by
  let f := fun n => HeavyTailedSospInvariants.markCharge p
    (trajectory (sampleStep p c g H) n (initial p target) ξ).phase
  have hb : (∑ n ∈ Finset.range (k + 1), f n) ≤ ∑ n ∈ Finset.range N, f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_range_succ] at hb
  have ht := HeavyTailedSospWork.completed_mark_count p c g H target N ξ hdone
  have hc := marked_cycleIndex p c g H target k ξ hm
  change f k = 1 at hm
  change (∑ n ∈ Finset.range N, f n) = c.cycles at ht
  change _ = ∑ n ∈ Finset.range k, f n at hc
  omega

lemma completed_output_sum (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) (φ : Space p → ℝ)
    (hdone : (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    (∑ j ∈ Finset.range c.cycles,
      φ (trajectory (sampleStep p c g H) N (initial p j) ξ).selected) =
      ∑ k ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p
        (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase = 1 then
          φ (trajectory (sampleStep p c g H) k (initial p 0) ξ).point else 0 := by
  classical
  let X := fun k => trajectory (sampleStep p c g H) k (initial p 0) ξ
  let F := (Finset.range N).filter (fun k => HeavyTailedSospInvariants.markCharge p (X k).phase = 1)
  have he : (∑ k ∈ F, φ (X k).point) =
      ∑ j ∈ Finset.range c.cycles, φ (trajectory (sampleStep p c g H) N (initial p j) ξ).selected := by
    apply Finset.sum_bij (fun k _ => (X k).cycleIndex)
    · intro k hk
      obtain ⟨hkN, hm⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_range.mpr (marked_cycleIndex_lt_cycles p c g H 0 N k ξ
        (Finset.mem_range.mp hkN) hm hdone)
    · intro k hk l hl hkl
      exact marked_cycleIndex_injective p c g H 0 k l ξ
        (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2 hkl
    · intro j hj
      obtain ⟨k, hk, hm, hc⟩ := completed_mark_exists p c g H 0 N j ξ
        (Finset.mem_range.mp hj) hdone
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hm⟩, hc⟩
    · intro k hk
      let j := (X k).cycleIndex
      have hc := coreEq_trajectory p c g H j 0 k ξ
      have hm : HeavyTailedSospInvariants.markCharge p
          (trajectory (sampleStep p c g H) k (initial p j) ξ).phase = 1 := by
        rw [hc.2.2.2.2]
        exact (Finset.mem_filter.mp hk).2
      have hs := selected_of_unique_mark p c g H j k N ξ
        (Nat.le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)) hm hc.2.2.2.1
      exact congrArg φ (hs.trans hc.1).symm
  rw [← he]
  exact Finset.sum_filter _ _

lemma completed_uniform_output_integral (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) (φ : Space p → ℝ) (hT : 0 < c.cycles)
    (hdone : (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    (∫ j : Fin (max 1 c.cycles), φ (trajectory (sampleStep p c g H) N (initial p j.val) ξ).selected
      ∂(PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure) =
      (c.cycles : ℝ)⁻¹ * ∑ k ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p
        (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase = 1 then
          φ (trajectory (sampleStep p c g H) k (initial p 0) ξ).point else 0 := by
  rw [OracleTemplate.MixedNoise.integral_uniform_finite]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => φ (trajectory (sampleStep p c g H) N (initial p j) ξ).selected)]
  rw [max_eq_right (by omega : 1 ≤ c.cycles), completed_output_sum p c g H N ξ φ hdone]

lemma completed_joint_output_integral (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (N : ℕ) (φ : Space p → ℝ) (hT : 0 < c.cycles)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hi : Integrable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      φ (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected)
      ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P)) :
    (∫ z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω),
      φ (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected
      ∂((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P)) =
      (c.cycles : ℝ)⁻¹ * ∫ ξ, ∑ k ∈ Finset.range N,
        if HeavyTailedSospInvariants.markCharge p
          (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase = 1 then
            φ (trajectory (sampleStep p c g H) k (initial p 0) ξ).point else 0 ∂P := by
  rw [integral_prod_symm _ hi]
  simp_rw [completed_uniform_output_integral p c g H N _ φ hT (hdone _)]
  exact integral_const_mul _ _

lemma completed_selected_displacement (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) (ht : target < c.cycles)
    (hdone : (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    ‖(trajectory (sampleStep p c g H) N (initial p target) ξ).selected - p.x0‖ ≤ N * c.h := by
  have hc := coreEq_trajectory p c g H target 0 N ξ
  have hdT : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done :=
    hc.2.2.2.2.trans hdone
  obtain ⟨k, hk, hm, hcycle⟩ := completed_mark_exists p c g H target N target ξ ht hdT
  rw [selected_of_unique_mark p c g H target k N ξ (Nat.le_of_lt hk) hm hcycle]
  exact (HeavyTailedSospGeometry.trajectory_displacement p c g H hd hh hs hseg
    (initial p target) (HeavyTailedSospGeometry.initial_bound p c target) k ξ).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hk) hh)

lemma completed_joint_output_integrable (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (N : ℕ) (φ : Space p → ℝ) (hφ : Continuous φ) (hT : 0 < c.cycles)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    Integrable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      φ (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected)
      ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P) := by
  have hout : Measurable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected) :=
    (HeavyTailedSospMeasurable.measurable_trajectory_output p c g H hg hH N).comp
      (((measurable_of_finite (fun j : Fin (max 1 c.cycles) => j.val)).comp measurable_fst).prodMk measurable_snd)
  refine HeavyTailedSospForecastIntegration.continuous_comp_integrable_of_bounded_range
    p ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P) φ hφ _ hout p.x0 (N * c.h) ?_
  intro z
  apply completed_selected_displacement p c g H hd hh hs hseg z.1.val N z.2 _ (hdone z.2)
  simpa only [max_eq_right (by omega : 1 ≤ c.cycles)] using z.1.isLt

lemma completed_joint_indicator_integral (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (N : ℕ) (B : Set (Space p)) (hB : MeasurableSet B) (hT : 0 < c.cycles)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    (∫ z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω),
      B.indicator (fun _ => (1 : ℝ))
        (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected
      ∂((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P)) =
      (c.cycles : ℝ)⁻¹ * ∫ ξ, ∑ k ∈ Finset.range N,
        (badMarkEvent p B).indicator (fun _ => (1 : ℝ))
          (trajectory (sampleStep p c g H) k (initial p 0) ξ) ∂P := by
  classical
  have hout : Measurable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected) :=
    (HeavyTailedSospMeasurable.measurable_trajectory_output p c g H hg hH N).comp
      (((measurable_of_finite (fun j : Fin (max 1 c.cycles) => j.val)).comp measurable_fst).prodMk measurable_snd)
  have hi : Integrable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      B.indicator (fun _ => (1 : ℝ))
        (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected)
      ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P) :=
    (integrable_const (1 : ℝ)).indicator (hB.preimage hout)
  rw [completed_joint_output_integral p c g H P N (B.indicator (fun _ => (1 : ℝ))) hT hdone hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase = 1
  all_goals simp [badMarkEvent, Set.indicator, hm]

lemma target_paired_streams_preserving (p : Params) (c : Config)
    (R : Measure (Fin (max 1 c.cycles))) [IsProbabilityMeasure R]
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (P : Measure (ℕ → p.Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) P0 P) :
    MeasurePreserving
      (fun z : (Fin (max 1 c.cycles) × (ℕ → Aux p c)) × (ℕ → p.Ω) =>
        (z.1.1, fun k => (z.1.2 k, z.2 k)))
      ((R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)))).prod P)
      (R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0)) := by
  have hstream := hiid.stream_law
  have hprod := (MeasurePreserving.id
    (R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c))))).prod hstream
  exact (LongTails.Proofs.HeavyTailedTapeExecution.initial_zip_streams_preserving
    R (auxLaw p c : Measure (Aux p c)) P0).comp hprod

lemma unpaddedWork_target_independent (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (j k N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    HeavyTailedSospWork.unpaddedWork p c g H j N ξ =
      HeavyTailedSospWork.unpaddedWork p c g H k N ξ := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [(coreEq_trajectory p c g H j k n ξ).2.2.2.2]

lemma capped_selected_eq_completed (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N C : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hwork : HeavyTailedSospWork.unpaddedWork p c g H 0 N ξ ≤ C) :
    (trajectory (sampleStep p c g H) C (initial p target) ξ).selected =
      (trajectory (sampleStep p c g H) N (initial p target) ξ).selected := by
  have hd := (coreEq_trajectory p c g H target 0 N ξ).2.2.2.2.trans hdone
  have hw : HeavyTailedSospWork.unpaddedWork p c g H target N ξ ≤ C := by
    rw [unpaddedWork_target_independent p c g H target 0 N ξ]
    exact hwork
  exact congrArg State.selected (HeavyTailedSospWork.capped_state_eq_completed p c g H target N C ξ hd hw)

lemma all_vector_lower_bound_iff (p : Params)
    (A : Space p → Space p →L[ℝ] Space p) (x : Space p) (κ : ℝ) :
    (∀ v : Space p, κ * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫) ↔
      x ∉ HeavyTailedSospDetectionIntegration.strictBadCurvature p A κ := by
  constructor
  · intro h ⟨v, hv, hb⟩
    have hh := h v
    rw [hv, one_pow, mul_one] at hh
    exact (not_lt_of_ge hh) hb
  · intro h v
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hn]
    have hb : κ ≤ ⟪u, A x u⟫ := le_of_not_gt (fun hh => h ⟨u, hu, hh⟩)
    have he : v = ‖v‖ • u := by simp [u, smul_smul, hn]
    have hi : ⟪v, A x v⟫ = ‖v‖ ^ 2 * ⟪u, A x u⟫ := by
      calc
        ⟪v, A x v⟫ = ⟪‖v‖ • u, A x (‖v‖ • u)⟫ := by rw [← he]
        _ = ‖v‖ ^ 2 * ⟪u, A x u⟫ := by simp [map_smul, inner_smul_left, inner_smul_right]; ring
    rw [hi]
    nlinarith [sq_nonneg ‖v‖, mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)]

lemma probability_norm_gt_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → E) (hY : Integrable (fun ω => ‖Y ω‖) P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε < ‖Y ω‖} ≤ (∫ ω, ‖Y ω‖ ∂P) / ε := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (Y ω))) hY ε
  have hs : P.real {ω | ε < ‖Y ω‖} ≤ P.real {ω | ε ≤ ‖Y ω‖} :=
    measureReal_mono (by
      intro ω h
      change ε < ‖Y ω‖ at h
      change ε ≤ ‖Y ω‖
      exact le_of_lt h)
  apply (le_div_iff₀ hε).mpr
  nlinarith

lemma secondOrderAccurate_iff (p : Params) (f : Space p → ℝ) (x : Space p) :
    secondOrderAccurate p f x ↔ ‖gradient f x‖ ≤ p.ε ∧
      x ∉ HeavyTailedSospDetectionIntegration.strictBadCurvature p
        (fun y => fderiv ℝ (gradient f) y) (-Real.sqrt (p.ρ * p.ε)) := by
  exact and_congr_right (fun _ => all_vector_lower_bound_iff p _ x _)

lemma secondOrderAccurate_measurableSet (p : Params) (f : Space p → ℝ)
    (hG : Continuous (gradient f)) (hA : Continuous (fun x => fderiv ℝ (gradient f) x)) :
    MeasurableSet {x | secondOrderAccurate p f x} := by
  have he : {x | secondOrderAccurate p f x} =
      {x | ‖gradient f x‖ ≤ p.ε} ∩
        (HeavyTailedSospDetectionIntegration.strictBadCurvature p
          (fun y => fderiv ℝ (gradient f) y) (-Real.sqrt (p.ρ * p.ε)))ᶜ := by
    ext x
    exact secondOrderAccurate_iff p f x
  rw [he]
  exact (measurableSet_le hG.norm.measurable measurable_const).inter
    (HeavyTailedSospDetectionIntegration.strictBadCurvature_isOpen p _ hA _).measurableSet.compl

lemma success_probability_of_failure_bounds (p : Params) (f : Space p → ℝ)
    (hG : Continuous (gradient f)) (hA : Continuous (fun x => fderiv ℝ (gradient f) x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : Ω → Space p) (hZ : Measurable Z) (W : Set Ω)
    (he : ∀ ω, ω ∉ W → Z ω = Y ω)
    (hg : P.real {ω | p.ε < ‖gradient f (Y ω)‖} ≤ 1 / 500)
    (hc : P.real {ω | Y ω ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p
      (fun x => fderiv ℝ (gradient f) x) (-Real.sqrt (p.ρ * p.ε))} ≤ 21 / 100)
    (hw : P.real W ≤ 1 / 10) :
    2 / 3 ≤ P.real {ω | secondOrderAccurate p f (Z ω)} := by
  let B := {ω | p.ε < ‖gradient f (Y ω)‖}
  let C := {ω | Y ω ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p
    (fun x => fderiv ℝ (gradient f) x) (-Real.sqrt (p.ρ * p.ε))}
  let S := {ω | secondOrderAccurate p f (Z ω)}
  have hS : MeasurableSet S := (secondOrderAccurate_measurableSet p f hG hA).preimage hZ
  have hsub : Sᶜ ⊆ (B ∪ C) ∪ W := by
    intro ω hω
    by_cases hh : ω ∈ W
    · exact Or.inr hh
    · apply Or.inl
      by_cases hb : p.ε < ‖gradient f (Y ω)‖
      · exact Or.inl hb
      · apply Or.inr
        by_contra hcurv
        apply hω
        change secondOrderAccurate p f (Z ω)
        rw [he ω hh, secondOrderAccurate_iff]
        exact ⟨le_of_not_gt hb, hcurv⟩
  have hb := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) (B ∪ C) W)
  have hbc := measureReal_union_le (μ := P) B C
  have hsum := measureReal_add_measureReal_compl (μ := P) hS
  rw [probReal_univ] at hsum
  change P.real B ≤ 1 / 500 at hg
  change P.real C ≤ 21 / 100 at hc
  change 2 / 3 ≤ P.real S
  linarith

lemma completed_gradient_failure_bound (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (G : Space p → Space p) (hG : Continuous G)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (N : ℕ) (hT : 0 < c.cycles) {ε : ℝ} (hε : 0 < ε)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hb : (∫ ξ, HeavyTailedSospForecastIntegration.markedGradientTotal p c G g H 0 N ξ ∂P) /
      c.cycles ≤ ε / 500) :
    ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P).real
      {z | ε < ‖G (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected‖} ≤ 1 / 500 := by
  have hi := completed_joint_output_integrable p c g hg H hH P hd hh hs hseg N
    (fun x => ‖G x‖) hG.norm hT hdone
  have he := completed_joint_output_integral p c g H P N (fun x => ‖G x‖) hT hdone hi
  have hb' : (∫ z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω),
      ‖G (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected‖
      ∂((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P)) ≤ ε / 500 := by
    rw [he]
    simpa only [HeavyTailedSospForecastIntegration.markedGradientTotal, div_eq_mul_inv, mul_comm] using hb
  refine (probability_norm_gt_bound _ _ hi hε).trans ?_
  apply (div_le_iff₀ hε).mpr
  linarith

lemma completed_set_probability (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (N : ℕ) (B : Set (Space p)) (hB : MeasurableSet B) (hT : 0 < c.cycles)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done) :
    ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P).real
      {z | (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected ∈ B} =
      (∫ ξ, ∑ k ∈ Finset.range N, (badMarkEvent p B).indicator (fun _ => (1 : ℝ))
        (trajectory (sampleStep p c g H) k (initial p 0) ξ) ∂P) / c.cycles := by
  have hout : Measurable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected) :=
    (HeavyTailedSospMeasurable.measurable_trajectory_output p c g H hg hH N).comp
      (((measurable_of_finite (fun j : Fin (max 1 c.cycles) => j.val)).comp measurable_fst).prodMk measurable_snd)
  have he := completed_joint_indicator_integral p c g hg H hH P N B hB hT hdone
  have hi := integral_indicator_one (μ := (PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod P)
    (hB.preimage hout)
  have hh := hi.symm.trans he
  simp only [div_eq_mul_inv, mul_comm] at hh ⊢
  convert hh using 2
  ext z
  rfl

lemma completed_curvature_failure_bound (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (A : Space p → Space p →L[ℝ] Space p) (hA : Continuous A) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (hρh : ρ * c.h ≤ c.γ)
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (N : ℕ) (hT : 0 < c.cycles) {δ : ℝ} (hδ : 0 ≤ δ) (hδu : δ ≤ 1 / 100)
    (hmiss : ∀ x ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-4 * c.γ),
      (Measure.infinitePi fun _ : ℕ => Q).real
        {ξ | HeavyTailedSospDetection.detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ δ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hacc : (∫ ξ, ∑ k ∈ Finset.range N,
      (HeavyTailedSospWork.ncCharge p (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ => Q)) / c.cycles ≤ 1 / 5) :
    ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => Q)).real
      {z | (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected ∈
        HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-5 * c.γ)} ≤ 21 / 100 := by
  let P := Measure.infinitePi fun _ : ℕ => Q
  have hb := (expected_bad_mark_start_count_bound p c g hg H hH A hA hρ hLip hρh
    P hd hh hs hseg 0 N hdone).2
  have hc := (HeavyTailedSospDetectionIntegration.expected_bad_start_count_bound p c g hg H hH
    (HeavyTailedSospDetectionIntegration.strictBadCurvature p A (-4 * c.γ))
    (HeavyTailedSospDetectionIntegration.strictBadCurvature_isOpen p A hA _).measurableSet
    Q δ hδ hmiss 0 N hdone).2
  rw [completed_set_probability p c g hg H hH P N _
    (HeavyTailedSospDetectionIntegration.strictBadCurvature_isOpen p A hA _).measurableSet hT hdone]
  have hTr : (0 : ℝ) < c.cycles := by exact_mod_cast hT
  apply (div_le_iff₀ hTr).mpr
  have ha := (div_le_iff₀ hTr).mp hacc
  have hδT := mul_le_mul_of_nonneg_right hδu (le_of_lt hTr)
  dsimp only at hb hc
  linarith

end LongTails.Proofs.HeavyTailedSospOutput
