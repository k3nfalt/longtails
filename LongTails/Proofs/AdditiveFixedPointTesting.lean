import LongTails.Proofs.AdditiveFixedPointProcess

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointTesting

open HeavyTailedProductProcess AdditiveFixedPointProcess

noncomputable def test {S W : Type*} [DecidableEq W] (g : S → W) (w : W) (s : S) : ℝ≥0∞ :=
  if g s = w then 1 else 0

lemma test_measurable {S W : Type*} [DecidableEq W] [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSingletonClass W] {g : S → W} (hg : Measurable g) (w : W) :
    Measurable (test g w) :=
  Measurable.ite (hg (measurableSet_singleton w)) measurable_const measurable_const

lemma test_sq {S W : Type*} [DecidableEq W] (g : S → W) (w : W) (s : S) :
    test g w s ^ 2 = test g w s := by simp [test, apply_ite]

lemma rare_word {S W : Type*} [Fintype W] [Nonempty W] [DecidableEq W] [MeasurableSpace W]
    [MeasurableSingletonClass W] [MeasurableSpace S] {g : S → W} (hg : Measurable g) {n : ℕ}
    (π : Fin n → ProbabilityMeasure S) :
    ∃ w : W, ∑ j, (∫⁻ s, test g w s ∂(π j : Measure S)) ≤ n / (Fintype.card W : ℝ≥0∞) := by
  classical
  let mass (w : W) := ∑ j, (∫⁻ s, test g w s ∂(π j : Measure S))
  have hsum : ∑ w, mass w = n := by
    unfold mass
    rw [Finset.sum_comm]
    have he (j : Fin n) : ∑ w, (∫⁻ s, test g w s ∂(π j : Measure S)) = 1 := by
      rw [← lintegral_finsetSum _ (fun w _ => test_measurable hg w)]
      simp [test]
    simp [he]
  obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ mass Finset.univ_nonempty
  refine ⟨w, ?_⟩
  change mass w ≤ _
  apply (ENNReal.le_div_iff_mul_le _ _).mpr
  · rw [← hsum, mul_comm, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum Finset.univ mass _ (fun i hi => hw i hi)
  · simp [Fintype.card_ne_zero]
  · simp

lemma trajectory_congr_before {S E W : Type*} (step full : S → E → S)
    (g : S → W) (w : W) (hagree : ∀ s, g s ≠ w → ∀ z, full s z = step s z)
    (n : ℕ) (s : S) (ξ : ℕ → E) (havoid : ∀ j < n, g (trajectory step j s ξ) ≠ w) :
    trajectory full n s ξ = trajectory step n s ξ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajectory_succ_last, trajectory_succ_last,
      ih (fun j hj => havoid j (by omega)), hagree _ (havoid n (by omega))]

lemma trajectory_test_bound {S E W : Type*} [DecidableEq W] (step full : S → E → S)
    (g : S → W) (w : W) (hagree : ∀ s, g s ≠ w → ∀ z, full s z = step s z)
    (pay : S → ℝ≥0∞) (hp : ∀ s, pay s ≤ 1) (n : ℕ) (s : S) (ξ : ℕ → E) :
    pay (trajectory full n s ξ) ≤ pay (trajectory step n s ξ) +
      ∑ j : Fin n, test g w (trajectory step j s ξ) := by
  classical
  by_cases ha : ∀ j < n, g (trajectory step j s ξ) ≠ w
  · rw [trajectory_congr_before step full g w hagree n s ξ ha]
    exact le_self_add
  · push Not at ha
    obtain ⟨j, hj, he⟩ := ha
    have hb := Finset.single_le_sum (f := fun t : Fin n => test g w (trajectory step t s ξ))
      (fun _ _ => zero_le) (Finset.mem_univ (⟨j, hj⟩ : Fin n))
    rw [show test g w (trajectory step (⟨j, hj⟩ : Fin n) s ξ) = 1 by simp [test, he]] at hb
    exact (hp _).trans (hb.trans le_add_self)

noncomputable def risk {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (π : ProbabilityMeasure S) (μ : Measure E) [IsProbabilityMeasure μ]
    (step : S → E → S) (pay : S → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ s, pay s ∂(stateLaw π μ step n : Measure S)

lemma risk_joint {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (π : ProbabilityMeasure S) (μ : Measure E) [IsProbabilityMeasure μ]
    {step : S → E → S} {pay : S → ℝ≥0∞} (hs : Measurable step.uncurry) (hp : Measurable pay)
    (n : ℕ) : risk π μ step pay n =
      ∫⁻ z : S × (ℕ → E), pay (trajectory step n z.1 z.2)
        ∂(π : Measure S).prod (Measure.infinitePi fun _ : ℕ => μ) :=
  lintegral_map hp (trajectory_measurable hs n)

lemma risk_coupling {S E W : Type*} [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace W]
    [MeasurableSingletonClass W] [DecidableEq W] (π : ProbabilityMeasure S) (μ : Measure E)
    [IsProbabilityMeasure μ] {step full : S → E → S} (hs : Measurable step.uncurry)
    (hf : Measurable full.uncurry) {g : S → W} (hg : Measurable g) (w : W)
    (hagree : ∀ s, g s ≠ w → ∀ z, full s z = step s z)
    {pay : S → ℝ≥0∞} (hp : Measurable pay) (hp1 : ∀ s, pay s ≤ 1) (n : ℕ) :
    risk π μ full pay n ≤ risk π μ step pay n +
      ∑ j : Fin n, risk π μ step (test g w) j := by
  simp_rw [risk_joint π μ hf hp, risk_joint π μ hs hp, risk_joint π μ hs (test_measurable hg w)]
  rw [← lintegral_finsetSum (Finset.univ : Finset (Fin n))
    (f := fun j (z : S × (ℕ → E)) => test g w (trajectory step j z.1 z.2))
    (fun j _ => (test_measurable hg w).comp (trajectory_measurable hs j)),
    ← lintegral_add_left (f := fun z : S × (ℕ → E) => pay (trajectory step n z.1 z.2))
      (hp.comp (trajectory_measurable hs n))]
  apply lintegral_mono
  intro z
  exact trajectory_test_bound step full g w hagree pay hp1 n z.1 z.2

lemma risk_add {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (π : ProbabilityMeasure S) (μ : Measure E) [IsProbabilityMeasure μ]
    {step : S → E → S} {pay : S → ℝ≥0∞} (hs : Measurable step.uncurry) (hp : Measurable pay)
    (n m : ℕ) : risk π μ step pay (n + m) = risk π μ step (average μ step pay m) n := by
  unfold risk
  rw [stateLaw_integral π μ hs hp, stateLaw_integral π μ hs (average_measurable μ hs hp m)]
  simp_rw [average_add μ hs hp n m]

lemma average_le_one {S E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (step : S → E → S) {pay : S → ℝ≥0∞} (hp : ∀ s, pay s ≤ 1) (n : ℕ) (s : S) :
    average μ step pay n s ≤ 1 := by
  exact (lintegral_mono (g := fun _ => 1) (fun ξ => hp (trajectory step n s ξ))).trans_eq
    (by simp)

end LongTails.Proofs.AdditiveFixedPointTesting
