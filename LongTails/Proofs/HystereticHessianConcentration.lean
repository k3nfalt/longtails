import LongTails.Proofs.HystereticHessianTransport
import LongTails.Proofs.GuardedHessianIntegration

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianConcentration

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianTransport HystereticHessianMoments HystereticHessianPhases
open AffineTransportConcentration StoppedVectorConcentration

set_option maxHeartbeats 800000 in
lemma macro_noise_tail (p : Params) (c : Config) {Ω Ψ : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q] (R : Measure Ψ) [IsProbabilityMeasure R]
    (ξ : ℕ → Ψ → ℝ × Ω)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q R)
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hanswer : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (s : State p c) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    {a C V θ : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hV : 0 ≤ V) (hθ : 0 ≤ θ)
    (hmom : ∀ t : State p c,
      Integrable (transportNoise p c Q answer g t) Q ∧
        Integrable (fun z => ‖transportNoise p c Q answer g t z‖ ^ 2) Q ∧
        (∫ z, transportNoise p c Q answer g t z ∂Q) = 0 ∧
        (∀ z, ‖transportNoise p c Q answer g t z‖ ≤ C) ∧
        (∫ z, ‖transportNoise p c Q answer g t z‖ ^ 2 ∂Q) ≤ V)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1) :
    R.real {ω | ∃ k ≤ macroCalls c - s.slot,
      a < ‖∑ i ∈ Finset.range k,
        transportNoise p c Q answer g (path p c answer s (fun j => ξ j ω) i) (ξ i ω)‖} ≤
      Real.exp (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) *
        ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2) := by
  let Y := fun k (w : (Fin k → ℝ × Ω) × (ℝ × Ω)) =>
    transportNoise p c Q answer g (historyState p c answer s k w.1) w.2
  let A := fun k (h : Fin k → ℝ × Ω) => localMask p c g (historyState p c answer s k h)
  have hY (k : ℕ) : Measurable (Y k) :=
    (measurable_transportNoise p c Q answer hanswer g hg).comp
      (((measurable_historyState p c answer hanswer s k).comp measurable_fst).prodMk measurable_snd)
  have hA (k : ℕ) : Measurable (A k) :=
    (measurable_localMask p c g hg).comp (measurable_historyState p c answer hanswer s k)
  have hi (k : ℕ) (h : Fin k → ℝ × Ω) : Integrable (fun z => Y k (h, z)) Q :=
    (hmom (historyState p c answer s k h)).1
  have h2i (k : ℕ) (h : Fin k → ℝ × Ω) : Integrable (fun z => ‖Y k (h, z)‖ ^ 2) Q :=
    (hmom (historyState p c answer s k h)).2.1
  have hcount (ω : Ψ) : historyActiveCount A (macroCalls c - s.slot) (fun i => ξ i ω) ≤
      (c.epoch + 1) * (c.transportBatch + 1) :=
    macro_masked_transport_count p c answer s (fun i => ξ i ω) hc hf A
      (fun k h hh => localMask_transport p c g (historyState p c answer s k h) hh)
  have hh := iid_active_count_energy_bound hsamples.measurable hsamples.independent hsamples.marginal
    hY hi h2i A hA (fun k h hh z => transportNoise_inactive p c Q answer g (historyState p c answer s k h) hh z)
    ha hC hV hθ (fun k h z => (hmom (historyState p c answer s k h)).2.2.2.1 z)
    (fun k h => (hmom (historyState p c answer s k h)).2.2.1) (fun k h => (hmom (historyState p c answer s k h)).2.2.2.2) hsmall
    ((c.epoch + 1) * (c.transportBatch + 1)) (macroCalls c - s.slot) hcount
  have heq (ω : Ψ) (i : ℕ) : historyState p c answer s i (fun j => ξ j ω) =
      path p c answer s (fun j => ξ j ω) i :=
    historyState_eq_path p c answer s (fun j => ξ j ω) i
  simp only [history_stopped_sum_eq, Y, heq] at hh
  exact maximal_sum_tail ha hθ (macroCalls c - s.slot) hh.1 hh.2

lemma oracle_macro_noise_tail (p : Params) (c : Config) {Ω Ψ : Type} [MeasurableSpace Ω] [MeasurableSpace Ψ]
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
    (R : Measure Ψ) [IsProbabilityMeasure R] (ξ : ℕ → Ψ → ℝ × Ω)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      ((LongTails.Algorithms.GuardedHessianTransport.uniformLaw : Measure ℝ).prod P) R)
    (s : State p c) (hc : CounterValid p c s) (hf : PhaseFits p c s)
    {a θ : ℝ} (ha0 : 0 ≤ a) (hθ : 0 ≤ θ) :
    let Q := (LongTails.Algorithms.GuardedHessianTransport.uniformLaw : Measure ℝ).prod P
    let C := 2 * c.clipThreshold / ((c.transportBatch + 1 : ℕ) : ℝ)
    let V := (2 * c.clipThreshold) ^ (2 - p.q) * (512 * K * c.fineStep) ^ p.q /
      ((c.transportBatch + 1 : ℕ) : ℝ) ^ 2
    θ * (2 * a * C + C ^ 2) ≤ 1 →
      R.real {ω | ∃ k ≤ macroCalls c - s.slot,
        a < ‖∑ i ∈ Finset.range k,
          transportNoise p c Q answer g (path p c answer s (fun j => ξ j ω) i) (ξ i ω)‖} ≤
        Real.exp (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) *
          ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2) := by
  intro Q C V henergy
  have hK0 : 0 ≤ K := by
    nlinarith [mul_nonneg hL1 (by positivity : 0 ≤ 4 * c.radius),
      mul_nonneg hα (by positivity : 0 ≤ 4 * c.radius)]
  apply macro_noise_tail p c Q R ξ hsamples answer ha g hg.continuous.measurable s hc hf
    ha0 (by dsimp [C]; positivity) (by dsimp [V]; positivity) hθ _ henergy
  intro t
  exact transportNoise_moments p c P answer ha g hL0 hL1 hq hq2 hσ hα hU hη hτ hK
    hg hD hH hi hm hpi hb hsmall hbase t

def macroBad (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (a : ℝ) : Set (State p c × (ℕ → ℝ × Ω)) :=
  {w | ∃ k ≤ macroCalls c - w.1.slot,
    a < ‖∑ i ∈ Finset.range k,
      transportNoise p c Q answer g (path p c answer w.1 w.2 i) (w.2 i)‖}

lemma measurableSet_macroBad (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [SFinite Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (a : ℝ) : MeasurableSet (macroBad p c Q answer g a) := by
  have hpath (i : ℕ) : Measurable (fun w : State p c × (ℕ → ℝ × Ω) => path p c answer w.1 w.2 i) :=
    HeavyTailedProductProcess.trajectory_measurable (measurable_advance p c answer ha) i
  have hsum (k : ℕ) : Measurable (fun w : State p c × (ℕ → ℝ × Ω) =>
      ∑ i ∈ Finset.range k, transportNoise p c Q answer g (path p c answer w.1 w.2 i) (w.2 i)) :=
    Finset.measurable_sum _ (fun i _ => (measurable_transportNoise p c Q answer ha g hg).comp
      ((hpath i).prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hslot : Measurable (fun w : State p c × (ℕ → ℝ × Ω) => macroCalls c - w.1.slot) := by
    fun_prop
  unfold macroBad
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_le measurable_const hslot).inter (measurableSet_lt measurable_const (hsum k).norm)

lemma fresh_macro_noise_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (s : State p c) (hc : CounterValid p c s) (hf : PhaseFits p c s) (a δ : ℝ)
    (htail : ∀ t : State p c, CounterValid p c t → PhaseFits p c t →
      (Measure.infinitePi fun _ : ℕ => Q).real {ξ | (t, ξ) ∈ macroBad p c Q answer g a} ≤ δ)
    (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | (path p c answer s ξ n, fun k => ξ (n + k)) ∈ macroBad p c Q answer g a} ≤ δ := by
  let advance := fun (t : State p c) (z : ℝ × Ω) =>
    update p c t z.1 (answer (query p c t z.1) z.2)
  apply GuardedHessianIntegration.fresh_continuation_probability Q advance
    (measurable_advance p c answer ha) n s (macroBad p c Q answer g a)
    (measurableSet_macroBad p c Q answer ha g hg a) δ
  intro η
  have hh := HeavyTailedSospEpochIntegration.finite_iterate_invariant advance
    (fun t => CounterValid p c t ∧ PhaseFits p c t)
    (fun t z ht => ⟨update_counter_valid p c t ht.1 z.1 _,
      update_phase_fits p c t ht.1 ht.2 z.1 _⟩) n s ⟨hc, hf⟩ η
  exact htail _ hh.1 hh.2

lemma trial_macro_noise_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (a δ : ℝ)
    (htail : ∀ t : State p c, CounterValid p c t → PhaseFits p c t →
      (Measure.infinitePi fun _ : ℕ => Q).real {ξ | (t, ξ) ∈ macroBad p c Q answer g a} ≤ δ) :
    (Measure.infinitePi fun _ : ℕ => Q).real {ξ | ∃ j < c.macros + 1,
      (path p c answer (initial p c) ξ (j * macroCalls c),
        fun k => ξ (j * macroCalls c + k)) ∈ macroBad p c Q answer g a} ≤
      (c.macros + 1 : ℕ) * δ := by
  let R := Measure.infinitePi fun _ : ℕ => Q
  let A := fun j : ℕ => {ξ : ℕ → ℝ × Ω |
    (path p c answer (initial p c) ξ (j * macroCalls c),
      fun k => ξ (j * macroCalls c + k)) ∈ macroBad p c Q answer g a}
  have heq : {ξ : ℕ → ℝ × Ω | ∃ j < c.macros + 1, ξ ∈ A j} =
      ⋃ j ∈ Finset.range (c.macros + 1), A j := by
    ext ξ
    simp
  change R.real {ξ | ∃ j < c.macros + 1, ξ ∈ A j} ≤ _
  rw [heq]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (c.macros + 1), δ := by
      apply Finset.sum_le_sum
      intro j _
      exact fresh_macro_noise_probability p c Q answer ha g hg (initial p c)
        (initial_counter_valid p c) (initial_phase_fits p c) a δ htail (j * macroCalls c)
    _ = _ := by simp

lemma trial_noise_tail (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hanswer : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    {a C V θ : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hV : 0 ≤ V) (hθ : 0 ≤ θ)
    (hmom : ∀ t : State p c,
      Integrable (transportNoise p c Q answer g t) Q ∧
        Integrable (fun z => ‖transportNoise p c Q answer g t z‖ ^ 2) Q ∧
        (∫ z, transportNoise p c Q answer g t z ∂Q) = 0 ∧
        (∀ z, ‖transportNoise p c Q answer g t z‖ ≤ C) ∧
        (∫ z, ‖transportNoise p c Q answer g t z‖ ^ 2 ∂Q) ≤ V)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1) :
    (Measure.infinitePi fun _ : ℕ => Q).real {ξ | ∃ j < c.macros + 1,
      (path p c answer (initial p c) ξ (j * macroCalls c),
        fun k => ξ (j * macroCalls c + k)) ∈ macroBad p c Q answer g a} ≤
      (c.macros + 1 : ℕ) * Real.exp (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) *
        ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2) := by
  apply trial_macro_noise_probability p c Q answer hanswer g hg
  intro t hc hf
  exact macro_noise_tail p c Q (Measure.infinitePi fun _ : ℕ => Q) (fun k ξ => ξ k)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid Q) answer hanswer g hg t hc hf
    ha hC hV hθ hmom hsmall

lemma medoid_failure_of_first {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (u : E) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun ω => ‖X ω - u‖) P)
    (hm : (∫ ω, ‖X ω - u‖ ∂P) ≤ r / 1536) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | r < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hr6 : 0 < r / 6 := by positivity
  have hh := (hi.div_const (r / 6)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (norm_nonneg _) hr6.le))
    (s := {ω | r / 6 < ‖X ω - u‖}) (fun ω hω => (one_le_div hr6).mpr hω.le)
  have hb : P {ω | r / 6 < ‖X ω - u‖} ≤ ENNReal.ofReal (1 / 256 : ℝ) := by
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    apply (div_le_iff₀ hr6).mpr
    linarith
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hreal : P.real {ω | r / 6 < ‖X ω - u‖} ≤ 1 / 256 := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 256)] using ht
  have hmed := OracleTemplate.MultiplicativeRobustEstimator.medoid_failure_probability hX u hr6.le hreal n
  simpa only [show 6 * (r / 6) = r by ring] using hmed

lemma batched_medoid_failure_at_radius {E : Type*} {Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (u : E) {q κ r : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hr : 0 < r)
    (hi : Integrable X P) (hm : (∫ ω, X ω ∂P) = u)
    (hqi : Integrable (fun ω => ‖X ω - u‖ ^ q) P)
    (hqb : (∫ ω, ‖X ω - u‖ ^ q ∂P) ≤ κ)
    (B : ℕ) (hB : 0 < B) (hsize : 6 * κ / (B : ℝ) ^ (q - 1) ≤ (r / 1536) ^ q)
    (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin B => P)
      {ξ | r < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j => (B : ℝ)⁻¹ • ∑ k : Fin B, X (ξ j k)) - u‖} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hh := GuardedGradientMoments.finite_batch_accuracy hX u hq hq2
    (by positivity : 0 ≤ r / 1536) hi hm hqi hqb B hB hsize
  exact medoid_failure_of_first (by fun_prop) u hr hh.1 hh.2 n

lemma stream_medoid_failure_at_radius {E : Type*} {Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    {X : Ω → E} (hX : Measurable X) (u : E) {q κ r : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hr : 0 < r)
    (hi : Integrable X P) (hm : (∫ ω, X ω ∂P) = u)
    (hqi : Integrable (fun ω => ‖X ω - u‖ ^ q) P)
    (hqb : (∫ ω, ‖X ω - u‖ ^ q ∂P) ≤ κ)
    (B : ℕ) (hB : 0 < B) (hsize : 6 * κ / (B : ℝ) ^ (q - 1) ≤ (r / 1536) ^ q)
    (n : ℕ) :
    Q {ξ | r < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun j : Fin (n + 1) => (B : ℝ)⁻¹ •
        ∑ k ∈ Finset.range B, X (ξ (j.val * B + k))) - u‖} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hblocks := OracleTemplate.GapStrongGrowth.iid_groups_law P Q hIID (n + 1) B
  have hbound := batched_medoid_failure_at_radius hX u hq hq2 hr hi hm hqi hqb B hB hsize n
  have hset : MeasurableSet {ξ : Fin (n + 1) → Fin B → Ω |
      r < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j => (B : ℝ)⁻¹ • ∑ k : Fin B, X (ξ j k)) - u‖} := by
    apply measurableSet_lt measurable_const
    exact ((OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
      (by fun_prop)).sub_const u).norm
  rw [← hblocks.measure_preimage hset.nullMeasurableSet] at hbound
  have heq (ξ : ℕ → Ω) (j : Fin (n + 1)) :
      (∑ k : Fin B, X (ξ (j.val * B + k.val))) =
        ∑ k ∈ Finset.range B, X (ξ (j.val * B + k)) :=
    Fin.sum_univ_eq_sum_range (fun k => X (ξ (j.val * B + k))) B
  simpa only [Set.preimage_ofPred_eq, heq] using hbound

lemma macro_noise_prefix_eq (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (ξ : ℕ → ℝ × Ω) (n k : ℕ) :
    (∑ i ∈ Finset.range k, transportNoise p c Q answer g
      (path p c answer (path p c answer s ξ n) (fun j => ξ (n + j)) i) (ξ (n + i))) =
        ∑ i ∈ Finset.range k,
          transportNoise p c Q answer g (path p c answer s ξ (n + i)) (ξ (n + i)) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (HeavyTailedSospEpochIntegration.trajectory_add _ n i s ξ).symm

lemma macroBad_at_boundary (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (a : ℝ) (ξ : ℕ → ℝ × Ω) (j : ℕ) :
    (path p c answer (initial p c) ξ (j * macroCalls c),
      fun k => ξ (j * macroCalls c + k)) ∈ macroBad p c Q answer g a ↔
    ∃ k ≤ macroCalls c, a < ‖∑ i ∈ Finset.range k,
      transportNoise p c Q answer g
        (path p c answer (initial p c) ξ (j * macroCalls c + i)) (ξ (j * macroCalls c + i))‖ := by
  have hs : (path p c answer (initial p c) ξ (j * macroCalls c)).slot = 0 := by
    rw [path_slot]
    simp
  change (∃ k ≤ macroCalls c - (path p c answer (initial p c) ξ (j * macroCalls c)).slot, _) ↔ _
  rw [hs, Nat.sub_zero]
  simp only [macro_noise_prefix_eq p c Q answer g (initial p c) ξ (j * macroCalls c)]

end LongTails.Proofs.HystereticHessianConcentration
