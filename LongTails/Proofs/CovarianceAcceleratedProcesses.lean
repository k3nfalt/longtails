import LongTails.Proofs.CovarianceAcceleratedHints
import LongTails.Proofs.CovarianceAcceleratedConditionalMoments
import LongTails.Setups.CovarianceSmoothConvex

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace NNReal
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedMeasurable
open LongTails.Proofs.CovarianceAcceleratedSelection
open LongTails.Proofs.CovarianceAcceleratedConditionalMoments

namespace LongTails.Proofs.CovarianceAcceleratedProcesses

noncomputable local instance simplexMeasurableSpace (n : ℕ) : MeasurableSpace (StdSimplex ℝ (Fin n)) := borel _
local instance (n : ℕ) : BorelSpace (StdSimplex ℝ (Fin n)) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (StdSimplex ℝ (Fin n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).secondCountableTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (c : Config E n)

noncomputable def localError {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (s : State c) (ω : Ω) (u : E) : ℝ :=
  error c.x0 (c.x0 + c.a • mean c.centers s.2.2.1)
    (OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2)
    (v (query c s)) (g (query c s) ω) c.a (weight c.η (s.1 - (c.window + 1))) u

noncomputable def goodState (v : E → E) (B : ℕ → ℝ) (T : ℕ) (s : State c) : Prop :=
  c.window + 1 ≤ s.1 ∧ s.1 < c.window + 1 + T ∧
    ‖v (query c s) - OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2‖ ≤ B (s.1 - (c.window + 1))

lemma localError_measurable {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    Measurable (fun q : (State c × Ω) × E => localError c g v q.1.1 q.1.2 q.2) := by
  have hq : Measurable (fun q : (State c × Ω) × E => query c q.1.1) :=
    (measurable_query c).comp measurable_fst.fst
  have hh : Measurable (fun q : (State c × Ω) × E =>
      OracleTemplate.MultiplicativeRobustEstimator.medoid q.1.1.2.2.2) :=
    OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp (by fun_prop)
  have hm : Measurable (fun q : (State c × Ω) × E => mean c.centers q.1.1.2.2.1) :=
    (mean_continuous c.centers).measurable.comp (by fun_prop)
  have hr := hg.comp (hq.prodMk (measurable_fst.snd : Measurable (fun q : (State c × Ω) × E => q.1.2)))
  have hgrad := hv.comp hq
  unfold localError error weight
  fun_prop

lemma goodState_measurable {v : E → E} (hv : Measurable v) (B : ℕ → ℝ) (T : ℕ) :
    MeasurableSet {s : State c | goodState c v B T s} := by
  have hh : Measurable (fun s : State c => OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2) :=
    OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp (by fun_prop)
  have hB : Measurable B := measurable_of_countable B
  have hr := ((hv.comp (measurable_query c)).sub hh).norm
  have hb : Measurable (fun s : State c => B (s.1 - (c.window + 1))) := hB.comp (by fun_prop)
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter (measurableSet_le hr hb))

lemma mixture_measurable :
    Measurable (fun q : StdSimplex ℝ (Fin n) × E => mixture c.centers q.1 q.2) := by
  apply Continuous.measurable
  unfold mixture density
  fun_prop

lemma normalizer_measurable {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    Measurable (fun q : State c × Ω => ∫ u, mixture c.centers q.1.2.2.1 u *
      Real.exp (-localError c g v q.1 q.2 u) ∂stdGaussian E) := by
  have hm := (mixture_measurable c).comp
    (show Measurable (fun q : (State c × Ω) × E => (q.1.1.2.2.1, q.2)) by fun_prop)
  have hf := hm.mul (Real.measurable_exp.comp (localError_measurable c hg hv).neg)
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

lemma comparator_measurable {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (w : StdSimplex ℝ (Fin n)) :
    Measurable (fun q : State c × Ω => ∫ u, mixture c.centers w u *
      localError c g v q.1 q.2 u ∂stdGaussian E) := by
  have hm := (mixture_measurable c).comp
    (show Measurable (fun q : (State c × Ω) × E => (w, q.2)) by fun_prop)
  exact (hm.mul (localError_measurable c hg hv)).stronglyMeasurable.integral_prod_right'.measurable

noncomputable def logMassIncrement {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (B C : ℕ → ℝ) (T : ℕ) (s : State c) (ω : Ω) : ℝ := by
  classical
  exact if goodState c v B T s then
    Real.log (∫ u, mixture c.centers s.2.2.1 u * Real.exp (-localError c g v s ω u) ∂stdGaussian E) -
      C (s.1 - (c.window + 1)) else 0

noncomputable def comparatorIncrement {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (w : StdSimplex ℝ (Fin n)) (B C : ℕ → ℝ) (T : ℕ) (s : State c) (ω : Ω) : ℝ := by
  classical
  exact if goodState c v B T s then
    (∫ u, mixture c.centers w u * localError c g v s ω u ∂stdGaussian E) -
      C (s.1 - (c.window + 1)) else 0

lemma logMassIncrement_measurable {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (B C : ℕ → ℝ) (T : ℕ) :
    Measurable (Function.uncurry (logMassIncrement c g v B C T)) := by
  have hC : Measurable (fun q : State c × Ω => C (q.1.1 - (c.window + 1))) :=
    (measurable_of_countable C).comp (by fun_prop)
  exact Measurable.ite ((goodState_measurable c hv B T).preimage measurable_fst)
    ((Real.measurable_log.comp (normalizer_measurable c hg hv)).sub hC) measurable_const

lemma comparatorIncrement_measurable {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (w : StdSimplex ℝ (Fin n))
    (B C : ℕ → ℝ) (T : ℕ) :
    Measurable (Function.uncurry (comparatorIncrement c g v w B C T)) := by
  have hC : Measurable (fun q : State c × Ω => C (q.1.1 - (c.window + 1))) :=
    (measurable_of_countable C).comp (by fun_prop)
  exact Measurable.ite ((goodState_measurable c hv B T).preimage measurable_fst)
    ((comparator_measurable c hg hv w).sub hC) measurable_const

omit [BorelSpace E] in
lemma phase_localError {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (v : E → E) (t : ℕ) (u : E) :
    localError c g v (CovarianceAcceleratedRun.phase c g ξ t) (ξ (c.window + 1 + t)) u =
      -CovarianceAcceleratedRun.residual c g ξ v t u := by
  simp only [localError, CovarianceAcceleratedRun.residual, CovarianceAcceleratedRun.phase,
    CovarianceAcceleratedExecution.trajectory_clock, Nat.add_sub_cancel_left, error]
  ring

noncomputable def momentCost (R σ s : ℝ) (proxy : ℝ≥0) (t : ℕ) : ℝ :=
  320 * weight c.η t ^ 2 * R ^ 2 * s ^ 2 + 80 * weight c.η t ^ 2 * c.a ^ 2 * σ ^ 2 +
    18 * Real.exp (-1 / (32 * (proxy : ℝ)))

lemma state_moment_bounds {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : E → ℝ} {g : E → Ω → E} {σ s : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (B : ℕ → ℝ) (T : ℕ) {proxy : ℝ≥0} (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4)
    (hsmall : ∀ t < T, 2 * R * weight c.η t * B t ≤ 1 / 4)
    (hproxy : ∀ t < T, (weight c.η t * c.a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ))
    (w : StdSimplex ℝ (Fin n)) (q : State c) (hq : goodState c (gradient f) B T q) :
    (Integrable (fun ω => ∫ u, mixture c.centers q.2.2.1 u *
        Real.exp (-localError c g (gradient f) q ω u) ∂stdGaussian E) μ ∧
      (∫ ω, ∫ u, mixture c.centers q.2.2.1 u *
        Real.exp (-localError c g (gradient f) q ω u) ∂stdGaussian E ∂μ) ≤
        1 + momentCost c R σ s proxy (q.1 - (c.window + 1))) ∧
    (Integrable (fun ω => Real.exp (∫ u, mixture c.centers w u *
        localError c g (gradient f) q ω u ∂stdGaussian E)) μ ∧
      (∫ ω, Real.exp (∫ u, mixture c.centers w u *
        localError c g (gradient f) q ω u ∂stdGaussian E) ∂μ) ≤
        1 + momentCost c R σ s proxy (q.1 - (c.window + 1))) := by
  let x := query c q
  let v := gradient f x
  let h := OracleTemplate.MultiplicativeRobustEstimator.medoid q.2.2.2
  let ξ : Ω → E := fun ω => g x ω - v
  let t := q.1 - (c.window + 1)
  let α := weight c.η t
  let b := c.x0 + c.a • mean c.centers q.2.2.1
  have hξ : Measurable ξ := (ho.measurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  have hi : Integrable ξ μ := (ho.integrable x).sub (integrable_const v)
  have hm : (∫ ω, ξ ω ∂μ) = 0 := by
    rw [show ξ = (fun ω => g x ω - v) from rfl,
      integral_sub (ho.integrable x) (integrable_const v), ho.unbiased x]
    simp [v]
  have hcov (d : E) : (∫ ω, ⟪ξ ω, d⟫ ^ 2 ∂μ) ≤ s ^ 2 * ‖d‖ ^ 2 := by
    simpa only [ξ, v, real_inner_comm] using ho.covariance x d
  have hq' := hq
  dsimp only [goodState] at hq'
  have ht : t < T := by dsimp [t]; omega
  have hd := covariance_clipping_data μ hcov c.centers q.2.2.1 c.x0 (v - h)
    hR (CovarianceAcceleratedRun.weight_pos hη t).le hz ha hq'.2.2 (hsmall t ht) (hproxy t ht)
  have hW := mixture_clipping_moment μ hξ hi (ho.variance_integrable x) hm
    c.centers q.2.2.1 c.x0 b h v c.a α (-1) hd.1 (ho.variance x) hd.2.1 hd.2.2 hp0 hp1 (Or.inr rfl)
  have hU := comparator_clipping_moment μ hξ hi (ho.variance_integrable x) hm
    c.centers w c.x0 b h v c.a α hd.1 (ho.variance x) hd.2.1 hd.2.2 hp0 hp1
  have he (ω : Ω) : v + ξ ω = g x ω := by dsimp [ξ]; abel
  simp_rw [he, neg_one_mul] at hW
  simp_rw [he] at hU
  have hcost : 1 + 80 * (α ^ 2 * (4 * R ^ 2 * s ^ 2) + (α * c.a) ^ 2 * σ ^ 2) +
      18 * Real.exp (-1 / (32 * (proxy : ℝ))) = 1 + momentCost c R σ s proxy t := by
    unfold momentCost α
    ring
  rw [hcost] at hW hU
  exact ⟨hW, hU⟩

lemma normalizer_positive {Ω : Type*} (g : E → Ω → E) (v : E → E) (q : State c) (ω : Ω) :
    0 < ∫ u, mixture c.centers q.2.2.1 u * Real.exp (-localError c g v q ω u) ∂stdGaussian E := by
  simpa only [localError, neg_one_mul] using mixture_exp_error_positive c.centers q.2.2.1 c.x0
    (c.x0 + c.a • mean c.centers q.2.2.1) (OracleTemplate.MultiplicativeRobustEstimator.medoid q.2.2.2)
    (v (query c q)) (g (query c q) ω) c.a (weight c.η (q.1 - (c.window + 1))) (-1)

lemma increments_exp_control {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : E → ℝ} {g : E → Ω → E} {σ s : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (B : ℕ → ℝ) (T : ℕ) {proxy : ℝ≥0} (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4)
    (hsmall : ∀ t < T, 2 * R * weight c.η t * B t ≤ 1 / 4)
    (hproxy : ∀ t < T, (weight c.η t * c.a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ))
    (w : StdSimplex ℝ (Fin n)) (q : State c) :
    (Integrable (fun ω => Real.exp (logMassIncrement c g (gradient f) B (momentCost c R σ s proxy) T q ω)) μ ∧
      (∫ ω, Real.exp (logMassIncrement c g (gradient f) B (momentCost c R σ s proxy) T q ω) ∂μ) ≤ 1) ∧
    (Integrable (fun ω => Real.exp (comparatorIncrement c g (gradient f) w B (momentCost c R σ s proxy) T q ω)) μ ∧
      (∫ ω, Real.exp (comparatorIncrement c g (gradient f) w B (momentCost c R σ s proxy) T q ω) ∂μ) ≤ 1) := by
  classical
  by_cases hq : goodState c (gradient f) B T q
  · have hb := state_moment_bounds c μ ho hη hR hz ha B T hp0 hp1 hsmall hproxy w q hq
    have he : (fun ω => Real.exp (Real.log (∫ u, mixture c.centers q.2.2.1 u *
        Real.exp (-localError c g (gradient f) q ω u) ∂stdGaussian E))) =ᵐ[μ]
        (fun ω => ∫ u, mixture c.centers q.2.2.1 u *
          Real.exp (-localError c g (gradient f) q ω u) ∂stdGaussian E) :=
      Filter.Eventually.of_forall fun ω => Real.exp_log (normalizer_positive c g (gradient f) q ω)
    have hiLog := hb.1.1.congr he.symm
    have hbLog := (integral_congr_ae he).trans_le hb.1.2
    simp only [logMassIncrement, comparatorIncrement, ite_eq_left hq]
    exact ⟨CovarianceAcceleratedConcentration.compensated_exp_control hiLog hbLog,
      CovarianceAcceleratedConcentration.compensated_exp_control hb.2.1 hb.2.2⟩
  · simp [logMassIncrement, comparatorIncrement, hq]

lemma increments_tails {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    {f : E → ℝ} {g : E → Ω → E} {σ s : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hv : Measurable (gradient f)) (hη : 0 < c.η) (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (B : ℕ → ℝ) (T : ℕ) {proxy : ℝ≥0} (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4)
    (hsmall : ∀ t < T, 2 * R * weight c.η t * B t ≤ 1 / 4)
    (hproxy : ∀ t < T, (weight c.η t * c.a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ))
    (w : StdSimplex ℝ (Fin n)) (ell : ℝ) :
    (P {ω | ell ≤ ∑ i ∈ Finset.range (c.window + 1 + T),
      logMassIncrement c g (gradient f) B (momentCost c R σ s proxy) T
        (trajectory c g (fun j => ξ j ω) i) (ξ i ω)} ≤ ENNReal.ofReal (Real.exp (-ell))) ∧
    (P {ω | ell ≤ ∑ i ∈ Finset.range (c.window + 1 + T),
      comparatorIncrement c g (gradient f) w B (momentCost c R σ s proxy) T
        (trajectory c g (fun j => ξ j ω) i) (ξ i ω)} ≤ ENNReal.ofReal (Real.exp (-ell))) := by
  have hn := CovarianceAcceleratedHints.measurable_next c ho.measurable hβ hγ hM hz
  have hb (q : State c) := increments_exp_control c μ ho hη hR hz ha B T hp0 hp1 hsmall hproxy w q
  constructor
  · have ht := CovarianceAcceleratedConcentration.iid_exponential_tail hsamples hn
      (logMassIncrement_measurable c ho.measurable hv B (momentCost c R σ s proxy) T)
      (fun q => (hb q).1.1) (fun q => (hb q).1.2) (c.window + 1 + T) (initial c) ell
    simpa only [CovarianceAcceleratedHints.stateAt_trajectory] using ht
  · have ht := CovarianceAcceleratedConcentration.iid_exponential_tail hsamples hn
      (comparatorIncrement_measurable c ho.measurable hv w B (momentCost c R σ s proxy) T)
      (fun q => (hb q).2.1) (fun q => (hb q).2.2) (c.window + 1 + T) (initial c) ell
    simpa only [CovarianceAcceleratedHints.stateAt_trajectory] using ht

omit [BorelSpace E] in
lemma logMass_sum_of_good {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (v : E → E)
    (B C : ℕ → ℝ) (T : ℕ)
    (hgood : ∀ t < T, goodState c v B T (CovarianceAcceleratedRun.phase c g ξ t)) :
    (∑ i ∈ Finset.range (c.window + 1 + T), logMassIncrement c g v B C T (trajectory c g ξ i) (ξ i)) =
      (∑ t ∈ Finset.range T, Real.log (∫ u, mixture c.centers (CovarianceAcceleratedRun.phase c g ξ t).2.2.1 u *
        Real.exp (CovarianceAcceleratedRun.residual c g ξ v t u) ∂stdGaussian E)) -
      ∑ t ∈ Finset.range T, C t := by
  classical
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (c.window + 1), logMassIncrement c g v B C T (trajectory c g ξ i) (ξ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ¬c.window + 1 ≤ i := Nat.not_le_of_gt (Finset.mem_range.mp hi)
    simp [logMassIncrement, goodState, CovarianceAcceleratedExecution.trajectory_clock, hn]
  rw [hz, zero_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  change logMassIncrement c g v B C T (CovarianceAcceleratedRun.phase c g ξ t) (ξ (c.window + 1 + t)) = _
  have hc : (CovarianceAcceleratedRun.phase c g ξ t).1 - (c.window + 1) = t := by
    simp only [CovarianceAcceleratedRun.phase, CovarianceAcceleratedExecution.trajectory_clock, Nat.add_sub_cancel_left]
  rw [logMassIncrement, ite_eq_left (hgood t (Finset.mem_range.mp ht)), hc]
  simp_rw [phase_localError, neg_neg]

omit [BorelSpace E] in
lemma comparator_sum_of_good {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (v : E → E)
    (w : StdSimplex ℝ (Fin n)) (B C : ℕ → ℝ) (T : ℕ)
    (hgood : ∀ t < T, goodState c v B T (CovarianceAcceleratedRun.phase c g ξ t)) :
    (∑ i ∈ Finset.range (c.window + 1 + T), comparatorIncrement c g v w B C T (trajectory c g ξ i) (ξ i)) =
      -(∑ t ∈ Finset.range T, ∫ u, mixture c.centers w u *
        CovarianceAcceleratedRun.residual c g ξ v t u ∂stdGaussian E) -
      ∑ t ∈ Finset.range T, C t := by
  classical
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (c.window + 1), comparatorIncrement c g v w B C T (trajectory c g ξ i) (ξ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ¬c.window + 1 ≤ i := Nat.not_le_of_gt (Finset.mem_range.mp hi)
    simp [comparatorIncrement, goodState, CovarianceAcceleratedExecution.trajectory_clock, hn]
  rw [hz, zero_add, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  change comparatorIncrement c g v w B C T (CovarianceAcceleratedRun.phase c g ξ t) (ξ (c.window + 1 + t)) = _
  have hc : (CovarianceAcceleratedRun.phase c g ξ t).1 - (c.window + 1) = t := by
    simp only [CovarianceAcceleratedRun.phase, CovarianceAcceleratedExecution.trajectory_clock, Nat.add_sub_cancel_left]
  rw [comparatorIncrement, ite_eq_left (hgood t (Finset.mem_range.mp ht)), hc]
  simp_rw [phase_localError, mul_neg, integral_neg]

end LongTails.Proofs.CovarianceAcceleratedProcesses
