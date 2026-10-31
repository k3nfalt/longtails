import LongTails.Proofs.ValidatedMuonExecution
import LongTails.Proofs.MatrixPolarGeometry
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.MatrixOracleMoments
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import LongTails.Setups.FiniteVarianceSpectralSmooth
import LongTails.Proofs.MatrixCovariance

namespace LongTails.Proofs.MuonProcess

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon
open LongTails.Algorithms.MatrixPolar

lemma measurable_trainingStep {m n : ℕ} (α η : ℝ) :
    Measurable (fun p : (Space m n × Space m n) × Space m n =>
      trainingStep α η p.1 p.2) := by
  have hM : Measurable (fun p : (Space m n × Space m n) × Space m n =>
      (1 - α) • p.1.2 + α • p.2) :=
    (measurable_fst.snd.const_smul (1 - α)).add (measurable_snd.const_smul α)
  exact (measurable_fst.fst.sub (((measurable_polar m n).comp hM).const_smul η)).prodMk hM

lemma measurable_trajectory {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (α η : ℝ) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g))
    (state : Space m n × Space m n) (call t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => trajectory α η g ξ state call t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (measurable_trainingStep α η).comp
      (ih.prodMk (hg.comp (ih.fst.prodMk (measurable_pi_apply (call + t)))))

abbrev past {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) : MeasurableSpace (ℕ → Ω) :=
  MeasurableSpace.comap (fun ξ (i : Fin t) => ξ i) inferInstance

lemma measurable_prefix {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) :
    @Measurable (ℕ → Ω) (Fin t → Ω) (past t) inferInstance (fun ξ i => ξ i) :=
  comap_measurable _

lemma measurable_eval_past {Ω : Type*} [MeasurableSpace Ω] {k t : ℕ} (h : k < t) :
    @Measurable (ℕ → Ω) Ω (past t) inferInstance (fun ξ => ξ k) :=
  (measurable_pi_apply (⟨k, h⟩ : Fin t)).comp (measurable_prefix t)

lemma past_mono {Ω : Type*} [MeasurableSpace Ω] {s t : ℕ} (h : s ≤ t) :
    past (Ω := Ω) s ≤ past t := by
  let : MeasurableSpace (ℕ → Ω) := past t
  exact (Measurable.of_eval fun i : Fin s =>
    measurable_eval_past (i.isLt.trans_le h)).comap_le

lemma past_le {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) :
    past (Ω := Ω) t ≤ (inferInstance : MeasurableSpace (ℕ → Ω)) :=
  (Measurable.of_eval fun i : Fin t => measurable_pi_apply i.val).comap_le

lemma adapted_trajectory {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (α η : ℝ) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g))
    (state : Space m n × Space m n) (call t : ℕ) :
    @Measurable (ℕ → Ω) (Space m n × Space m n) (past (call + t)) inferInstance
      (fun ξ => trajectory α η g ξ state call t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ih' := ih.mono (past_mono (show call + t ≤ call + (t + 1) by omega)) le_rfl
    exact (measurable_trainingStep α η).comp
      (ih'.prodMk (hg.comp (ih'.fst.prodMk (measurable_eval_past (by omega)))))

lemma pair_local_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ξ A B : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace A] [MeasurableSpace B] {P : Measure Ξ}
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {X : Ξ → A} {Y : Ξ → B}
    (hpair : MeasurePreserving (fun ω => (X ω, Y ω)) P (μ.prod ν))
    {F : A × B → E} (hF : Integrable F (μ.prod ν))
    {C : Set A} (hC : MeasurableSet C) :
    (∫ ω in X ⁻¹' C, F (X ω, Y ω) ∂P) =
      ∫ a in C, ∫ b, F (a, b) ∂ν ∂μ := by
  let H : A × B → E := (Prod.fst ⁻¹' C).indicator F
  have hH : Integrable H (μ.prod ν) := hF.indicator (hC.preimage measurable_fst)
  have heq : (fun ω => (X ⁻¹' C).indicator (fun ω => F (X ω, Y ω)) ω) =
      H ∘ (fun ω => (X ω, Y ω)) := by
    funext ω
    by_cases h : X ω ∈ C <;> simp [H, h]
  rw [← integral_indicator (hC.preimage hpair.measurable.fst), heq]
  change (∫ ω, H (X ω, Y ω) ∂P) = _
  have hmap := integral_map hpair.measurable.aemeasurable
    (show AEStronglyMeasurable H (P.map (fun ω => (X ω, Y ω))) by
      rw [hpair.map_eq]
      exact hH.aestronglyMeasurable)
  rw [hpair.map_eq] at hmap
  rw [← hmap, integral_prod _ hH, ← integral_indicator hC]
  apply integral_congr_ae
  filter_upwards [] with a
  by_cases ha : a ∈ C <;> simp [H, ha]

lemma pair_conditional_le {Ξ A B : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace A] [MeasurableSpace B] {P : Measure Ξ} [IsFiniteMeasure P]
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {X : Ξ → A} {Y : Ξ → B}
    (hpair : MeasurePreserving (fun ω => (X ω, Y ω)) P (μ.prod ν))
    {F : A × B → ℝ} (hF : Integrable F (μ.prod ν)) {c : ℝ}
    (hmean : ∀ a, (∫ b, F (a, b) ∂ν) ≤ c) :
    ∀ᵐ ω ∂P, P[(fun ω => F (X ω, Y ω)) |
      MeasurableSpace.comap X inferInstance] ω ≤ c := by
  have hm := hpair.measurable.fst.comap_le
  apply MatrixOracleMoments.conditional_le_of_local_integrals hm
    (hpair.integrable_comp_of_integrable hF)
  intro C hC
  obtain ⟨D, hD, rfl⟩ := hC
  change (∫ ω in X ⁻¹' D, F (X ω, Y ω) ∂P) ≤ c * P.real (X ⁻¹' D)
  rw [pair_local_integral hpair hF hD]
  have hmap : MeasurePreserving X P μ :=
    measurePreserving_fst.comp hpair
  have hmass : P.real (X ⁻¹' D) = μ.real D := by
    rw [measureReal_def, measureReal_def, hmap.measure_preimage hD.nullMeasurableSet]
  rw [hmass, mul_comm c, ← smul_eq_mul, ← setIntegral_const]
  exact integral_mono_ae hF.integral_prod_left.integrableOn
    (integrable_const c) (Filter.Eventually.of_forall hmean)

lemma pair_conditional_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ξ A B : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace A] [MeasurableSpace B] {P : Measure Ξ} [IsFiniteMeasure P]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {X : Ξ → A} {Y : Ξ → B}
    (hpair : MeasurePreserving (fun ω => (X ω, Y ω)) P (μ.prod ν))
    {F : A × B → E} (hF : Integrable F (μ.prod ν))
    (hmean : ∀ a, (∫ b, F (a, b) ∂ν) = 0) :
    P[(fun ω => F (X ω, Y ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[P] 0 := by
  have hm := hpair.measurable.fst.comap_le
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm
    (hpair.integrable_comp_of_integrable hF)
    (fun _ _ _ => integrable_const (0 : E)) ?_ stronglyMeasurable_const.aestronglyMeasurable
  intro C hC _
  obtain ⟨D, hD, rfl⟩ := hC
  change (∫ _ in X ⁻¹' D, (0 : E) ∂P) = ∫ ω in X ⁻¹' D, F (X ω, Y ω) ∂P
  rw [pair_local_integral hpair hF hD]
  simp only [hmean, integral_zero]

lemma kernel_integrable_nonneg {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [SFinite ν]
    {F : A × B → ℝ} (hF : Measurable F) (hpos : ∀ z, 0 ≤ F z)
    (hint : ∀ a, Integrable (fun b => F (a, b)) ν) {c : ℝ}
    (hbound : ∀ a, (∫ b, F (a, b) ∂ν) ≤ c) : Integrable F (μ.prod ν) := by
  have houter : Integrable (fun a => ∫ b, ‖F (a, b)‖ ∂ν) μ := by
    apply Integrable.of_bound
      hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable c
    exact Filter.Eventually.of_forall fun a => by
      simp_rw [Real.norm_of_nonneg (hpos _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun b => hpos (a, b))]
      exact hbound a
  exact (integrable_prod_iff hF.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall hint, houter⟩

lemma kernel_memLp_two {E A B : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [SFinite ν]
    {F : A × B → E} (hF : Measurable F)
    (hrows : ∀ a, MemLp (fun b => F (a, b)) 2 ν) {c : ℝ}
    (hbound : ∀ a, (∫ b, ‖F (a, b)‖ ^ 2 ∂ν) ≤ c) : MemLp F 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).2
  exact kernel_integrable_nonneg (hF.norm.pow_const 2) (fun _ => sq_nonneg _)
    (fun a => (hrows a).norm.integrable_sq) hbound

lemma iid_prefix_next {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P) (t : ℕ) :
    MeasurePreserving (fun ξ => ((fun i : Fin t => ξ i), ξ t)) P
      ((Measure.pi fun _ : Fin t => p).prod p) := by
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin t => p)).prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => p) 0)).comp (h.prefix_tail_law t)
  simpa only [Function.comp_def, Prod.map_apply, id_eq, Function.eval, Nat.add_zero] using hp

lemma adaptive_kernel_moments {E S Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S] [MeasurableSpace Ω]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P) (t : ℕ)
    {X : (ℕ → Ω) → S} (hX : Measurable[past t] X)
    {F : S → Ω → E} (hF : Measurable (Function.uncurry F))
    (hrows : ∀ x, MemLp (F x) 2 p) (hmean : ∀ x, (∫ ω, F x ω ∂p) = 0)
    {c : ℝ} (hbound : ∀ x, (∫ ω, ‖F x ω‖ ^ 2 ∂p) ≤ c) :
    MemLp (fun ξ => F (X ξ) (ξ t)) 2 P ∧
    P[(fun ξ => F (X ξ) (ξ t)) | past t] =ᵐ[P] 0 ∧
    ∀ᵐ ξ ∂P, P[(fun ξ => ‖F (X ξ) (ξ t)‖ ^ 2) | past t] ξ ≤ c := by
  obtain ⟨θ, hθ, heq⟩ := hX.exists_eq_measurable_comp
  let K : (Fin t → Ω) × Ω → E := fun z => F (θ z.1) z.2
  have hK : Measurable K := hF.comp ((hθ.comp measurable_fst).prodMk measurable_snd)
  have hKl : MemLp K 2 ((Measure.pi fun _ : Fin t => p).prod p) :=
    kernel_memLp_two hK (fun a => hrows (θ a)) (fun a => hbound (θ a))
  have hp := iid_prefix_next h t
  constructor
  · simpa only [K, heq, Function.comp_def] using hKl.comp_measurePreserving hp
  constructor
  · simpa only [K, heq, Function.comp_def] using
      pair_conditional_zero hp (hKl.integrable (by norm_num)) (fun a => hmean (θ a))
  · simpa only [K, heq, Function.comp_def] using
      pair_conditional_le hp hKl.norm.integrable_sq (fun a => hbound (θ a))

noncomputable def rowMap {m n : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    Space m n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (operatorEquiv m n X).adjoint v
      map_add' := by intros; simp
      map_smul' := by intros; simp }

lemma measurable_gradient {m n : ℕ} (f : Space m n → ℝ) :
    Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space m n)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

lemma model_row_mean {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    (x : Space m n) (v : EuclideanSpace ℝ (Fin m)) :
    (∫ ω, rowMap v (model.sample x ω - gradient f x) ∂(model.law : Measure _)) = 0 := by
  have hi : Integrable (fun ω => model.sample x ω - gradient f x) (model.law : Measure _) :=
    (model.integrable x).sub (integrable_const (gradient f x))
  rw [(rowMap v).integral_comp_comm hi,
    integral_sub (model.integrable x) (integrable_const (gradient f x)), model.unbiased]
  simp

lemma model_adaptive_row_moments {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P) (t : ℕ)
    {X : (ℕ → model.Ω) → Space m n} (hX : Measurable[past t] X)
    (v : EuclideanSpace ℝ (Fin m)) {c : ℝ}
    (hrows : ∀ x, MemLp (fun ω => rowMap v (model.sample x ω - gradient f x)) 2
      (model.law : Measure _))
    (hbound : ∀ x, (∫ ω, ‖rowMap v (model.sample x ω - gradient f x)‖ ^ 2
      ∂(model.law : Measure _)) ≤ c) :
    MemLp (fun ξ => rowMap v (model.sample (X ξ) (ξ t) - gradient f (X ξ))) 2 P ∧
    P[(fun ξ => rowMap v (model.sample (X ξ) (ξ t) - gradient f (X ξ))) | past t] =ᵐ[P] 0 ∧
    ∀ᵐ ξ ∂P, P[(fun ξ => ‖rowMap v (model.sample (X ξ) (ξ t) - gradient f (X ξ))‖ ^ 2)
      | past t] ξ ≤ c := by
  exact adaptive_kernel_moments (F := fun x ω => rowMap v (model.sample x ω - gradient f x)) h t hX
    ((rowMap v).continuous.measurable.comp
      (model.jointly_measurable.sub ((measurable_gradient f).comp measurable_fst)))
    hrows (fun x => model_row_mean model x v) hbound

lemma measurable_adaptive_noise {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    (t : ℕ) {X : (ℕ → model.Ω) → Space m n} (hX : Measurable[past t] X) :
    Measurable[past (t + 1)]
      (fun ξ => model.sample (X ξ) (ξ t) - gradient f (X ξ)) := by
  have hx := hX.mono (past_mono (Nat.le_succ t)) le_rfl
  exact (model.jointly_measurable.comp
    (hx.prodMk (measurable_eval_past (Nat.lt_succ_self t)))).sub
      ((measurable_gradient f).comp hx)

lemma model_weighted_noise_bounds {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {X : ℕ → (ℕ → model.Ω) → Space m n} (hX : ∀ t, Measurable[past t] (X t))
    (start T : ℕ) (w : ℕ → ℝ) :
    let V := fun ξ => nuclearNorm (∑ j ∈ Finset.range T, w j •
      (model.sample (X (start + j) ξ) (ξ (start + j)) - gradient f (X (start + j) ξ)))
    MemLp V 2 P ∧ (∫ ξ, V ξ ^ 2 ∂P) ≤ (∑ j ∈ Finset.range T, w j ^ 2) * s ^ 2 ∧
      (∀ᵐ ξ ∂P, P[(fun ξ => V ξ ^ 2) | past start] ξ ≤
        (∑ j ∈ Finset.range T, w j ^ 2) * s ^ 2) ∧
      ∀ᵐ ξ ∂P, P[V | past start] ξ ≤ Real.sqrt (∑ j ∈ Finset.range T, w j ^ 2) * s := by
  obtain ⟨b, σ, hσ, hsum, hprofile⟩ := model.row_profile
  let N := fun t ξ => model.sample (X (start + t) ξ) (ξ (start + t)) -
    gradient f (X (start + t) ξ)
  have hmom (t : ℕ) (i : Fin m) := model_adaptive_row_moments model h (start + t)
    (hX (start + t)) (b i) (fun x => (hprofile x i).1) (fun x => (hprofile x i).2)
  have hn (t : ℕ) : Measurable[past (start + t + 1)] (N t) :=
    measurable_adaptive_noise model (start + t) (hX (start + t))
  have hadapt (t : ℕ) (i : Fin m) : StronglyMeasurable[past (start + (t + 1))]
      (fun ξ => (operatorEquiv m n (N t ξ)).adjoint (b i)) := by
    have hh := ((rowMap (b i)).continuous.measurable.comp (hn t)).stronglyMeasurable
    rw [Nat.add_assoc] at hh
    exact hh
  have hsecond (t : ℕ) (i : Fin m) :
      (∫ ξ, ‖(operatorEquiv m n (N t ξ)).adjoint (b i)‖ ^ 2 ∂P) ≤ σ i ^ 2 := by
    have hh := MatrixOracleMoments.local_integral_le_of_conditional_bound (past_le (start + t))
      (hmom t i).1.norm.integrable_sq (hmom t i).2.2 MeasurableSet.univ
    change (∫ ξ in Set.univ, ‖(operatorEquiv m n (N t ξ)).adjoint (b i)‖ ^ 2 ∂P) ≤
      σ i ^ 2 * P.real Set.univ at hh
    simpa using hh
  have hv := MatrixCovariance.weighted_row_martingale_second_moment (P := P) b
    (F := fun t => past (start + t)) (fun t => past_le (start + t))
    (fun _ _ ht => past_mono (Nat.add_le_add_left ht start))
    (N := N) (fun t => (hn t).mono (past_le _) le_rfl) hσ
    (fun t i => (hmom t i).1) hadapt (fun t i => (hmom t i).2.1) hsecond w T
  have hc := MatrixCovariance.conditional_weighted_row_second_moment (P := P) b
    (F := fun t => past (start + t)) (fun t => past_le (start + t))
    (fun _ _ ht => past_mono (Nat.add_le_add_left ht start))
    (N := N) (fun t => (hn t).mono (past_le _) le_rfl) hσ
    (fun t i => (hmom t i).1) hadapt (fun t i => (hmom t i).2.1)
    (fun A hA t i => MatrixOracleMoments.local_integral_le_of_conditional_bound
      (past_le (start + t)) (hmom t i).1.norm.integrable_sq (hmom t i).2.2
      (past_mono (Nat.add_le_add_left (Nat.zero_le t) start) _ hA)) w T
  have hh := MatrixCovariance.conditional_weighted_row_mean (P := P) b
    (F := fun t => past (start + t)) (fun t => past_le (start + t))
    (fun _ _ ht => past_mono (Nat.add_le_add_left ht start))
    (N := N) (fun t => (hn t).mono (past_le _) le_rfl) hσ
    (fun t i => (hmom t i).1) hadapt
    (fun t i => (hmom t i).2.1) (fun t i => (hmom t i).2.2) w T
  have hscale : (∑ j ∈ Finset.range T, w j ^ 2) * (∑ i, σ i) ^ 2 ≤
      (∑ j ∈ Finset.range T, w j ^ 2) * s ^ 2 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hσ i)) hsum 2)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  refine ⟨hv.1, hv.2.trans hscale, ?_, ?_⟩
  · filter_upwards [hc] with ξ hξ
    exact hξ.trans hscale
  · filter_upwards [hh] with ξ hξ
    exact hξ.trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))

lemma measurable_batch_mean {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {X : (ℕ → model.Ω) → Space m n} (hX : Measurable X) (start b : ℕ) :
    Measurable (fun ξ => QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start) := by
  simp_rw [ValidatedMuonExecution.sampledEval_batchMeanPlan]
  exact (Finset.measurable_sum (Finset.range b) (fun j _ => model.jointly_measurable.comp
    (hX.prodMk (measurable_pi_apply (start + j))))).const_smul (1 / (b : ℝ))

lemma measurable_batch_error {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {X : (ℕ → model.Ω) → Space m n} (hX : Measurable X) (start b : ℕ) :
    Measurable (fun ξ => nuclearNorm
      (QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start - gradient f (X ξ))) := by
  exact (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
    ((measurable_batch_mean model hX start b).sub ((measurable_gradient f).comp hX))

lemma adapted_batch_error {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {X : (ℕ → model.Ω) → Space m n} {start : ℕ}
    (hX : Measurable[past start] X) (b : ℕ) :
    Measurable[past (start + b)] (fun ξ => nuclearNorm
      (QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start - gradient f (X ξ))) := by
  have hx := hX.mono (past_mono (Nat.le_add_right start b)) le_rfl
  simp_rw [ValidatedMuonExecution.sampledEval_batchMeanPlan]
  exact (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
    (((Finset.measurable_sum (Finset.range b) (fun j hj => model.jointly_measurable.comp
      (hx.prodMk (measurable_eval_past (Nat.add_lt_add_left (Finset.mem_range.mp hj) start))))).const_smul (1 / (b : ℝ))).sub ((measurable_gradient f).comp hx))

lemma model_frozen_batch_bounds {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {start b : ℕ} (hb : 0 < b) {X : (ℕ → model.Ω) → Space m n}
    (hX : Measurable[past start] X) :
    let V := fun ξ => nuclearNorm
      (QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start - gradient f (X ξ))
    MemLp V 2 P ∧ ∀ᵐ ξ ∂P, P[(fun ξ => V ξ ^ 2) | past start] ξ ≤ s ^ 2 / b := by
  classical
  let Q := fun j ξ => if start ≤ j then X ξ else (0 : Space m n)
  have hQ (j : ℕ) : Measurable[past j] (Q j) := by
    by_cases hj : start ≤ j
    · simpa only [Q, ite_eq_left hj] using hX.mono (past_mono hj) le_rfl
    · simpa only [Q, ite_eq_right hj] using
        (measurable_const : Measurable[past j] (fun _ : ℕ → model.Ω => (0 : Space m n)))
  have hh := model_weighted_noise_bounds model h hQ start b (fun _ => 1 / (b : ℝ))
  have hw : (∑ _j ∈ Finset.range b, (1 / (b : ℝ)) ^ 2) = 1 / (b : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
    field_simp
  have he (ξ : ℕ → model.Ω) :
      nuclearNorm (QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start -
        gradient f (X ξ)) =
      nuclearNorm (∑ j ∈ Finset.range b, (1 / (b : ℝ)) •
        (model.sample (Q (start + j) ξ) (ξ (start + j)) - gradient f (Q (start + j) ξ))) := by
    rw [ValidatedMuonExecution.sampledEval_batchMean_centered _ _ _ _ hb]
    simp only [Q, Nat.le_add_right, ite_true]
  simp only [hw] at hh
  constructor
  · simpa only [he] using hh.1
  · have hcoef : (1 / (b : ℝ)) * s ^ 2 = s ^ 2 / b := by ring
    simpa only [he, hcoef] using hh.2.2.1

lemma conditional_affine_bound {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ m₀)
    {Z W : Ω → ℝ} (hZ : Integrable Z P) (hW : Integrable W P)
    {a b c : ℝ} (hb : 0 ≤ b) (hpoint : ∀ ω, Z ω ≤ a + b * W ω)
    (hmean : ∀ᵐ ω ∂P, P[W | m] ω ≤ c) :
    ∀ᵐ ω ∂P, P[Z | m] ω ≤ a + b * c := by
  apply MatrixOracleMoments.conditional_le_of_local_integrals hm hZ
  intro A hA
  have hw := MatrixOracleMoments.local_integral_le_of_conditional_bound hm hW hmean hA
  calc
    (∫ ω in A, Z ω ∂P) ≤ ∫ ω in A, a + b * W ω ∂P :=
      integral_mono hZ.integrableOn ((integrable_const a).add (hW.integrableOn.const_mul b)) hpoint
    _ = a * P.real A + b * (∫ ω in A, W ω ∂P) := by
      rw [integral_add (integrable_const a) (hW.integrableOn.const_mul b),
        integral_const_mul, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ a * P.real A + b * (c * P.real A) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hw hb)
    _ = (a + b * c) * P.real A := by ring

lemma conditional_square_markov {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ m₀)
    {Y : Ω → ℝ} (hY : Measurable Y) (hY2 : MemLp Y 2 P)
    {r c : ℝ} (hr : 0 < r)
    (hmean : ∀ᵐ ω ∂P, P[(fun ω => Y ω ^ 2) | m] ω ≤ c) :
    ∀ᵐ ω ∂P, P[(fun ω => if r < Y ω then (1 : ℝ) else 0) | m] ω ≤ c / r ^ 2 := by
  classical
  let Z := fun ω => if r < Y ω then (1 : ℝ) else 0
  have hZ : Measurable Z := Measurable.ite
    (measurableSet_lt measurable_const hY) measurable_const measurable_const
  have hiZ : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by dsimp [Z]; split_ifs <;> norm_num)
  have hp (ω : Ω) : Z ω ≤ 0 + (1 / r ^ 2) * Y ω ^ 2 := by
    dsimp [Z]
    split_ifs with h
    · have hs : r ^ 2 ≤ Y ω ^ 2 := by nlinarith
      have hh := (one_le_div₀ (sq_pos_of_pos hr)).2 hs
      simpa only [zero_add, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
    · positivity
  have hh := conditional_affine_bound hm hiZ hY2.integrable_sq (by positivity) hp hmean
  simpa only [Z, zero_add, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh

lemma model_frozen_batch_bad_mean {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {start b : ℕ} (hb : 0 < b) {X : (ℕ → model.Ω) → Space m n}
    (hX : Measurable[past start] X) {r : ℝ} (hr : 0 < r)
    (hbudget : 16 * s ^ 2 ≤ (b : ℝ) * r ^ 2) :
    ∀ᵐ ξ ∂P, P[(fun ξ => if r < nuclearNorm
      (QueryPlan.sampledEval model.sample ξ (batchMeanPlan (X ξ) b) start - gradient f (X ξ))
      then (1 : ℝ) else 0) | past start] ξ ≤ (1 / 16 : ℝ) := by
  have hv := model_frozen_batch_bounds model h hb hX
  have hc := conditional_square_markov (past_le start)
    (measurable_batch_error model (hX.mono (past_le start) le_rfl) start b) hv.1 hr hv.2
  filter_upwards [hc] with ξ hξ
  refine hξ.trans ?_
  rw [div_div]
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast hb) (sq_pos_of_pos hr))).2
  nlinarith

lemma coordinateIID_map {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure p]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : ℕ → Ω) => ω k) p (P.map (fun ω k => ξ k ω)) := by
  rw [h.stream_law.map_eq]
  exact OracleTemplate.StochasticGeneralized.infinitePi_iid p

lemma model_single_noise_bounds {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {X : ℕ → (ℕ → model.Ω) → Space m n} (hX : ∀ t, Measurable[past t] (X t)) (t : ℕ) :
    let Y := fun ξ => nuclearNorm (model.sample (X t ξ) (ξ t) - gradient f (X t ξ))
    MemLp Y 2 P ∧ (∫ ξ, Y ξ ^ 2 ∂P) ≤ s ^ 2 := by
  have hh := model_weighted_noise_bounds model h hX t 1 (fun _ => 1)
  simpa using And.intro hh.1 hh.2.1

lemma square_moment_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) {R v : ℝ}
    (hR : 0 < R) (hv : (∫ ξ, Y ξ ^ 2 ∂P) ≤ v) :
    P.real {ξ | R < Y ξ} ≤ v / R ^ 2 := by
  have hi : Integrable (fun ξ => Y ξ ^ 2) P := by
    simpa only [Real.norm_eq_abs, sq_abs] using hY.norm.integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ξ => sq_nonneg (Y ξ)) hi (R ^ 2)
  have hp : P.real {ξ | R < Y ξ} ≤ P.real {ξ | R ^ 2 ≤ Y ξ ^ 2} := by
    apply measureReal_mono (μ := P) ?_ (by finiteness)
    intro ξ hξ
    change R < Y ξ at hξ
    change R ^ 2 ≤ Y ξ ^ 2
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg R)
  nlinarith

lemma zero_square_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hv : (∫ ξ, Y ξ ^ 2 ∂P) ≤ 0) : ∀ᵐ ξ ∂P, Y ξ = 0 := by
  have hi : Integrable (fun ξ => Y ξ ^ 2) P := by
    simpa only [Real.norm_eq_abs, sq_abs] using hY.norm.integrable_sq
  have he : (∫ ξ, Y ξ ^ 2 ∂P) = 0 :=
    le_antisymm hv (integral_nonneg fun ξ => sq_nonneg (Y ξ))
  have hz := (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg (Y ξ)) hi).mp he
  filter_upwards [hz] with ξ hξ
  exact (sq_eq_zero_iff).mp hξ

lemma finite_square_moment_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {R v : ℝ} (hR : 0 < R)
    (hY : ∀ t, MemLp (Y t) 2 P) (hv : ∀ t, (∫ ξ, Y t ξ ^ 2 ∂P) ≤ v) (T : ℕ) :
    P.real {ξ | ∃ t < T, R < Y t ξ} ≤ T * (v / R ^ 2) := by
  have he : {ξ | ∃ t < T, R < Y t ξ} =
      ⋃ t ∈ Finset.range T, {ξ | R < Y t ξ} := by
    ext ξ
    simp
  rw [he]
  calc
    _ ≤ ∑ t ∈ Finset.range T, P.real {ξ | R < Y t ξ} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range T, v / R ^ 2 :=
      Finset.sum_le_sum (fun t _ => square_moment_tail (hY t) hR (hv t))
    _ = _ := by simp

lemma model_noise_max_tail {m n : ℕ} {f : Space m n → ℝ} {s : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {X : ℕ → (ℕ → model.Ω) → Space m n} (hX : ∀ t, Measurable[past t] (X t))
    (hs : 0 ≤ s) {γ : ℝ} (hγ : 0 < γ) {T : ℕ} (hT : 0 < T) :
    P.real {ξ | ∃ t < T, s * Real.sqrt (2 * (T : ℝ) / γ) <
      nuclearNorm (model.sample (X t ξ) (ξ t) - gradient f (X t ξ))} ≤ γ / 2 := by
  let Y := fun t ξ => nuclearNorm (model.sample (X t ξ) (ξ t) - gradient f (X t ξ))
  have hm (t : ℕ) := model_single_noise_bounds model h hX t
  change P.real {ξ | ∃ t < T, s * Real.sqrt (2 * (T : ℝ) / γ) < Y t ξ} ≤ γ / 2
  by_cases hs0 : s = 0
  · have hz : ∀ᵐ ξ ∂P, ∀ t, Y t ξ = 0 := by
      apply ae_all_iff.mpr
      intro t
      exact zero_square_moment (hm t).1 (by simpa only [hs0, sq, zero_mul] using (hm t).2)
    have hn : ∀ᵐ ξ ∂P, ¬∃ t < T, s * Real.sqrt (2 * (T : ℝ) / γ) < Y t ξ := by
      filter_upwards [hz] with ξ hξ
      simp [hs0, hξ]
    have he : P {ξ | ∃ t < T, s * Real.sqrt (2 * (T : ℝ) / γ) < Y t ξ} = 0 := by
      simpa only [not_not] using ae_iff.mp hn
    rw [measureReal_def, he, ENNReal.toReal_zero]
    positivity
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hTp : 0 < (T : ℝ) := by exact_mod_cast hT
    have harg : 0 < 2 * (T : ℝ) / γ := by positivity
    have hR : 0 < s * Real.sqrt (2 * (T : ℝ) / γ) :=
      mul_pos hsp (Real.sqrt_pos.mpr harg)
    calc
      _ ≤ (T : ℝ) * (s ^ 2 / (s * Real.sqrt (2 * (T : ℝ) / γ)) ^ 2) :=
        finite_square_moment_tail hR (fun t => (hm t).1) (fun t => (hm t).2) T
      _ = γ / 2 := by
        rw [mul_pow, Real.sq_sqrt harg.le]
        field_simp [hs0, ne_of_gt hTp, ne_of_gt hγ]

end LongTails.Proofs.MuonProcess
