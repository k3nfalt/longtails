import LongTails.Proofs.HessianAdaptiveCubicMoments
import LongTails.Proofs.NormSubGaussianBatch
import LongTails.Proofs.SymmetricThirdOrderEstimation
import LongTails.Proofs.SymmetricThirdOrderHistory

namespace LongTails.Proofs.SymmetricThirdOrderSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma prefix_block_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω)))
      P ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin k => p)) := by
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving p k)).comp (h.prefix_tail_law n)
  simpa only [Function.comp_def, Prod.map, id_eq] using hp

lemma prefix_block_probability {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ)
    (S : Set ((Fin n → Ω) × (Fin k → Ω))) (hS : MeasurableSet S) (q : ℝ≥0∞)
    (hb : ∀ u, (Measure.pi fun _ : Fin k => p) {v | (u, v) ∈ S} ≤ q) :
    P {ω | ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω)) ∈ S} ≤ q := by
  have hp := prefix_block_law h n k
  have he := congrArg (fun μ : Measure ((Fin n → Ω) × (Fin k → Ω)) => μ S) hp.map_eq
  rw [Measure.map_apply hp.measurable hS] at he
  change P ((fun ω => ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω))) ⁻¹' S) ≤ q
  rw [he, Measure.prod_apply hS]
  exact (lintegral_mono hb).trans_eq (by simp)

lemma prefix_block_nonnegative_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ)
    (F : (Fin n → Ω) × (Fin k → Ω) → ℝ) (B : ℝ) (hF : Measurable F)
    (hpos : ∀ z, 0 ≤ F z)
    (hsections : ∀ u, Integrable (fun v => F (u, v)) (Measure.pi fun _ : Fin k => p))
    (hbound : ∀ u, (∫ v, F (u, v) ∂(Measure.pi fun _ : Fin k => p)) ≤ B) :
    Integrable (fun ω => F ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω))) P ∧
      (∫ ω, F ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω)) ∂P) ≤ B := by
  have hp := HessianAdaptiveCubicMoments.nonnegative_product_bound
    (Measure.pi fun _ : Fin n => p) (Measure.pi fun _ : Fin k => p) F B hF hpos hsections hbound
  have hlaw := prefix_block_law h n k
  refine ⟨hlaw.integrable_comp_of_integrable hp.1, ?_⟩
  rw [HessianAdaptiveCubicMoments.preserving_integral hlaw hF.aestronglyMeasurable]
  exact hp.2

set_option maxHeartbeats 800000 in
lemma adaptive_hessian_failure {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ)
    (x : (Fin n → Ω) → E) (hx : Measurable x)
    (H : E → Ω → E →L[ℝ] E) (hH : Measurable (Function.uncurry H))
    (Htrue : E → E →L[ℝ] E) (htrue : Measurable Htrue)
    (hsym : ∀ z a b : E, inner ℝ a (Htrue z b) = inner ℝ (Htrue z a) b)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : ∀ z, Integrable (fun ω => ‖H z ω - Htrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖H z ω - Htrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    P {ω | 9 * σ < ‖LongTails.Algorithms.SymmetricThirdOrder.hessianPilot σ
      (fun i : Fin k => H (x (fun j => ξ j ω)) (ξ (n + i) ω)) - Htrue (x (fun j => ξ j ω))‖} ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ k) := by
  let S : Set ((Fin n → Ω) × (Fin k → Ω)) := {z | 9 * σ <
    ‖LongTails.Algorithms.SymmetricThirdOrder.hessianPilot σ (fun i => H (x z.1) (z.2 i)) - Htrue (x z.1)‖}
  have hdata : Measurable (fun z : (Fin n → Ω) × (Fin k → Ω) =>
      (σ, fun i : Fin k => H (x z.1) (z.2 i))) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    exact hH.comp ((hx.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hpilot := (SymmetricThirdOrderEstimation.measurable_hessianPilot (E := E) k).comp hdata
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    ((hpilot.sub (htrue.comp (hx.comp measurable_fst))).norm)
  apply prefix_block_probability h n k S hS
  intro u
  exact SymmetricThirdOrderEstimation.hessianPilot_failure
    (hH.comp (measurable_const.prodMk measurable_id)) (Htrue (x u)) (hsym (x u)) hσ
    (hi (x u)) (hm (x u)) k

lemma prefix_group_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k m : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin n => ξ i ω),
      (fun (i : Fin k) (j : Fin m) => ξ (n + m * i.val + j.val) ω)))
      P ((Measure.pi fun _ : Fin n => p).prod
        (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => p)) := by
  have hid := OracleTemplate.StochasticGeneralized.infinitePi_iid p
  have hb := OracleTemplate.FiniteVariance.infinite_block_law p
    (Measure.infinitePi fun _ : ℕ => p) hid.independent hid.marginal m
  have hpre := (OracleTemplate.StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin m => p) k).comp hb
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod hpre).comp (h.prefix_tail_law n)
  simpa only [Function.comp_def, Prod.map, id_eq, Nat.mul_comm, Nat.add_assoc] using hp

lemma adaptive_gradient_failure {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k m : ℕ)
    (x : (Fin n → Ω) → E) (hx : Measurable x)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (gtrue : E → E) (htrue : Measurable gtrue)
    {σ a : ℝ} (ha : 0 < a) (hmpos : 0 < m) (hsize : 144 * σ ^ 2 ≤ (m : ℝ) * a ^ 2)
    (hgi : ∀ z, Integrable (g z) p) (hmean : ∀ z, ∫ ω, g z ω ∂p = gtrue z)
    (hi : ∀ z, Integrable (fun ω => ‖g z ω - gtrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖g z ω - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    P {ω | a < ‖LongTails.Algorithms.SymmetricThirdOrder.gradientPilot a
      (fun (i : Fin k) (j : Fin m) => g (x (fun l => ξ l ω)) (ξ (n + m * i.val + j.val) ω)) -
        gtrue (x (fun l => ξ l ω))‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  let S : Set ((Fin n → Ω) × (Fin k → Fin m → Ω)) := {z | a <
    ‖LongTails.Algorithms.SymmetricThirdOrder.gradientPilot a (fun i j => g (x z.1) (z.2 i j)) - gtrue (x z.1)‖}
  have hdata : Measurable (fun z : (Fin n → Ω) × (Fin k → Fin m → Ω) =>
      (a, fun (i : Fin k) (j : Fin m) => g (x z.1) (z.2 i j))) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hg.comp ((hx.comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)))
  have hpilot := (SymmetricThirdOrderEstimation.measurable_gradientPilot (E := E) k m).comp hdata
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    ((hpilot.sub (htrue.comp (hx.comp measurable_fst))).norm)
  have hlaw := prefix_group_law h n k m
  have he := congrArg (fun μ : Measure ((Fin n → Ω) × (Fin k → Fin m → Ω)) => μ S) hlaw.map_eq
  rw [Measure.map_apply hlaw.measurable hS] at he
  change P ((fun ω => ((fun i : Fin n => ξ i ω),
    (fun (i : Fin k) (j : Fin m) => ξ (n + m * i.val + j.val) ω))) ⁻¹' S) ≤ _
  rw [he, Measure.prod_apply hS]
  have hb : ∀ u, (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => p)
      {v | (u, v) ∈ S} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro u
    exact SymmetricThirdOrderEstimation.gradientPilot_failure
      (hg.comp (measurable_const.prodMk measurable_id)) (hgi (x u)) (gtrue (x u)) (hmean (x u))
      ha (hi (x u)) (hm (x u)) k m hmpos hsize
  exact (lintegral_mono hb).trans_eq (by simp)

lemma measurable_prefix_factor {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) (F : (ℕ → Ω) → Y) (hF : Measurable F)
    (hdep : ∀ ξ η, (∀ i < n, ξ i = η i) → F ξ = F η) :
    ∃ G : (Fin n → Ω) → Y, Measurable G ∧ ∀ ξ, F ξ = G (fun i => ξ i) := by
  obtain ⟨ω0, _⟩ := nonempty_of_measure_ne_zero (show p Set.univ ≠ 0 by simp)
  refine ⟨fun u => F (HessianAdaptiveCubicMoments.prefixExtend ω0 n u),
    hF.comp (HessianAdaptiveCubicMoments.measurable_prefixExtend ω0 n), ?_⟩
  exact HessianAdaptiveCubicMoments.factor_prefix ω0 n F hdep

lemma adaptive_hessian_failure_stream {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ)
    (x : (ℕ → Ω) → E) (hx : Measurable x)
    (hdep : ∀ ζ η, (∀ i < n, ζ i = η i) → x ζ = x η)
    (H : E → Ω → E →L[ℝ] E) (hH : Measurable (Function.uncurry H))
    (Htrue : E → E →L[ℝ] E) (htrue : Measurable Htrue)
    (hsym : ∀ z a b : E, inner ℝ a (Htrue z b) = inner ℝ (Htrue z a) b)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : ∀ z, Integrable (fun ω => ‖H z ω - Htrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖H z ω - Htrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    P {ω | 9 * σ < ‖LongTails.Algorithms.SymmetricThirdOrder.hessianPilot σ
      (fun i : Fin k => H (x (fun j => ξ j ω)) (ξ (n + i) ω)) - Htrue (x (fun j => ξ j ω))‖} ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ k) := by
  obtain ⟨xp, hxp, hfactor⟩ := measurable_prefix_factor p n x hx hdep
  have hb := adaptive_hessian_failure h n k xp hxp H hH Htrue htrue hsym hσ hi hm
  have he (ω : Ξ) : x (fun j => ξ j ω) = xp (fun i => ξ i ω) := hfactor _
  simpa only [← he] using hb

lemma adaptive_gradient_failure_stream {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k m : ℕ)
    (x : (ℕ → Ω) → E) (hx : Measurable x)
    (hdep : ∀ ζ η, (∀ i < n, ζ i = η i) → x ζ = x η)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (gtrue : E → E) (htrue : Measurable gtrue)
    {σ a : ℝ} (ha : 0 < a) (hmpos : 0 < m) (hsize : 144 * σ ^ 2 ≤ (m : ℝ) * a ^ 2)
    (hgi : ∀ z, Integrable (g z) p) (hmean : ∀ z, ∫ ω, g z ω ∂p = gtrue z)
    (hi : ∀ z, Integrable (fun ω => ‖g z ω - gtrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖g z ω - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    P {ω | a < ‖LongTails.Algorithms.SymmetricThirdOrder.gradientPilot a
      (fun (i : Fin k) (j : Fin m) => g (x (fun l => ξ l ω)) (ξ (n + m * i.val + j.val) ω)) -
        gtrue (x (fun l => ξ l ω))‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  obtain ⟨xp, hxp, hfactor⟩ := measurable_prefix_factor p n x hx hdep
  have hb := adaptive_gradient_failure h n k m xp hxp g hg gtrue htrue ha hmpos hsize hgi hmean hi hm
  have he (ω : Ξ) : x (fun j => ξ j ω) = xp (fun i => ξ i ω) := hfactor _
  simpa only [← he] using hb

lemma sampled_center_hessian_failure {Ω E : Type}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : LongTails.Algorithms.SymmetricThirdOrder.Config E)
    (oracle : E → Ω → LongTails.Algorithms.SymmetricThirdOrder.Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hσ : 0 ≤ cfg.σh)
    (Htrue : E → E →L[ℝ] E) (htrue : Measurable Htrue)
    (hsym : ∀ z a b : E, inner ℝ a (Htrue z b) = inner ℝ (Htrue z a) b)
    (hi : ∀ z, Integrable (fun ω => ‖(oracle z ω).2 - Htrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖(oracle z ω).2 - Htrue z‖ ^ 2 ∂p) ≤ cfg.σh ^ 2) (t : ℕ) :
    P {ξ | 9 * cfg.σh <
      ‖OracleTemplate.QueryPlan.sampledEval oracle ξ
        (LongTails.Algorithms.SymmetricThirdOrder.hessianPlan cfg
          (LongTails.Algorithms.SymmetricThirdOrder.sampledCenter cfg oracle ξ t))
        (LongTails.Algorithms.SymmetricThirdOrder.roundCalls cfg * t) -
      Htrue (LongTails.Algorithms.SymmetricThirdOrder.sampledCenter cfg oracle ξ t)‖} ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ cfg.groups) := by
  have hb := adaptive_hessian_failure_stream h
    (LongTails.Algorithms.SymmetricThirdOrder.roundCalls cfg * t) cfg.groups
    (fun ξ => LongTails.Algorithms.SymmetricThirdOrder.sampledCenter cfg oracle ξ t)
    (SymmetricThirdOrderHistory.measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t)
    (fun ξ η hξ => SymmetricThirdOrderHistory.sampledCenter_prefix cfg oracle t ξ η hξ)
    (fun z ω => (oracle z ω).2) ho.snd Htrue htrue hsym hσ hi hm
  simpa only [SymmetricThirdOrderExecution.hessianPlan_eval] using hb

open LongTails.Algorithms.SymmetricThirdOrder

lemma sampled_endpoint_gradient_failure {Ω E : Type}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (ha : 0 < cfg.tolerance)
    (gtrue : E → E) (htrue : Measurable gtrue) {σ : ℝ} (hmpos : 0 < cfg.batch)
    (hsize : 144 * σ ^ 2 ≤ (cfg.batch : ℝ) * cfg.tolerance ^ 2)
    (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gtrue z)
    (hi : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gtrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖(oracle z ω).1 - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2)
    (t j : ℕ) (reflected : Bool) :
    let start := roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j +
      (if reflected then cfg.batch * cfg.groups else 0)
    let point := fun ξ => if reflected then sampledCenter cfg oracle ξ t -
      (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t) else sampledInner cfg oracle ξ t j
    P {ξ | cfg.tolerance < ‖OracleTemplate.QueryPlan.sampledEval oracle ξ (gradientPlan cfg (point ξ)) start -
      gtrue (point ξ)‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ cfg.groups) := by
  let start := roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j +
    (if reflected then cfg.batch * cfg.groups else 0)
  let point := fun ξ => if reflected then sampledCenter cfg oracle ξ t -
    (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t) else sampledInner cfg oracle ξ t j
  have hx : Measurable point := SymmetricThirdOrderHistory.measurable_sampledEndpoint cfg oracle ho
    hC hne hconv hL hδ t j reflected
  have hdep : ∀ ξ η, (∀ i < start, ξ i = η i) → point ξ = point η :=
    SymmetricThirdOrderHistory.sampledEndpoint_prefix cfg oracle t j start reflected (Nat.le_add_right _ _)
  have hb := adaptive_gradient_failure_stream h start cfg.groups cfg.batch point hx hdep
    (fun z ω => (oracle z ω).1) ho.fst gtrue htrue ha hmpos hsize hgi hmean hi hm
  simpa only [SymmetricThirdOrderExecution.gradientPlan_eval] using hb

lemma sampled_cleanup_hessian_failure {Ω E : Type}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hσ : 0 ≤ cfg.σh)
    (Htrue : E → E →L[ℝ] E) (htrue : Measurable Htrue)
    (hsym : ∀ z a b : E, inner ℝ a (Htrue z b) = inner ℝ (Htrue z a) b)
    (hi : ∀ z, Integrable (fun ω => ‖(oracle z ω).2 - Htrue z‖ ^ 2) p)
    (hm : ∀ z, (∫ ω, ‖(oracle z ω).2 - Htrue z‖ ^ 2 ∂p) ≤ cfg.σh ^ 2)
    (t : ℕ) (reflected : Bool) :
    let start := roundCalls cfg * t + cfg.groups +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) + (if reflected then cfg.groups else 0)
    let point := fun ξ => if reflected then sampledCenter cfg oracle ξ t -
      (sampledInner cfg oracle ξ t cfg.innerRounds - sampledCenter cfg oracle ξ t)
      else sampledInner cfg oracle ξ t cfg.innerRounds
    P {ξ | 9 * cfg.σh < ‖OracleTemplate.QueryPlan.sampledEval oracle ξ (hessianPlan cfg (point ξ)) start -
      Htrue (point ξ)‖} ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ cfg.groups) := by
  let start := roundCalls cfg * t + cfg.groups +
    (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
    (cfg.batch * cfg.groups + cfg.batch * cfg.groups) + (if reflected then cfg.groups else 0)
  let point := fun ξ => if reflected then sampledCenter cfg oracle ξ t -
    (sampledInner cfg oracle ξ t cfg.innerRounds - sampledCenter cfg oracle ξ t)
    else sampledInner cfg oracle ξ t cfg.innerRounds
  have hx : Measurable point := SymmetricThirdOrderHistory.measurable_sampledEndpoint cfg oracle ho
    hC hne hconv hL hδ t cfg.innerRounds reflected
  have hdep : ∀ ξ η, (∀ i < start, ξ i = η i) → point ξ = point η :=
    SymmetricThirdOrderHistory.sampledEndpoint_prefix cfg oracle t cfg.innerRounds start reflected (by dsimp [start]; omega)
  have hb := adaptive_hessian_failure_stream h start cfg.groups point hx hdep
    (fun z ω => (oracle z ω).2) ho.snd Htrue htrue hsym hσ hi hm
  simpa only [SymmetricThirdOrderExecution.hessianPlan_eval] using hb

lemma prefix_block_integral {Ω Ξ V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n k : ℕ)
    (F : (Fin n → Ω) × (Fin k → Ω) → V)
    (hF : Integrable F ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin k => p))) :
    (∫ ω, F ((fun i : Fin n => ξ i ω), (fun i : Fin k => ξ (n + i) ω)) ∂P) =
      ∫ u, (∫ v, F (u, v) ∂(Measure.pi fun _ : Fin k => p)) ∂(Measure.pi fun _ : Fin n => p) := by
  rw [HessianAdaptiveCubicMoments.preserving_integral (prefix_block_law h n k) hF.aestronglyMeasurable,
    integral_prod _ hF]

lemma finite_mean_noise {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p : Measure Ω} [IsProbabilityMeasure p] {X : Ω → E}
    (hX : Measurable X) (hXi : Integrable X p) (u : E)
    (hmean : (∫ ω, X ω ∂p) = u) (h₂ : Integrable (fun ω => ‖X ω - u‖ ^ 2) p)
    {σ : ℝ} (hvar : (∫ ω, ‖X ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) (m : ℕ) (hm : 0 < m) :
    let e := fun v : Fin m → Ω => (1 / (m : ℝ)) • ∑ i, X (v i) - u
    Integrable e (Measure.pi fun _ : Fin m => p) ∧
      (∫ v, e v ∂(Measure.pi fun _ : Fin m => p)) = 0 ∧
      Integrable (fun v => ‖e v‖ ^ 2) (Measure.pi fun _ : Fin m => p) ∧
      (∫ v, ‖e v‖ ^ 2 ∂(Measure.pi fun _ : Fin m => p)) ≤ σ ^ 2 / m := by
  have h₁ := OracleTemplate.LightTail.finite_mean_integral hXi m hm
  have hv := OracleTemplate.RobustGradient.finite_mean_variance hX hXi u h₂ hmean m hm
  refine ⟨h₁.1.sub (integrable_const u), ?_, hv.1, ?_⟩
  · rw [integral_sub h₁.1 (integrable_const u), h₁.2, hmean]
    simp
  · exact hv.2.le.trans (div_le_div_of_nonneg_right hvar (Nat.cast_nonneg m))

lemma adaptive_mean_variance {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n m : ℕ) (hm : 0 < m)
    (x : (Fin n → Ω) → E) (hx : Measurable x)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (gtrue : E → E) (htrue : Measurable gtrue)
    (hi : ∀ z, Integrable (g z) p) (hmean : ∀ z, (∫ ω, g z ω ∂p) = gtrue z)
    (h₂ : ∀ z, Integrable (fun ω => ‖g z ω - gtrue z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖g z ω - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    let e := fun ω => (1 / (m : ℝ)) • ∑ i : Fin m, g (x (fun j => ξ j ω)) (ξ (n + i) ω) -
      gtrue (x (fun j => ξ j ω))
    Integrable (fun ω => ‖e ω‖ ^ 2) P ∧ (∫ ω, ‖e ω‖ ^ 2 ∂P) ≤ σ ^ 2 / m := by
  let F := fun z : (Fin n → Ω) × (Fin m → Ω) =>
    ‖(1 / (m : ℝ)) • ∑ i : Fin m, g (x z.1) (z.2 i) - gtrue (x z.1)‖ ^ 2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub
    · apply Measurable.const_smul
      exact Finset.measurable_sum _ (fun i _ => hg.comp ((hx.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
    · exact htrue.comp (hx.comp measurable_fst)
  have hb (u : Fin n → Ω) := finite_mean_noise
    (hg.comp (measurable_const.prodMk measurable_id)) (hi (x u)) (gtrue (x u))
      (hmean (x u)) (h₂ (x u)) (hvar (x u)) m hm
  exact prefix_block_nonnegative_bound h n m F (σ ^ 2 / m) hF (fun _ => sq_nonneg _)
    (fun u => (hb u).2.2.1) (fun u => (hb u).2.2.2)

lemma adaptive_mean_variance_stream {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n m : ℕ) (hm : 0 < m)
    (x : (ℕ → Ω) → E) (hx : Measurable x)
    (hdep : ∀ ζ η, (∀ i < n, ζ i = η i) → x ζ = x η)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (gtrue : E → E) (htrue : Measurable gtrue)
    (hi : ∀ z, Integrable (g z) p) (hmean : ∀ z, (∫ ω, g z ω ∂p) = gtrue z)
    (h₂ : ∀ z, Integrable (fun ω => ‖g z ω - gtrue z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖g z ω - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2) :
    let e := fun ω => (1 / (m : ℝ)) • ∑ i : Fin m, g (x (fun j => ξ j ω)) (ξ (n + i) ω) -
      gtrue (x (fun j => ξ j ω))
    Integrable (fun ω => ‖e ω‖ ^ 2) P ∧ (∫ ω, ‖e ω‖ ^ 2 ∂P) ≤ σ ^ 2 / m := by
  obtain ⟨xp, hxp, hfactor⟩ := measurable_prefix_factor p n x hx hdep
  have hb := adaptive_mean_variance h n m hm xp hxp g hg gtrue htrue hi hmean h₂ hvar
  have he (ω : Ξ) : x (fun j => ξ j ω) = xp (fun i => ξ i ω) := hfactor _
  simpa only [← he] using hb

lemma sampled_mean_variance {Ω E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hm : 0 < cfg.batch)
    (gtrue : E → E) (htrue : Measurable gtrue)
    (hi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gtrue z)
    (h₂ : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gtrue z‖ ^ 2) p)
    {σ : ℝ} (hvar : ∀ z, (∫ ω, ‖(oracle z ω).1 - gtrue z‖ ^ 2 ∂p) ≤ σ ^ 2) (t : ℕ) :
    let e := fun ξ => OracleTemplate.QueryPlan.sampledEval oracle ξ
      (meanPlan cfg.batch (sampledCleanup cfg oracle ξ t).1) (roundCalls cfg * (t + 1) - cfg.batch) -
        gtrue (sampledCleanup cfg oracle ξ t).1
    Integrable (fun ξ => ‖e ξ‖ ^ 2) P ∧ (∫ ξ, ‖e ξ‖ ^ 2 ∂P) ≤ σ ^ 2 / cfg.batch := by
  have hx := (SymmetricThirdOrderHistory.measurable_sampledCleanup cfg oracle ho hC hne hconv hL hδ t).fst
  have hdep : ∀ ζ η, (∀ i < roundCalls cfg * (t + 1) - cfg.batch, ζ i = η i) →
      (sampledCleanup cfg oracle ζ t).1 = (sampledCleanup cfg oracle η t).1 := by
    intro ζ η hh
    apply congrArg Prod.fst
    apply SymmetricThirdOrderHistory.sampledCleanup_prefix cfg oracle t ζ η
    simpa only [SymmetricThirdOrderHistory.correction_start] using hh
  have hb := adaptive_mean_variance_stream h (roundCalls cfg * (t + 1) - cfg.batch) cfg.batch hm
    (fun ξ => (sampledCleanup cfg oracle ξ t).1) hx hdep (fun z ω => (oracle z ω).1) ho.fst
    gtrue htrue hi hmean h₂ hvar
  simpa only [SymmetricThirdOrderExecution.meanPlan_eval] using hb

def blockExtend {Ω : Type*} (ω0 : Ω) (n m : ℕ) (u : Fin n → Ω) (v : Fin m → Ω) (j : ℕ) : Ω :=
  if hj : j < n then u ⟨j, hj⟩ else if hk : j - n < m then v ⟨j - n, hk⟩ else ω0

lemma blockExtend_head {Ω : Type*} (ω0 : Ω) (n m : ℕ) (u : Fin n → Ω) (v : Fin m → Ω) (i : Fin n) :
    blockExtend ω0 n m u v i = u i := by
  simp only [blockExtend, dite_eq_left i.isLt]

lemma blockExtend_tail {Ω : Type*} (ω0 : Ω) (n m : ℕ) (u : Fin n → Ω) (v : Fin m → Ω) (i : Fin m) :
    blockExtend ω0 n m u v (n + i) = v i := by
  have hh : ¬n + i.val < n := by omega
  simp only [blockExtend, dite_eq_right hh, Nat.add_sub_cancel_left, dite_eq_left i.isLt]

lemma measurable_blockExtend {Ω : Type*} [MeasurableSpace Ω] (ω0 : Ω) (n m : ℕ) :
    Measurable (fun z : (Fin n → Ω) × (Fin m → Ω) => blockExtend ω0 n m z.1 z.2) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j < n
  · simp only [blockExtend, dite_eq_left hj]
    exact (measurable_pi_apply _).comp measurable_fst
  · by_cases hk : j - n < m
    · simp only [blockExtend, dite_eq_right hj, dite_eq_left hk]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [blockExtend, dite_eq_right hj, dite_eq_right hk]
      exact measurable_const

lemma blockExtend_reconstruct {Ω : Type*} (ω0 : Ω) (n m : ℕ) (ξ : ℕ → Ω) (j : ℕ) (hj : j < n + m) :
    blockExtend ω0 n m (fun i => ξ i) (fun i => ξ (n + i)) j = ξ j := by
  by_cases hn : j < n
  · simp only [blockExtend, dite_eq_left hn]
  · have hk : j - n < m := by omega
    simp only [blockExtend, dite_eq_right hn, dite_eq_left hk]
    congr 1
    omega

lemma blockExtend_prefix {Ω V : Type*} (ω0 : Ω) (n m : ℕ) (F : (ℕ → Ω) → V)
    (hF : ∀ ξ η, (∀ j < n, ξ j = η j) → F ξ = F η)
    (u : Fin n → Ω) (v w : Fin m → Ω) :
    F (blockExtend ω0 n m u v) = F (blockExtend ω0 n m u w) := by
  apply hF
  intro j hj
  simp only [blockExtend, dite_eq_left hj]

lemma block_integrable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (ω0 : Ω) (n m : ℕ)
    (F : (ℕ → Ω) → ℝ) (hF : Measurable F)
    (hdep : ∀ ζ η, (∀ j < n + m, ζ j = η j) → F ζ = F η)
    (hi : Integrable (fun ω => F (fun j => ξ j ω)) P) :
    Integrable (fun z : (Fin n → Ω) × (Fin m → Ω) => F (blockExtend ω0 n m z.1 z.2))
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin m => p)) := by
  have hm := hF.comp (measurable_blockExtend ω0 n m)
  apply ((prefix_block_law h n m).integrable_comp hm.aestronglyMeasurable).mp
  have he (ω : Ξ) : F (blockExtend ω0 n m (fun i => ξ i ω) (fun i => ξ (n + i) ω)) =
      F (fun j => ξ j ω) := hdep _ _ (blockExtend_reconstruct ω0 n m (fun j => ξ j ω))
  simpa only [Function.comp_def, he] using hi

lemma block_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (ω0 : Ω) (n m : ℕ)
    (F : (ℕ → Ω) → ℝ) (hF : Measurable F)
    (hdep : ∀ ζ η, (∀ j < n + m, ζ j = η j) → F ζ = F η)
    (hi : Integrable (fun ω => F (fun j => ξ j ω)) P) :
    (∫ ω, F (fun j => ξ j ω) ∂P) = ∫ u, (∫ v, F (blockExtend ω0 n m u v)
      ∂(Measure.pi fun _ : Fin m => p)) ∂(Measure.pi fun _ : Fin n => p) := by
  have hb := prefix_block_integral h n m (fun z => F (blockExtend ω0 n m z.1 z.2))
    (block_integrable h ω0 n m F hF hdep hi)
  have he (ω : Ξ) : F (blockExtend ω0 n m (fun i => ξ i ω) (fun i => ξ (n + i) ω)) =
      F (fun j => ξ j ω) := hdep _ _ (blockExtend_reconstruct ω0 n m (fun j => ξ j ω))
  simpa only [he] using hb

lemma prefix_block_drift {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (ω0 : Ω) (n m : ℕ)
    (F B : (ℕ → Ω) → ℝ) (hF : Measurable F) (hB : Measurable B)
    (hdepF : ∀ ζ η, (∀ j < n + m, ζ j = η j) → F ζ = F η)
    (hdepB : ∀ ζ η, (∀ j < n, ζ j = η j) → B ζ = B η)
    (hFi : Integrable (fun ω => F (fun j => ξ j ω)) P)
    (hBi : Integrable (fun ω => B (fun j => ξ j ω)) P) (c : ℝ)
    (hsection : ∀ u : Fin n → Ω,
      Integrable (fun v => F (blockExtend ω0 n m u v)) (Measure.pi fun _ : Fin m => p) →
      (∫ v, F (blockExtend ω0 n m u v) ∂(Measure.pi fun _ : Fin m => p)) ≤
        B (blockExtend ω0 n m u (fun _ => ω0)) + c) :
    (∫ ω, F (fun j => ξ j ω) ∂P) ≤ (∫ ω, B (fun j => ξ j ω) ∂P) + c := by
  have hdepB' : ∀ ζ η, (∀ j < n + m, ζ j = η j) → B ζ = B η :=
    fun ζ η he => hdepB ζ η (fun j hj => he j (by omega))
  have hFp := block_integrable h ω0 n m F hF hdepF hFi
  have hBp := block_integrable h ω0 n m B hB hdepB' hBi
  have hconst (u : Fin n → Ω) :
      (∫ v, B (blockExtend ω0 n m u v) ∂(Measure.pi fun _ : Fin m => p)) =
        B (blockExtend ω0 n m u (fun _ => ω0)) := by
    simp_rw [blockExtend_prefix ω0 n m B hdepB u _ (fun _ => ω0)]
    simp
  have hbint : Integrable (fun u => B (blockExtend ω0 n m u (fun _ => ω0)))
      (Measure.pi fun _ : Fin n => p) := by
    simpa only [hconst] using hBp.integral_prod_left
  have hh := integral_mono_ae hFp.integral_prod_left (hbint.add (integrable_const c))
    (by filter_upwards [hFp.prod_right_ae] with u hu; exact hsection u hu)
  rw [block_integral h ω0 n m F hF hdepF hFi, block_integral h ω0 n m B hB hdepB' hBi]
  simp_rw [hconst]
  simpa only [Pi.add_apply, integral_add hbint (integrable_const c), integral_const, probReal_univ, one_smul] using hh

end LongTails.Proofs.SymmetricThirdOrderSampling
