import LongTails.Proofs.AdaptiveReplicaProcess
import LongTails.Proofs.ZerothOrderGridEstimator

namespace LongTails.Proofs.DashaProcess

open MeasureTheory
open LongTails.Proofs.HeavyTailedProductProcess

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

noncomputable def totalReward (step : S → Ω → S) (V R : S → ℝ) : ℕ → S → (ℕ → Ω) → ℝ
  | 0, s, _ => V s
  | n + 1, s, ξ => R s + totalReward step V R n (step s (ξ 0)) (fun k => ξ (k + 1))

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma totalReward_nonneg (step : S → Ω → S) (V R : S → ℝ)
    (hV : ∀ s, 0 ≤ V s) (hR : ∀ s, 0 ≤ R s) (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    0 ≤ totalReward step V R n s ξ := by
  induction n generalizing s ξ with
  | zero => exact hV s
  | succ n ih => exact add_nonneg (hR s) (ih _ _)

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma totalReward_eq (step : S → Ω → S) (V R : S → ℝ) (n : ℕ) (s : S)
    (ξ : ℕ → Ω) : totalReward step V R n s ξ =
      V (trajectory step n s ξ) + ∑ j ∈ Finset.range n, R (trajectory step j s ξ) := by
  induction n generalizing s ξ with
  | zero => simp [totalReward, trajectory]
  | succ n ih =>
    rw [totalReward, ih, Finset.sum_range_succ']
    simp only [trajectory]
    ring

lemma totalReward_measurable (step : S → Ω → S) (V R : S → ℝ)
    (hs : Measurable (Function.uncurry step)) (hV : Measurable V) (hR : Measurable R) (n : ℕ) :
    Measurable (Function.uncurry (totalReward step V R n)) := by
  induction n with
  | zero => exact hV.comp measurable_fst
  | succ n ih =>
    exact (hR.comp measurable_fst).add (ih.comp
      ((hs.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (Measurable.of_eval (fun k => (measurable_pi_apply (k + 1)).comp measurable_snd))))

lemma totalReward_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (V R : S → ℝ)
    (hs : Measurable (Function.uncurry step)) (hV : Measurable V) (hR : Measurable R)
    (hV0 : ∀ s, 0 ≤ V s) (hR0 : ∀ s, 0 ≤ R s)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (c : ℝ) (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s - R s + c)
    (n : ℕ) (s : S) :
    Integrable (totalReward step V R n s) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, totalReward step V R n s ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ V s + n * c := by
  induction n generalizing s with
  | zero => simp [totalReward]
  | succ n ih =>
    let F : Ω × (ℕ → Ω) → ℝ := fun z => totalReward step V R n (step s z.1) z.2
    have hF : Measurable F :=
      (totalReward_measurable step V R hs hV hR n).comp
        (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)
    have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun z => totalReward_nonneg step V R hV0 hR0 n _ _)
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).1))
      ((hi s).add (integrable_const (n * c)))
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).2))
    have hsplit := head_tail_preserving P
    have hJ := hsplit.integrable_comp_of_integrable hcontrol.1
    change Integrable (fun ξ : ℕ → Ω => F (ξ 0, fun k => ξ (k + 1)))
      (Measure.infinitePi fun _ : ℕ => P) at hJ
    have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heint
    refine ⟨(integrable_const (R s)).add hJ, ?_⟩
    change (∫ ξ, R s + F (ξ 0, fun k => ξ (k + 1))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
    rw [integral_add (integrable_const _) hJ, integral_const, ← heint]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have hc := hcontrol.2
    change (∫ z, F z ∂P.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
      (∫ ω, V (step s ω) + n * c ∂P) at hc
    rw [integral_add (hi s) (integrable_const _), integral_const] at hc
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hc
    rw [Nat.cast_add, Nat.cast_one]
    linarith [hb s]

lemma initialized_totalReward_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (init : Ω → S) (V R : S → ℝ)
    (hs : Measurable (Function.uncurry step)) (hinit : Measurable init)
    (hV : Measurable V) (hR : Measurable R)
    (hV0 : ∀ s, 0 ≤ V s) (hR0 : ∀ s, 0 ≤ R s)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (hIi : Integrable (fun ω => V (init ω)) P)
    (c : ℝ) (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s - R s + c) (n : ℕ) :
    Integrable (fun ξ => totalReward step V R n (init (ξ 0)) (fun k => ξ (k + 1)))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, totalReward step V R n (init (ξ 0)) (fun k => ξ (k + 1))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (∫ ω, V (init ω) ∂P) + n * c := by
  let F : Ω × (ℕ → Ω) → ℝ := fun z => totalReward step V R n (init z.1) z.2
  have hF : Measurable F := (totalReward_measurable step V R hs hV hR n).comp
    ((hinit.comp measurable_fst).prodMk measurable_snd)
  have hbound := totalReward_bound P step V R hs hV hR hV0 hR0 hi c hb n
  have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hF.stronglyMeasurable (fun z => totalReward_nonneg step V R hV0 hR0 n _ _)
    (Filter.Eventually.of_forall (fun ω => (hbound (init ω)).1))
    (hIi.add (integrable_const (n * c)))
    (Filter.Eventually.of_forall (fun ω => (hbound (init ω)).2))
  have hsplit := head_tail_preserving P
  have hJ := hsplit.integrable_comp_of_integrable hcontrol.1
  have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
    hsplit.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hsplit.map_eq] at heint
  refine ⟨hJ, ?_⟩
  change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
  rw [← heint]
  have hc := hcontrol.2
  change (∫ z, F z ∂P.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
    (∫ ω, V (init ω) + n * c ∂P) at hc
  rw [integral_add hIi (integrable_const _), integral_const] at hc
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hc

lemma initialized_reward_sum_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (init : Ω → S) (V R : S → ℝ)
    (hs : Measurable (Function.uncurry step)) (hinit : Measurable init)
    (hV : Measurable V) (hR : Measurable R)
    (hV0 : ∀ s, 0 ≤ V s) (hR0 : ∀ s, 0 ≤ R s)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (hIi : Integrable (fun ω => V (init ω)) P)
    (c : ℝ) (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s - R s + c) (n : ℕ) :
    let sumR := fun ξ : ℕ → Ω => ∑ j ∈ Finset.range n,
      R (trajectory step j (init (ξ 0)) (fun k => ξ (k + 1)))
    Integrable sumR (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, sumR ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (∫ ω, V (init ω) ∂P) + n * c := by
  let sumR := fun ξ : ℕ → Ω => ∑ j ∈ Finset.range n,
    R (trajectory step j (init (ξ 0)) (fun k => ξ (k + 1)))
  have hsumM : Measurable sumR := by
    apply Finset.measurable_sum
    intro j _
    exact hR.comp ((trajectory_measurable hs j).comp
      ((hinit.comp (measurable_pi_apply 0)).prodMk
        (Measurable.of_eval (fun k => measurable_pi_apply (k + 1)))))
  have hsum0 (ξ : ℕ → Ω) : 0 ≤ sumR ξ := Finset.sum_nonneg (fun _ _ => hR0 _)
  have hsumle (ξ : ℕ → Ω) : sumR ξ ≤
      totalReward step V R n (init (ξ 0)) (fun k => ξ (k + 1)) := by
    rw [totalReward_eq]
    exact le_add_of_nonneg_left (hV0 _)
  have ht := initialized_totalReward_bound P step init V R hs hinit hV hR hV0 hR0 hi hIi c hb n
  have hI : Integrable sumR (Measure.infinitePi fun _ : ℕ => P) :=
    ht.1.mono' hsumM.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hsum0 ξ)]
      exact hsumle ξ))
  exact ⟨hI, (integral_mono hI ht.1 hsumle).trans ht.2⟩

lemma uniform_average (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ+)
    (X : Fin K → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (h0 : ∀ i ω, 0 ≤ X i ω)
    (hi : Integrable (fun ω => ∑ i, X i ω) P) :
    Integrable (fun z : Fin K × Ω => X z.1 z.2) ((PMF.uniformOfFintype (Fin K)).toMeasure.prod P) ∧
    (∫ z : Fin K × Ω, X z.1 z.2 ∂((PMF.uniformOfFintype (Fin K)).toMeasure.prod P)) =
      (1 / (K : ℝ)) * ∫ ω, ∑ i, X i ω ∂P := by
  have hIi (i : Fin K) : Integrable (X i) P :=
    hi.mono' (hm i).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 i ω)]
      exact Finset.single_le_sum (fun j _ => h0 j ω) (Finset.mem_univ i)))
  have hM : Measurable (fun z : Fin K × Ω => X z.1 z.2) :=
    measurable_from_prod_countable_right hm
  have hprod := OracleTemplate.ZerothOrder.finite_prod_integrable
    (μ := (PMF.uniformOfFintype (Fin K)).toMeasure) (ν := P) hM.aestronglyMeasurable hIi
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod, OracleTemplate.ZerothOrder.uniform_integral_explicit,
    integral_finsetSum _ (fun i _ => hIi i)]
  simp only [Fintype.card_fin, smul_eq_mul, one_div]

end LongTails.Proofs.DashaProcess
