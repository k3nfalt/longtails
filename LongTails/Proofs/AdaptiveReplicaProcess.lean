import LongTails.Proofs.AdaptiveReplicaMoments
import LongTails.Proofs.HeavyTailedProductProcess

open MeasureTheory

namespace LongTails.Proofs.AdaptiveReplicaProcess

open HeavyTailedProductProcess

lemma trajectory_potential_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (hs : Measurable (Function.uncurry step))
    (V : S → ℝ) (hV : Measurable V) (hV0 : ∀ s, 0 ≤ V s)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s) (n : ℕ) (s : S) :
    Integrable (fun ξ => V (trajectory step n s ξ)) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, V (trajectory step n s ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ V s := by
  induction n generalizing s with
  | zero => simp [trajectory]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → ℝ := fun z => V (trajectory step n (step s z.1) z.2)
      have hF : Measurable F :=
        hV.comp ((trajectory_measurable hs n).comp
          (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd))
      have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
        hF.stronglyMeasurable (fun z => hV0 _)
        (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).1))
        (hi s) (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).2))
      have hsplit := head_tail_preserving P
      have heq : (fun ξ => V (trajectory step (n + 1) s ξ)) =
          F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
      rw [heq]
      refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
        hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1))
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
      rw [← heint]
      exact hcontrol.2.trans (hb s)

lemma trajectory_reward_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (hs : Measurable (Function.uncurry step))
    (V : S → ℝ) (hV : Measurable V) (hV0 : ∀ s, 0 ≤ V s)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s)
    (R : S → Ω → ℝ) (hR : Measurable (Function.uncurry R))
    (hR0 : ∀ s ω, 0 ≤ R s ω)
    (hRi : ∀ s, Integrable (R s) P)
    (hRb : ∀ s, (∫ ω, R s ω ∂P) ≤ V s) (n : ℕ) (s : S) :
    Integrable (fun z : (ℕ → Ω) × Ω => R (trajectory step n s z.1) z.2)
      ((Measure.infinitePi fun _ : ℕ => P).prod P) ∧
    (∫ z : (ℕ → Ω) × Ω, R (trajectory step n s z.1) z.2
      ∂((Measure.infinitePi fun _ : ℕ => P).prod P)) ≤ V s := by
  have htrajectory : Measurable (trajectory step n s) :=
    (trajectory_measurable hs n).comp (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun z : (ℕ → Ω) × Ω => R (trajectory step n s z.1) z.2) :=
    hR.comp ((htrajectory.comp measurable_fst).prodMk measurable_snd)
  have hcontrol := trajectory_potential_bound P step hs V hV hV0 hi hb n s
  have hbound := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hF.stronglyMeasurable (fun z => hR0 _ _)
    (Filter.Eventually.of_forall (fun ξ => hRi (trajectory step n s ξ)))
    hcontrol.1 (Filter.Eventually.of_forall (fun ξ => hRb (trajectory step n s ξ)))
  exact ⟨hbound.1, hbound.2.trans hcontrol.2⟩

lemma trajectory_next_reward_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (step : S → Ω → S) (hs : Measurable (Function.uncurry step))
    (V : S → ℝ)
    (hi : ∀ s, Integrable (fun ω => V (step s ω)) P)
    (hb : ∀ s, (∫ ω, V (step s ω) ∂P) ≤ V s)
    (R : S → Ω → ℝ) (hR : Measurable (Function.uncurry R))
    (hR0 : ∀ s ω, 0 ≤ R s ω)
    (hRi : ∀ s, Integrable (R s) P)
    (hRb : ∀ s, (∫ ω, R s ω ∂P) ≤ V s) (n : ℕ) (s : S) :
    Integrable (fun ξ => R (trajectory step n s ξ) (ξ n))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, R (trajectory step n s ξ) (ξ n)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ V s := by
  induction n generalizing s with
  | zero =>
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0
    have hRs : Measurable (R s) := hR.comp measurable_prodMk_left
    refine ⟨hm.integrable_comp_of_integrable (hRi s), ?_⟩
    have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hm.measurable.aemeasurable hRs.aestronglyMeasurable
    rw [hm.map_eq] at he
    simpa [trajectory] using he.symm.trans_le (hRb s)
  | succ n ih =>
    let F : Ω × (ℕ → Ω) → ℝ :=
      fun z => R (trajectory step n (step s z.1) z.2) (z.2 n)
    have ht : Measurable (fun z : Ω × (ℕ → Ω) =>
        trajectory step n (step s z.1) z.2) :=
      (trajectory_measurable hs n).comp
        (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)
    have hF : Measurable F :=
      hR.comp (ht.prodMk ((measurable_pi_apply n).comp measurable_snd))
    have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun z => hR0 _ _)
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).1))
      (hi s) (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).2))
    have hsplit := head_tail_preserving P
    have heq : (fun ξ => R (trajectory step (n + 1) s ξ) (ξ (n + 1))) =
        F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
    rw [heq]
    refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
    have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heint
    change (∫ ξ, F (ξ 0, fun k => ξ (k + 1))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
    rw [← heint]
    exact hcontrol.2.trans (hb s)

def blockReward {S Ω : Type*} (cost : ℕ → ℕ)
    (step : (t : ℕ) → S → (Fin (cost t) → Ω) → S)
    (R : (t : ℕ) → S → (Fin (cost t) → Ω) → ℝ) :
    ℕ → ℕ → S → (ℕ → Ω) → ℝ
  | 0, t, s, ξ => R t s (fun i => ξ i.val)
  | n + 1, t, s, ξ => blockReward cost step R n (t + 1)
      (step t s (fun i => ξ i.val)) (fun k => ξ (cost t + k))

lemma blockReward_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (cost : ℕ → ℕ) (step : (t : ℕ) → S → (Fin (cost t) → Ω) → S)
    (hs : ∀ t, Measurable (Function.uncurry (step t)))
    (R : (t : ℕ) → S → (Fin (cost t) → Ω) → ℝ)
    (hR : ∀ t, Measurable (Function.uncurry (R t))) (n t : ℕ) :
    Measurable (Function.uncurry (blockReward cost step R n t)) := by
  induction n generalizing t with
  | zero => exact (hR t).comp (measurable_fst.prodMk (by fun_prop))
  | succ n ih =>
    exact (ih (t + 1)).comp
      (((hs t).comp (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop))

lemma blockReward_nonneg {S Ω : Type*} (cost : ℕ → ℕ)
    (step : (t : ℕ) → S → (Fin (cost t) → Ω) → S)
    (R : (t : ℕ) → S → (Fin (cost t) → Ω) → ℝ)
    (hR : ∀ t s ω, 0 ≤ R t s ω) (n t : ℕ) (s : S) (ξ : ℕ → Ω) :
    0 ≤ blockReward cost step R n t s ξ := by
  induction n generalizing t s ξ with
  | zero => exact hR t s _
  | succ n ih => exact ih (t + 1) _ _

lemma blockReward_integral_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : ℕ → ℕ)
    (step : (t : ℕ) → S → (Fin (cost t) → Ω) → S)
    (hs : ∀ t, Measurable (Function.uncurry (step t))) (V : ℕ → S → ℝ)
    (hi : ∀ t s, Integrable (fun ω => V (t + 1) (step t s ω))
      (Measure.pi fun _ : Fin (cost t) => P))
    (hb : ∀ t s, (∫ ω, V (t + 1) (step t s ω)
      ∂Measure.pi (fun _ : Fin (cost t) => P)) ≤ V t s)
    (R : (t : ℕ) → S → (Fin (cost t) → Ω) → ℝ)
    (hR : ∀ t, Measurable (Function.uncurry (R t)))
    (hR0 : ∀ t s ω, 0 ≤ R t s ω)
    (hRi : ∀ t s, Integrable (R t s) (Measure.pi fun _ : Fin (cost t) => P))
    (hRb : ∀ t s, (∫ ω, R t s ω ∂Measure.pi (fun _ : Fin (cost t) => P)) ≤ V t s)
    (n t : ℕ) (s : S) :
    Integrable (blockReward cost step R n t s) (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, blockReward cost step R n t s ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ V t s := by
  induction n generalizing t s with
  | zero =>
    have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving P (cost t)
    have hm := measurePreserving_fst.comp hsplit
    have hRs : Measurable (R t s) := (hR t).comp measurable_prodMk_left
    refine ⟨hm.integrable_comp_of_integrable (hRi t s), ?_⟩
    have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hm.measurable.aemeasurable hRs.aestronglyMeasurable
    rw [hm.map_eq] at he
    exact he.symm.trans_le (hRb t s)
  | succ n ih =>
    let F : (Fin (cost t) → Ω) × (ℕ → Ω) → ℝ :=
      fun z => blockReward cost step R n (t + 1) (step t s z.1) z.2
    have hF : Measurable F :=
      (blockReward_measurable cost step hs R hR n (t + 1)).comp
        ((((hs t).comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)
    have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun z => blockReward_nonneg cost step R hR0 n (t + 1) _ _)
      (Filter.Eventually.of_forall (fun ω => (ih (t + 1) (step t s ω)).1))
      (hi t s) (Filter.Eventually.of_forall (fun ω => (ih (t + 1) (step t s ω)).2))
    have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving P (cost t)
    have heq : blockReward cost step R (n + 1) t s =
        F ∘ OracleTemplate.StochasticGeneralized.splitStream (cost t) := rfl
    rw [heq]
    refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
    have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heint
    change (∫ ξ, F (OracleTemplate.StochasticGeneralized.splitStream (cost t) ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
    rw [← heint]
    exact hcontrol.2.trans (hb t s)

lemma prefix_uniform_integral_bound {S Ω Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (m : ℕ) (enter : (Fin m → Ω) → S) (hm : Measurable enter)
    (F : S → (ℕ → Ω) → ℝ) (hF : Measurable (Function.uncurry F))
    (hF0 : ∀ s ω, 0 ≤ F s ω) (C : ℝ)
    (hi : ∀ s, Integrable (F s) (Measure.infinitePi fun _ : ℕ => p))
    (hb : ∀ s, (∫ ω, F s ω ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ C) :
    Integrable (fun ω => F (enter (fun i => ξ i ω)) (fun k => ξ (m + k) ω)) P ∧
    (∫ ω, F (enter (fun i => ξ i ω)) (fun k => ξ (m + k) ω) ∂P) ≤ C := by
  let G : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z => F (enter z.1) z.2
  have hG : Measurable G := hF.comp ((hm.comp measurable_fst).prodMk measurable_snd)
  have hc := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin m => p)
    hG.stronglyMeasurable (fun z => hF0 _ _)
    (Filter.Eventually.of_forall (fun z => hi (enter z)))
    (integrable_const C) (Filter.Eventually.of_forall (fun z => hb (enter z)))
  have hl := hξ.prefix_tail_law m
  refine ⟨hl.integrable_comp_of_integrable hc.1, ?_⟩
  have he := integral_map (μ := P) hl.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hl.map_eq] at he
  exact he.symm.trans_le (by simpa using hc.2)

end LongTails.Proofs.AdaptiveReplicaProcess
