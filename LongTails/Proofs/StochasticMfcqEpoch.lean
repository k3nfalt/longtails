import LongTails.Proofs.StochasticMfcqOracle
import LongTails.Proofs.StochasticMfcqMeasurability
import LongTails.Proofs.AdaptiveReplicaProbability

open MeasureTheory

namespace LongTails.Proofs.StochasticMfcqEpoch

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open StochasticMfcqMeasurability StochasticMfcqOracle

abbrev KilledState (p : Params) := Bool × State p

def live (p : Params) (I : Problem p) (s : KilledState p) : Prop :=
  s.1 = true ∧ validQueryState p I s.2

noncomputable def killedNext (p : Params) (I : Problem p) (s : KilledState p)
    (estimates : Fin (replicas p) → JointSpace p) : KilledState p := by
  classical
  exact (decide (live p I s ∧ validQueryState p I (nextState p s.2 estimates)),
    nextState p s.2 estimates)

noncomputable def potential (p : Params) (I : Problem p) (a : ℝ) (s : KilledState p) : ℝ := by
  classical
  exact if live p I s then ∏ i, (‖s.2.2.2.1 i - mean p I s.2.2.1‖ ^ 2 + precision p ^ 2 / 576 + a)
    else 0

noncomputable def reward (p : Params) (I : Problem p) (a : ℝ) (s : KilledState p)
    (estimates : Fin (replicas p) → JointSpace p) : ℝ := by
  classical
  exact if live p I s then ∏ i, (‖estimates i - mean p I s.2.1‖ ^ 2 + precision p ^ 2 / 576 + a)
    else 0

lemma killedNext_live (p : Params) (I : Problem p) (s : KilledState p)
    (estimates : Fin (replicas p) → JointSpace p) :
    live p I (killedNext p I s estimates) ↔
      live p I s ∧ validQueryState p I (nextState p s.2 estimates) := by
  classical
  change (decide (live p I s ∧ validQueryState p I (nextState p s.2 estimates)) = true ∧
    validQueryState p I (nextState p s.2 estimates)) ↔ _
  rw [decide_eq_true_eq]
  tauto

lemma killedNext_dead (p : Params) (I : Problem p) (s : KilledState p)
    (estimates : Fin (replicas p) → JointSpace p) (hs : ¬ live p I s) :
    ¬ live p I (killedNext p I s estimates) := by
  rw [killedNext_live]
  exact fun h => hs h.1

lemma reward_nonneg (p : Params) (I : Problem p) (a : ℝ) (ha : 0 ≤ a)
    (s : KilledState p) (estimates : Fin (replicas p) → JointSpace p) :
    0 ≤ reward p I a s estimates := by
  classical
  unfold reward
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => by positivity)
  · exact le_rfl

lemma next_estimates (p : Params) (s : State p)
    (estimates : Fin (replicas p) → JointSpace p) :
    (nextState p s estimates).2.2.1 = estimates := by
  dsimp only [nextState]
  split_ifs <;> rfl

lemma potential_next_le_reward (p : Params) (I : Problem p) (a : ℝ) (ha : 0 ≤ a)
    (s : KilledState p) (estimates : Fin (replicas p) → JointSpace p) :
    potential p I a (killedNext p I s estimates) ≤ reward p I a s estimates := by
  classical
  by_cases hn : live p I (killedNext p I s estimates)
  · have hs := ((killedNext_live p I s estimates).mp hn).1
    simp only [potential, hn, ↓reduceIte, reward, hs]
    change (∏ i, (‖(nextState p s.2 estimates).2.2.1 i -
      mean p I (nextState p s.2 estimates).2.1‖ ^ 2 + precision p ^ 2 / 576 + a)) ≤ _
    rw [next_estimates, StochasticMfcqPath.next_previous]
  · simp only [potential, hn, ↓reduceIte]
    exact reward_nonneg p I a ha s estimates

lemma measurable_mean (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Measurable (mean p I) := by
  have hc : Measurable I.c := by
    have he : I.c = fun x => WithLp.toLp 2 (fun i => I.c x i) := rfl
    rw [he]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin p.m => ℝ)).measurable.comp
    exact Measurable.of_eval (fun i => (continuous_constraint p I H i).measurable)
  have hJ : Measurable I.J := by
    have he : I.J = fun x => WithLp.toLp 2 (fun i => I.J x i) := rfl
    rw [he]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin p.m => p.E)).measurable.comp
    exact Measurable.of_eval (fun i => (continuous_jacobian_row p I hp H i).measurable)
  exact (jointEquiv p).continuous.measurable.comp
    ((continuous_gradient p I hp H).measurable.prodMk (hc.prodMk hJ))

lemma measurableSet_live (p : Params) (I : Problem p) (H : Regularity p I) :
    MeasurableSet {s | live p I s} :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((measurableSet_validQueryState p I H).preimage measurable_snd)

lemma measurable_potential (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (a : ℝ) : Measurable (potential p I a) := by
  classical
  unfold potential
  apply Measurable.ite (measurableSet_live p I H) ?_ measurable_const
  apply Finset.measurable_prod
  intro i _
  exact ((((measurable_pi_apply i).comp measurable_snd.snd.snd.fst).sub
    ((measurable_mean p I hp H).comp measurable_snd.snd.fst)).norm.pow_const 2).add_const _ |>.add_const a

lemma measurable_reward (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (a : ℝ) : Measurable (Function.uncurry (reward p I a)) := by
  classical
  unfold reward
  apply Measurable.ite ((measurableSet_live p I H).preimage measurable_fst) ?_ measurable_const
  apply Finset.measurable_prod
  intro i _
  exact ((((measurable_pi_apply i).comp measurable_snd).sub
    ((measurable_mean p I hp H).comp measurable_fst.snd.fst)).norm.pow_const 2).add_const _ |>.add_const a

lemma measurable_killedNext (p : Params) (I : Problem p) (H : Regularity p I) :
    Measurable (Function.uncurry (killedNext p I)) := by
  classical
  have hn : Measurable (fun z : KilledState p × (Fin (replicas p) → JointSpace p) =>
      nextState p z.1.2 z.2) :=
    (measurable_nextState p).comp (measurable_fst.snd.prodMk measurable_snd)
  have hg : MeasurableSet {z : KilledState p × (Fin (replicas p) → JointSpace p) |
      live p I z.1 ∧ validQueryState p I (nextState p z.1.2 z.2)} :=
    ((measurableSet_live p I H).preimage measurable_fst).inter
      ((measurableSet_validQueryState p I H).preimage hn)
  have hd : Measurable (fun z : KilledState p × (Fin (replicas p) → JointSpace p) =>
      decide (live p I z.1 ∧ validQueryState p I (nextState p z.1.2 z.2))) := by
    convert (Measurable.ite hg measurable_const measurable_const : Measurable
      (fun z : KilledState p × (Fin (replicas p) → JointSpace p) =>
        if live p I z.1 ∧ validQueryState p I (nextState p z.1.2 z.2) then true else false)) using 1
    funext z
    split_ifs <;> simp_all
  exact hd.prodMk hn

lemma potential_nonneg (p : Params) (I : Problem p) (a : ℝ) (ha : 0 ≤ a)
    (s : KilledState p) : 0 ≤ potential p I a s := by
  classical
  unfold potential
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => by positivity)
  · exact le_rfl

noncomputable def incrementEstimates (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (n : ℕ) (s : State p) (ξ : Fin (replicas p) → Fin n → p.Ω) :
    Fin (replicas p) → JointSpace p := fun i =>
  (1 / (n : ℝ)) • ∑ j, (observation p g v D s.1 (ξ i j) -
    observation p g v D s.2.1 (ξ i j)) + s.2.2.1 i

lemma increment_reward_bound (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) (s : KilledState p) :
    Integrable (fun ξ => reward p I a s (incrementEstimates p g v D n s.2 ξ))
      (Measure.pi fun _ : Fin (replicas p) => Measure.pi fun _ : Fin n => (P : Measure p.Ω)) ∧
    (∫ ξ, reward p I a s (incrementEstimates p g v D n s.2 ξ)
      ∂Measure.pi (fun _ : Fin (replicas p) => Measure.pi fun _ : Fin n => (P : Measure p.Ω))) ≤
      potential p I (a + p.L ^ 2 * stepSize p ^ 2 / n) s := by
  classical
  by_cases hs : live p I s
  · have hx := hs.2.1
    have hy := hs.2.2.1
    have hd := hs.2.2.2
    have hxI := observation_integrable p I g v D P H s.2.1 hx
    have hyI := observation_integrable p I g v D P H s.2.2.1 hy
    have hm := observation_measurable p I g v D P H
    have hmean : (∫ ω, observation p g v D s.2.1 ω - observation p g v D s.2.2.1 ω
        ∂(P : Measure p.Ω)) = mean p I s.2.1 - mean p I s.2.2.1 := by
      rw [integral_sub hxI hyI, observation_mean p I g v D P H _ hx,
        observation_mean p I g v D P H _ hy]
    have hv := centered_difference_moment p I g v D P H s.2.1 s.2.2.1 hx hy
    have hd0 : 0 ≤ stepSize p := (norm_nonneg _).trans hd
    have hvar := hv.2.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hd0).mpr hd) (sq_nonneg p.L))
    have hb := AdaptiveReplicaMoments.independent_batch_product_step
      (fun ω => observation p g v D s.2.1 ω - observation p g v D s.2.2.1 ω)
      ((hm.comp measurable_prodMk_left).sub (hm.comp measurable_prodMk_left))
      (hxI.sub hyI) (mean p I s.2.1 - mean p I s.2.2.1) hmean hv.1
      (p.L ^ 2 * stepSize p ^ 2) hvar n hn
      (fun i => s.2.2.2.1 i - mean p I s.2.2.1) (precision p ^ 2 / 576 + a) (by positivity)
    have he : (fun ξ => reward p I a s (incrementEstimates p g v D n s.2 ξ)) =
        fun ξ => ∏ i, (‖(s.2.2.2.1 i - mean p I s.2.2.1) +
          ((1 / (n : ℝ)) • ∑ j, (observation p g v D s.2.1 (ξ i j) -
            observation p g v D s.2.2.1 (ξ i j)) -
            (mean p I s.2.1 - mean p I s.2.2.1))‖ ^ 2 + (precision p ^ 2 / 576 + a)) := by
      funext ξ
      simp only [reward, hs, ↓reduceIte, incrementEstimates]
      apply Finset.prod_congr rfl
      intro i _
      have he : (1 / (n : ℝ)) • ∑ j, (observation p g v D s.2.1 (ξ i j) -
          observation p g v D s.2.2.1 (ξ i j)) + s.2.2.2.1 i - mean p I s.2.1 =
          (s.2.2.2.1 i - mean p I s.2.2.1) +
          ((1 / (n : ℝ)) • ∑ j, (observation p g v D s.2.1 (ξ i j) -
            observation p g v D s.2.2.1 (ξ i j)) -
            (mean p I s.2.1 - mean p I s.2.2.1)) := by abel
      rw [he]
      ring
    rw [he]
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    simp only [potential, hs, ↓reduceIte]
    apply Finset.prod_congr rfl
    intro i _
    ring
  · simp [reward, potential, hs]

noncomputable def resetEstimates (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (n : ℕ) (s : State p) (ξ : Fin (replicas p) → Fin n → p.Ω) :
    Fin (replicas p) → JointSpace p := fun i =>
  (1 / (n : ℝ)) • ∑ j, observation p g v D s.1 (ξ i j)

lemma reset_reward_bound (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) (s : KilledState p) :
    Integrable (fun ξ => reward p I a s (resetEstimates p g v D n s.2 ξ))
      (Measure.pi fun _ : Fin (replicas p) => Measure.pi fun _ : Fin n => (P : Measure p.Ω)) ∧
    (∫ ξ, reward p I a s (resetEstimates p g v D n s.2 ξ)
      ∂Measure.pi (fun _ : Fin (replicas p) => Measure.pi fun _ : Fin n => (P : Measure p.Ω))) ≤
      (p.σ ^ 2 / n + precision p ^ 2 / 576 + a) ^ replicas p := by
  classical
  by_cases hs : live p I s
  · have hx := hs.2.1
    have hm : Measurable (observation p g v D s.2.1) :=
      (observation_measurable p I g v D P H).comp measurable_prodMk_left
    have hv := observation_variance p I g v D P H _ hx
    have hb := AdaptiveReplicaMoments.independent_batch_product_step
      (observation p g v D s.2.1) hm (observation_integrable p I g v D P H _ hx)
      (mean p I s.2.1) (observation_mean p I g v D P H _ hx) hv.1
      (p.σ ^ 2) hv.2 n hn (fun _ : Fin (replicas p) => (0 : JointSpace p))
      (precision p ^ 2 / 576 + a) (by positivity)
    simpa [reward, hs, resetEstimates, add_assoc] using hb
  · simp only [reward, hs, ↓reduceIte, integral_zero]
    exact ⟨integrable_const _, by positivity⟩

lemma reset_epoch_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (k : ℕ) (hk : k ≤ epochLength p)
    (s : KilledState p) :
    (∫ ξ, reward p I (k * (p.L ^ 2 * stepSize p ^ 2 / incrementBatch p)) s
      (resetEstimates p g v D (resetBatch p) s.2 ξ)
      ∂Measure.pi (fun _ : Fin (replicas p) =>
        Measure.pi fun _ : Fin (resetBatch p) => (P : Measure p.Ω))) ≤
      (2 * (precision p ^ 2 / 576)) ^ replicas p := by
  have hb := reset_reward_bound p I g v D P H (resetBatch p)
    (StochasticMfcqTuning.batch_sizes_positive p).2.1
    (k * (p.L ^ 2 * stepSize p ^ 2 / incrementBatch p)) (by positivity) s
  apply hb.2.trans
  apply pow_le_pow_left₀ (by positivity)
  linarith [StochasticMfcqTuning.epoch_variance_bound p hp k hk]

lemma measurable_incrementEstimates (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (n : ℕ) :
    Measurable (Function.uncurry (incrementEstimates p g v D n)) := by
  have hm := observation_measurable p I g v D P H
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : State p × (Fin (replicas p) → Fin n → p.Ω) =>
    (1 / (n : ℝ)) • ∑ j, (observation p g v D z.1.1 (z.2 i j) -
      observation p g v D z.1.2.1 (z.2 i j)) + z.1.2.2.1 i)
  apply Measurable.add ?_ (by fun_prop)
  refine Measurable.const_smul (g := fun z : State p × (Fin (replicas p) → Fin n → p.Ω) =>
    ∑ j, (observation p g v D z.1.1 (z.2 i j) - observation p g v D z.1.2.1 (z.2 i j)))
    ?_ (1 / (n : ℝ))
  apply Finset.measurable_sum
  intro j _
  exact (hm.comp (measurable_fst.fst.prodMk (by fun_prop))).sub
    (hm.comp (measurable_fst.snd.fst.prodMk (by fun_prop)))

lemma measurable_resetEstimates (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (n : ℕ) :
    Measurable (Function.uncurry (resetEstimates p g v D n)) := by
  have hm := observation_measurable p I g v D P H
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : State p × (Fin (replicas p) → Fin n → p.Ω) =>
    (1 / (n : ℝ)) • ∑ j, observation p g v D z.1.1 (z.2 i j))
  refine Measurable.const_smul (g := fun z : State p × (Fin (replicas p) → Fin n → p.Ω) =>
    ∑ j, observation p g v D z.1.1 (z.2 i j)) ?_ (1 / (n : ℝ))
  apply Finset.measurable_sum
  intro j _
  exact hm.comp (measurable_fst.fst.prodMk (by fun_prop))

lemma post_update_integral_le {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (H : Regularity p I)
    (Q : Measure Ξ) (a : ℝ) (ha : 0 ≤ a) (s : KilledState p)
    (estimates : Ξ → Fin (replicas p) → JointSpace p) (he : Measurable estimates)
    (hi : Integrable (fun ξ => reward p I a s (estimates ξ)) Q) :
    Integrable (fun ξ => potential p I a (killedNext p I s (estimates ξ))) Q ∧
    (∫ ξ, potential p I a (killedNext p I s (estimates ξ)) ∂Q) ≤
      ∫ ξ, reward p I a s (estimates ξ) ∂Q := by
  have hm : Measurable (fun ξ => potential p I a (killedNext p I s (estimates ξ))) :=
    (measurable_potential p I hp H a).comp
    ((measurable_killedNext p I H).comp (measurable_const.prodMk he))
  have hpost : Integrable (fun ξ => potential p I a (killedNext p I s (estimates ξ))) Q := by
    apply hi.mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg p I a ha _)]
    exact potential_next_le_reward p I a ha s (estimates ξ)
  exact ⟨hpost, integral_mono hpost hi (fun ξ => potential_next_le_reward p I a ha s (estimates ξ))⟩

lemma small_reward_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (a : ℝ) (ha : 0 ≤ a) (s : KilledState p) (hs : live p I s)
    (estimates : Fin (replicas p) → JointSpace p)
    (hr : reward p I a s estimates < (8 * (precision p ^ 2 / 576)) ^ replicas p) :
    StochasticMfcqPath.estimateAccurate p I s.2.1 (robustEstimate p estimates) := by
  classical
  apply StochasticMfcqEstimator.majority_accurate p I hp s.2.1 estimates
  by_contra hgood
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (replicas p))))
    (p := fun i => ‖estimates i - mean p I s.2.1‖ ≤ (2 * precision p) / 6)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  have hbad : replicas p ≤ 2 * (Finset.univ.filter (fun i =>
      (2 * precision p) / 6 < ‖estimates i - mean p I s.2.1‖)).card := by
    change ¬ replicas p < 2 * (Finset.univ.filter (fun i =>
      ‖estimates i - mean p I s.2.1‖ ≤ (2 * precision p) / 6)).card at hgood
    omega
  have hcard : (Finset.univ.filter (fun i =>
      (2 * precision p) / 6 < ‖estimates i - mean p I s.2.1‖)).card ≤
      (Finset.univ.filter (fun i => 64 * (precision p ^ 2 / 576) ≤
        ‖estimates i - mean p I s.2.1‖ ^ 2)).card := by
    apply Finset.card_le_card
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hn := (Finset.mem_filter.mp hi).2
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (2 * precision p) / 6)
      (norm_nonneg (estimates i - mean p I s.2.1))).mpr hn.le
    nlinarith
  have hl := AdaptiveReplicaProbability.scaled_majority_product_lower
    (fun i => ‖estimates i - mean p I s.2.1‖ ^ 2) (fun i => sq_nonneg _)
    (precision p ^ 2 / 576) a (by positivity) ha (by omega)
  have hl' : (8 * (precision p ^ 2 / 576)) ^ replicas p ≤ reward p I a s estimates := by
    simpa only [reward, hs, ↓reduceIte] using hl
  exact (not_le_of_gt hr) hl'

end LongTails.Proofs.StochasticMfcqEpoch
