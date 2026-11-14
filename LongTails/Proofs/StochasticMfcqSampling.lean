import LongTails.Proofs.StochasticMfcqEpochProcess
import LongTails.Proofs.StochasticMfcqExecution

open MeasureTheory
namespace LongTails.Proofs.StochasticMfcqSampling
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticMfcqEpoch StochasticMfcqOracle StochasticMfcqExecution

noncomputable def samplePrefix (p : Params) (k : ℕ) : ℕ :=
  slotCalls (fun j => batchSize p j * replicas p) k 0

noncomputable def slotEstimates (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (k : ℕ) (s : State p) (ξ : ℕ → p.Ω) : Fin (replicas p) → JointSpace p :=
  fun i => (batchSize p k : ℝ)⁻¹ • ∑ j : Fin (batchSize p k),
    (if k % epochLength p = 0 then
      observation p g v D s.1 (ξ (samplePrefix p k + batchSize p k * i.val + j.val))
    else observation p g v D s.1 (ξ (samplePrefix p k + batchSize p k * i.val + j.val)) -
      observation p g v D s.2.1 (ξ (samplePrefix p k + batchSize p k * i.val + j.val))) +
    if k % epochLength p = 0 then 0 else s.2.2.1 i

noncomputable def killedStateAt (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ : ℕ → p.Ω) : ℕ → KilledState p
  | 0 => (true, initial p)
  | k + 1 => killedNext p I (killedStateAt p I g v D ξ k)
      (slotEstimates p g v D k (killedStateAt p I g v D ξ k).2 ξ)

lemma killedStateAt_actual (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ : ℕ → p.Ω) (k : ℕ) :
    (killedStateAt p I g v D ξ k).2 = stateAt p
      (fun n z => ((g z.1 (ξ n), v z.1 (ξ n), D z.1 (ξ n)),
        (g z.2 (ξ n), v z.2 (ξ n), D z.2 (ξ n)))) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [killedStateAt, killedNext, stateAt_succ]
    simp only [ih, sampleValue]
    congr 1

lemma measurable_slotEstimates (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (k : ℕ) :
    Measurable (Function.uncurry (slotEstimates p g v D k)) := by
  have hm := observation_measurable p I g v D P H
  apply Measurable.of_eval
  intro i
  unfold Function.uncurry slotEstimates
  apply Measurable.add
  · refine Measurable.const_smul (g := fun z : State p × (ℕ → p.Ω) =>
      ∑ j : Fin (batchSize p k), if k % epochLength p = 0 then
        observation p g v D z.1.1 (z.2 (samplePrefix p k + batchSize p k * i.val + j.val))
      else observation p g v D z.1.1 (z.2 (samplePrefix p k + batchSize p k * i.val + j.val)) -
        observation p g v D z.1.2.1 (z.2 (samplePrefix p k + batchSize p k * i.val + j.val)))
      ?_ ((batchSize p k : ℝ)⁻¹)
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact hm.comp (measurable_fst.fst.prodMk (by fun_prop))
    · exact (hm.comp (measurable_fst.fst.prodMk (by fun_prop))).sub
        (hm.comp (measurable_fst.snd.fst.prodMk (by fun_prop)))
  · split_ifs <;> fun_prop

lemma measurable_killedStateAt (p : Params) (I : Problem p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (k : ℕ) :
    Measurable (fun ξ => killedStateAt p I g v D ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hs : Measurable (fun ξ : ℕ → p.Ω => ((killedStateAt p I g v D ξ k).2, ξ)) :=
      ih.snd.prodMk measurable_id
    have he := (measurable_slotEstimates p I g v D P H k).comp hs
    have hc := (measurable_killedNext p I R).comp (ih.prodMk he)
    simpa only [Function.comp_def, Function.uncurry_apply_pair, killedStateAt] using hc

lemma samplePrefix_succ (p : Params) (k : ℕ) :
    samplePrefix p (k + 1) = samplePrefix p k + batchSize p k * replicas p :=
  StochasticEnvelopeExecution.slotCalls_prefix_succ _ k

lemma slot_index_lt (p : Params) (k : ℕ) (i : Fin (replicas p))
    (j : Fin (batchSize p k)) :
    samplePrefix p k + batchSize p k * i.val + j.val < samplePrefix p (k + 1) := by
  rw [samplePrefix_succ]
  have hb : batchSize p k * i.val + j.val < batchSize p k * replicas p := by
    calc
      _ < batchSize p k * i.val + batchSize p k := Nat.add_lt_add_left j.isLt _
      _ = batchSize p k * (i.val + 1) := by ring
      _ ≤ batchSize p k * replicas p := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt i.isLt)
  omega

lemma killedStateAt_prefix_congr (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ ζ : ℕ → p.Ω) (k : ℕ) (h : ∀ j < samplePrefix p k, ξ j = ζ j) :
    killedStateAt p I g v D ξ k = killedStateAt p I g v D ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he := ih (fun j hj => h j (by rw [samplePrefix_succ]; omega))
    simp only [killedStateAt, he]
    congr 1
    funext i
    unfold slotEstimates
    congr 1
    apply congrArg ((batchSize p k : ℝ)⁻¹ • ·)
    apply Finset.sum_congr rfl
    intro j _
    rw [h _ (slot_index_lt p k i j)]

noncomputable def enterState (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (a : p.Ω) (k : ℕ) (z : Fin (samplePrefix p k) → p.Ω) : KilledState p :=
  killedStateAt p I g v D (fun j => if h : j < samplePrefix p k then z ⟨j, h⟩ else a) k

lemma enterState_eq (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (a : p.Ω) (k : ℕ) (ξ : ℕ → p.Ω) :
    enterState p I g v D a k (fun i => ξ i) = killedStateAt p I g v D ξ k := by
  apply killedStateAt_prefix_congr
  intro j hj
  simp only [dite_eq_left hj]

lemma measurable_enterState (p : Params) (I : Problem p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (a : p.Ω) (k : ℕ) :
    Measurable (enterState p I g v D a k) := by
  apply (measurable_killedStateAt p I R g v D P H k).comp
  apply Measurable.of_eval
  intro j
  split_ifs <;> fun_prop


lemma slotEstimates_epoch (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (k : ℕ) (s : State p) (ξ : ℕ → p.Ω) :
    slotEstimates p g v D k s ξ = StochasticMfcqEpochProcess.estimates p g v D
      (k % epochLength p) s (fun i => ξ (samplePrefix p k + i.val)) := by
  classical
  unfold StochasticMfcqEpochProcess.estimates StochasticMfcqEpochProcess.groupedEstimates
  unfold slotEstimates
  split_ifs with h <;> funext i <;>
    simp [h, batchSize, StochasticMfcqEpochProcess.size, resetEstimates, incrementEstimates,
      StochasticMfcqEpochProcess.matrix, finProdFinEquiv, Nat.add_comm,
      Nat.add_assoc] <;> rfl


lemma epoch_cost_eq (p : Params) (k : ℕ) :
    StochasticMfcqEpochProcess.cost p (k % epochLength p) = batchSize p k * replicas p := by
  simp only [StochasticMfcqEpochProcess.cost, StochasticMfcqEpochProcess.size, batchSize]
  exact Nat.mul_comm _ _

lemma processStep_actual (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ : ℕ → p.Ω) (k : ℕ) :
    StochasticMfcqEpochProcess.processStep p I g v D (k % epochLength p)
      (killedStateAt p I g v D ξ k) (fun i => ξ (samplePrefix p k + i.val)) =
      killedStateAt p I g v D ξ (k + 1) := by
  have ht : k % epochLength p < epochLength p :=
    Nat.mod_lt k (StochasticMfcqTuning.batch_sizes_positive p).1
  rw [StochasticMfcqEpochProcess.processStep, ite_eq_left ht, ← slotEstimates_epoch]
  rfl

noncomputable def slotReward (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ : ℕ → p.Ω) (k : ℕ) : ℝ :=
  reward p I (StochasticMfcqEpochProcess.shift p (k % epochLength p))
    (killedStateAt p I g v D ξ k)
    (slotEstimates p g v D k (killedStateAt p I g v D ξ k).2 ξ)

lemma blockReward_actual (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (ξ : ℕ → p.Ω) (n k : ℕ) (hn : k % epochLength p + n < epochLength p) :
    AdaptiveReplicaProcess.blockReward (StochasticMfcqEpochProcess.cost p)
      (StochasticMfcqEpochProcess.processStep p I g v D)
      (StochasticMfcqEpochProcess.processReward p I g v D) n (k % epochLength p)
      (killedStateAt p I g v D ξ k) (fun j => ξ (samplePrefix p k + j)) =
      slotReward p I g v D ξ (k + n) := by
  induction n generalizing k with
  | zero =>
    have ht : k % epochLength p < epochLength p := by omega
    simp only [AdaptiveReplicaProcess.blockReward, StochasticMfcqEpochProcess.processReward,
      ht, ↓reduceIte, Nat.add_zero, slotReward, slotEstimates_epoch]
  | succ n ih =>
    have ht : k % epochLength p + 1 < epochLength p := by omega
    have hmod : (k + 1) % epochLength p = k % epochLength p + 1 := by
      rw [Nat.add_mod]
      have hq : 1 < epochLength p := by omega
      rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt ht]
    rw [AdaptiveReplicaProcess.blockReward, processStep_actual, ← hmod]
    have htail : (fun j => ξ (samplePrefix p k +
        (StochasticMfcqEpochProcess.cost p (k % epochLength p) + j))) =
        (fun j => ξ (samplePrefix p (k + 1) + j)) := by
      funext j
      rw [samplePrefix_succ, epoch_cost_eq]
      congr 1
      omega
    rw [htail]
    have hh := ih (k + 1) (by rw [hmod]; omega)
    convert hh using 1
    congr 1
    omega


lemma slotReward_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ P Q) (k : ℕ) :
    Q {ω | (8 * (precision p ^ 2 / 576)) ^ replicas p ≤
      slotReward p I g v D (fun j => ξ j ω) k} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ replicas p) := by
  let a : p.Ω := Classical.choice (nonempty_of_isProbabilityMeasure (P : Measure p.Ω))
  let e := epochLength p * (k / epochLength p)
  have he : e % epochLength p = 0 := by simp [e]
  have headd : e + k % epochLength p = k := by
    have hh := Nat.mod_add_div k (epochLength p)
    omega
  have ht : k % epochLength p < epochLength p :=
    Nat.mod_lt k (StochasticMfcqTuning.batch_sizes_positive p).1
  have hb := StochasticMfcqEpochProcess.random_entry_reward_probability p I hp R g v D P H
    Q ξ hξ (samplePrefix p e) (k % epochLength p) (enterState p I g v D a e)
    (measurable_enterState p I R g v D P H a e)
  have hEq : ∀ ω, AdaptiveReplicaProcess.blockReward (StochasticMfcqEpochProcess.cost p)
      (StochasticMfcqEpochProcess.processStep p I g v D)
      (StochasticMfcqEpochProcess.processReward p I g v D) (k % epochLength p) 0
      (enterState p I g v D a e (fun i => ξ i ω)) (fun j => ξ (samplePrefix p e + j) ω) =
      slotReward p I g v D (fun j => ξ j ω) k := by
    intro ω
    rw [enterState_eq p I g v D a e (fun j => ξ j ω)]
    have hh := blockReward_actual p I g v D (fun j => ξ j ω) (k % epochLength p) e
      (by rw [he]; omega)
    simpa only [he, headd] using hh
  simpa only [hEq] using hb


lemma any_large_reward_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ P Q) :
    Q (⋃ k : Fin (outerSteps p), {ω | (8 * (precision p ^ 2 / 576)) ^ replicas p ≤
      slotReward p I g v D (fun j => ξ j ω) k}) ≤ ENNReal.ofReal p.ρ := by
  calc
    _ ≤ ∑ k : Fin (outerSteps p), Q {ω | (8 * (precision p ^ 2 / 576)) ^ replicas p ≤
        slotReward p I g v D (fun j => ξ j ω) k} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (outerSteps p), ENNReal.ofReal ((1 / 4 : ℝ) ^ replicas p) := by
      apply Finset.sum_le_sum
      intro k _
      exact slotReward_probability p I hp R g v D P H Q ξ hξ k
    _ = ENNReal.ofReal ((outerSteps p : ℝ) * (1 / 4 : ℝ) ^ replicas p) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal p.ρ := ENNReal.ofReal_le_ofReal
      (StochasticMfcqTuning.confidence_bound p hp)


lemma small_rewards_invariant (p : Params) (I : Problem p) (hp : spec.valid p)
    (R : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (ξ : ℕ → p.Ω)
    (hsmall : ∀ k < outerSteps p, slotReward p I g v D ξ k <
      (8 * (precision p ^ 2 / 576)) ^ replicas p) (k : ℕ) (hk : k ≤ outerSteps p) :
    live p I (killedStateAt p I g v D ξ k) ∧
      StochasticMfcqPath.invariant p I k (killedStateAt p I g v D ξ k).2 := by
  induction k with
  | zero =>
    refine ⟨⟨rfl, StochasticMfcqMeasurability.initial_validQueryState p I hp R⟩,
      StochasticMfcqPath.initial_invariant p I R⟩
  | succ k ih =>
    have hh := ih (by omega)
    have he := small_reward_accurate p I hp _ (StochasticMfcqEpochProcess.shift_nonneg p _)
      _ hh.1 _ (hsmall k (by omega))
    have hn := StochasticMfcqPath.next_invariant p I hp R k _ _ hh.2 he
    refine ⟨?_, hn⟩
    rw [killedStateAt, killedNext_live]
    exact ⟨hh.1, StochasticMfcqMeasurability.next_validQueryState p I hp _ _ hh.2.1 hn.1⟩


lemma measurable_slotReward (p : Params) (I : Problem p) (hp : spec.valid p)
    (R : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (k : ℕ) :
    Measurable (fun ξ => slotReward p I g v D ξ k) := by
  have hs := measurable_killedStateAt p I R g v D P H k
  have he := (measurable_slotEstimates p I g v D P H k).comp (hs.snd.prodMk measurable_id)
  have hr := (measurable_reward p I hp R (StochasticMfcqEpochProcess.shift p
    (k % epochLength p))).comp (hs.prodMk he)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq, slotReward] using hr

lemma small_rewards_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ P Q) :
    ENNReal.ofReal (1 - p.ρ) ≤ Q {ω | ∀ k < outerSteps p,
      slotReward p I g v D (fun j => ξ j ω) k < (8 * (precision p ^ 2 / 576)) ^ replicas p} := by
  let B := ⋃ k : Fin (outerSteps p), {ω | (8 * (precision p ^ 2 / 576)) ^ replicas p ≤
    slotReward p I g v D (fun j => ξ j ω) k}
  have hm : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro k
    exact measurableSet_le measurable_const
      ((measurable_slotReward p I hp R g v D P H k).comp (Measurable.of_eval hξ.measurable))
  have he : {ω | ∀ k < outerSteps p, slotReward p I g v D (fun j => ξ j ω) k <
      (8 * (precision p ^ 2 / 576)) ^ replicas p} = Bᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, B, Set.mem_iUnion, not_exists, not_le]
    exact ⟨fun h k => h k k.isLt, fun h k hk => h ⟨k, hk⟩⟩
  rw [he, measure_compl hm (measure_ne_top Q B), measure_univ]
  have hρ : 0 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.2.1.le
  rw [ENNReal.ofReal_sub 1 hρ, ENNReal.ofReal_one]
  exact tsub_le_tsub_left (any_large_reward_probability p I hp R g v D P H Q ξ hξ) 1


lemma safe_accurate_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ P Q) :
    ENNReal.ofReal (1 - p.ρ) ≤ Q {ω |
      (∀ k ≤ outerSteps p, StochasticMfcqMeasurability.validQueryState p I
        (killedStateAt p I g v D (fun j => ξ j ω) k).2) ∧
      accurate p I ((killedStateAt p I g v D (fun j => ξ j ω) (outerSteps p)).2.1,
        (killedStateAt p I g v D (fun j => ξ j ω) (outerSteps p)).2.2.2.2.2)} := by
  apply (small_rewards_probability p I hp R g v D P H Q ξ hξ).trans
  apply measure_mono
  intro ω hω
  have hh := small_rewards_invariant p I hp R g v D (fun j => ξ j ω) hω
  refine ⟨fun k hk => (hh k hk).1.2, ?_⟩
  exact StochasticMfcqPath.final_accurate p I hp R _ (hh (outerSteps p) le_rfl).2

end LongTails.Proofs.StochasticMfcqSampling
