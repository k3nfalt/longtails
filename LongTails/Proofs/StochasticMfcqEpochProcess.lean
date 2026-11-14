import LongTails.Proofs.StochasticMfcqEpoch

open MeasureTheory

namespace LongTails.Proofs.StochasticMfcqEpochProcess

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open StochasticMfcqEpoch StochasticMfcqOracle

noncomputable abbrev size (p : Params) (t : ℕ) : ℕ :=
  if t = 0 then resetBatch p else incrementBatch p

noncomputable abbrev cost (p : Params) (t : ℕ) : ℕ := replicas p * size p t

noncomputable def matrix (p : Params) (t : ℕ) (ξ : Fin (cost p t) → p.Ω) :
    Fin (replicas p) → Fin (size p t) → p.Ω := fun i j => ξ (finProdFinEquiv (i, j))

noncomputable def groupedEstimates (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : State p) (ξ : Fin (replicas p) → Fin (size p t) → p.Ω) :
    Fin (replicas p) → JointSpace p :=
  if t = 0 then resetEstimates p g v D (size p t) s ξ
  else incrementEstimates p g v D (size p t) s ξ

noncomputable def estimates (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : State p) (ξ : Fin (cost p t) → p.Ω) : Fin (replicas p) → JointSpace p :=
  groupedEstimates p g v D t s (matrix p t ξ)

noncomputable def variance (p : Params) : ℝ := p.L ^ 2 * stepSize p ^ 2 / incrementBatch p

noncomputable def shift (p : Params) (t : ℕ) : ℝ := ((epochLength p - (t + 1) : ℕ) : ℝ) * variance p

noncomputable def processStep (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : KilledState p) (ξ : Fin (cost p t) → p.Ω) : KilledState p :=
  if t < epochLength p then killedNext p I s (estimates p g v D t s.2 ξ) else s

noncomputable def processReward (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : KilledState p) (ξ : Fin (cost p t) → p.Ω) : ℝ :=
  if t < epochLength p then reward p I (shift p t) s (estimates p g v D t s.2 ξ) else 0

noncomputable def processPotential (p : Params) (I : Problem p) (t : ℕ) (s : KilledState p) : ℝ :=
  if t = 0 then (2 * (precision p ^ 2 / 576)) ^ replicas p
  else if t < epochLength p then potential p I (((epochLength p - t : ℕ) : ℝ) * variance p) s else 0

lemma shift_nonneg (p : Params) (t : ℕ) : 0 ≤ shift p t := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))

lemma matrix_law (p : Params) (P : ProbabilityMeasure p.Ω) (t : ℕ) :
    MeasurePreserving (matrix p t)
      (Measure.pi fun _ : Fin (cost p t) => (P : Measure p.Ω))
      (Measure.pi fun _ : Fin (replicas p) => Measure.pi fun _ : Fin (size p t) => (P : Measure p.Ω)) :=
  AdaptiveReplicaMoments.replica_blocks_law (P : Measure p.Ω) (replicas p) (size p t)

lemma measurable_groupedEstimates (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) :
    Measurable (Function.uncurry (groupedEstimates p g v D t)) := by
  unfold groupedEstimates
  split_ifs
  · exact measurable_resetEstimates p I g v D P H (size p t)
  · exact measurable_incrementEstimates p I g v D P H (size p t)

lemma measurable_estimates (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) :
    Measurable (Function.uncurry (estimates p g v D t)) := by
  have hm : Measurable (matrix p t) := (matrix_law p P t).measurable
  have hpair : Measurable (fun z : State p × (Fin (cost p t) → p.Ω) =>
      (z.1, matrix p t z.2)) := measurable_fst.prodMk (hm.comp measurable_snd)
  change Measurable (fun z : State p × (Fin (cost p t) → p.Ω) =>
    groupedEstimates p g v D t z.1 (matrix p t z.2))
  have hc : Measurable (Function.uncurry (groupedEstimates p g v D t) ∘
      (fun z : State p × (Fin (cost p t) → p.Ω) => (z.1, matrix p t z.2))) :=
    (measurable_groupedEstimates p I g v D P H t).comp hpair
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using hc

lemma measurable_processStep (p : Params) (I : Problem p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) :
    Measurable (Function.uncurry (processStep p I g v D t)) := by
  unfold processStep
  split_ifs
  · exact (measurable_killedNext p I R).comp (measurable_fst.prodMk
      ((measurable_estimates p I g v D P H t).comp (measurable_fst.snd.prodMk measurable_snd)))
  · exact measurable_fst

lemma measurable_processReward (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) :
    Measurable (Function.uncurry (processReward p I g v D t)) := by
  unfold processReward
  split_ifs
  · exact (measurable_reward p I hp R (shift p t)).comp (measurable_fst.prodMk
      ((measurable_estimates p I g v D P H t).comp (measurable_fst.snd.prodMk measurable_snd)))
  · exact measurable_const

lemma processReward_nonneg (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : KilledState p) (ξ : Fin (cost p t) → p.Ω) :
    0 ≤ processReward p I g v D t s ξ := by
  unfold processReward
  split_ifs
  · exact reward_nonneg p I _ (shift_nonneg p t) _ _
  · exact le_rfl

lemma next_potential_le_reward (p : Params) (I : Problem p) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (t : ℕ) (s : KilledState p) (ξ : Fin (cost p t) → p.Ω) :
    processPotential p I (t + 1) (processStep p I g v D t s ξ) ≤
      processReward p I g v D t s ξ := by
  by_cases ht : t + 1 < epochLength p
  · have ht' : t < epochLength p := by omega
    simpa [processPotential, processStep, processReward, ht, ht', shift] using
      potential_next_le_reward p I (shift p t) (shift_nonneg p t) s (estimates p g v D t s.2 ξ)
  · simp only [processPotential, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, ht]
    exact processReward_nonneg p I g v D t s ξ

lemma grouped_reward_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) (ht : t < epochLength p) (s : KilledState p) :
    Integrable (fun ξ => reward p I (shift p t) s (groupedEstimates p g v D t s.2 ξ))
      (Measure.pi fun _ : Fin (replicas p) => Measure.pi fun _ : Fin (size p t) => (P : Measure p.Ω)) ∧
    (∫ ξ, reward p I (shift p t) s (groupedEstimates p g v D t s.2 ξ)
      ∂Measure.pi (fun _ : Fin (replicas p) => Measure.pi fun _ : Fin (size p t) => (P : Measure p.Ω))) ≤
      processPotential p I t s := by
  have hn : 0 < size p t := by
    unfold size
    split_ifs
    · exact (StochasticMfcqTuning.batch_sizes_positive p).2.1
    · exact (StochasticMfcqTuning.batch_sizes_positive p).2.2.1
  by_cases h0 : t = 0
  · have hb := reset_reward_bound p I g v D P H (size p t) hn (shift p t) (shift_nonneg p t) s
    have hnum : (p.σ ^ 2 / size p t + precision p ^ 2 / 576 + shift p t) ^ replicas p ≤
        (2 * (precision p ^ 2 / 576)) ^ replicas p := by
      have hs := shift_nonneg p t
      apply pow_le_pow_left₀ (by positivity)
      have hv := StochasticMfcqTuning.epoch_variance_bound p hp (epochLength p - 1) (by omega)
      subst t
      simp only [size, ↓reduceIte, shift, zero_add, variance] at *
      linarith
    refine ⟨?_, ?_⟩
    · simpa only [groupedEstimates, h0, ↓reduceIte] using hb.1
    · simpa only [groupedEstimates, h0, ↓reduceIte, processPotential] using hb.2.trans hnum
  · have hb := increment_reward_bound p I g v D P H (size p t) hn (shift p t) (shift_nonneg p t) s
    have he : shift p t + p.L ^ 2 * stepSize p ^ 2 / size p t =
        ((epochLength p - t : ℕ) : ℝ) * variance p := by
      have hc : epochLength p - t = (epochLength p - (t + 1)) + 1 := by omega
      rw [hc]
      simp only [shift, Nat.cast_add, Nat.cast_one, variance, size, h0, ↓reduceIte]
      ring
    simp only [he] at hb
    simpa only [groupedEstimates, h0, ↓reduceIte, processPotential, ht] using hb

lemma matrix_integral (p : Params) (P : ProbabilityMeasure p.Ω) (t : ℕ)
    (F : (Fin (replicas p) → Fin (size p t) → p.Ω) → ℝ) (hF : Measurable F) :
    (∫ ξ, F (matrix p t ξ) ∂Measure.pi (fun _ : Fin (cost p t) => (P : Measure p.Ω))) =
      ∫ ξ, F ξ ∂Measure.pi (fun _ : Fin (replicas p) =>
        Measure.pi fun _ : Fin (size p t) => (P : Measure p.Ω)) := by
  have hl := matrix_law p P t
  have he := integral_map (μ := Measure.pi fun _ : Fin (cost p t) => (P : Measure p.Ω))
    hl.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hl.map_eq] at he
  exact he.symm

lemma processPotential_nonneg (p : Params) (I : Problem p) (t : ℕ) (s : KilledState p) :
    0 ≤ processPotential p I t s := by
  unfold processPotential
  split_ifs
  · positivity
  · apply potential_nonneg
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
  · exact le_rfl

lemma measurable_processPotential (p : Params) (I : Problem p) (hp : spec.valid p)
    (R : Regularity p I) (t : ℕ) : Measurable (processPotential p I t) := by
  unfold processPotential
  split_ifs
  · exact measurable_const
  · exact measurable_potential p I hp R _
  · exact measurable_const

lemma processReward_bound (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) (s : KilledState p) :
    Integrable (processReward p I g v D t s)
      (Measure.pi fun _ : Fin (cost p t) => (P : Measure p.Ω)) ∧
    (∫ ξ, processReward p I g v D t s ξ
      ∂Measure.pi (fun _ : Fin (cost p t) => (P : Measure p.Ω))) ≤ processPotential p I t s := by
  change Integrable (fun ξ => processReward p I g v D t s ξ) _ ∧ _
  by_cases ht : t < epochLength p
  · let F := fun ξ => reward p I (shift p t) s (groupedEstimates p g v D t s.2 ξ)
    have hG : Measurable (fun ξ => groupedEstimates p g v D t s.2 ξ) :=
      (measurable_groupedEstimates p I g v D P H t).of_uncurry_left
    have hF : Measurable F :=
      (measurable_reward p I hp R (shift p t)).of_uncurry_left.comp hG
    have hb := grouped_reward_bound p I hp g v D P H t ht s
    have hi := (matrix_law p P t).integrable_comp_of_integrable hb.1
    have he := matrix_integral p P t F hF
    simp only [processReward, ht, ↓reduceIte, estimates]
    refine ⟨?_, he.trans_le hb.2⟩
    simpa only [Function.comp_def] using hi
  · have h0 : t ≠ 0 := by
      have := (StochasticMfcqTuning.batch_sizes_positive p).1
      omega
    simp [processReward, ht, processPotential, h0]

lemma processStep_bound (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (t : ℕ) (s : KilledState p) :
    Integrable (fun ξ => processPotential p I (t + 1) (processStep p I g v D t s ξ))
      (Measure.pi fun _ : Fin (cost p t) => (P : Measure p.Ω)) ∧
    (∫ ξ, processPotential p I (t + 1) (processStep p I g v D t s ξ)
      ∂Measure.pi (fun _ : Fin (cost p t) => (P : Measure p.Ω))) ≤ processPotential p I t s := by
  have hb := processReward_bound p I hp R g v D P H t s
  have hm : Measurable (fun ξ => processPotential p I (t + 1) (processStep p I g v D t s ξ)) :=
    (measurable_processPotential p I hp R (t + 1)).comp
      ((measurable_processStep p I R g v D P H t).comp measurable_prodMk_left)
  have hi : Integrable (fun ξ => processPotential p I (t + 1) (processStep p I g v D t s ξ))
      (Measure.pi fun _ : Fin (cost p t) => (P : Measure p.Ω)) := by
    apply hb.1.mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (processPotential_nonneg p I _ _)]
    exact next_potential_le_reward p I g v D t s ξ
  refine ⟨hi, (integral_mono hi hb.1 (fun ξ => next_potential_le_reward p I g v D t s ξ)).trans hb.2⟩

lemma epoch_reward_integral_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (R : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (n : ℕ) (s : KilledState p) :
    Integrable (AdaptiveReplicaProcess.blockReward (cost p) (processStep p I g v D)
      (processReward p I g v D) n 0 s) (Measure.infinitePi fun _ : ℕ => (P : Measure p.Ω)) ∧
    (∫ ξ, AdaptiveReplicaProcess.blockReward (cost p) (processStep p I g v D)
      (processReward p I g v D) n 0 s ξ ∂Measure.infinitePi (fun _ : ℕ => (P : Measure p.Ω))) ≤
      (2 * (precision p ^ 2 / 576)) ^ replicas p := by
  have hb := AdaptiveReplicaProcess.blockReward_integral_bound (P : Measure p.Ω) (cost p)
    (processStep p I g v D) (measurable_processStep p I R g v D P H) (processPotential p I)
    (fun t s => (processStep_bound p I hp R g v D P H t s).1)
    (fun t s => (processStep_bound p I hp R g v D P H t s).2)
    (processReward p I g v D) (measurable_processReward p I hp R g v D P H)
    (processReward_nonneg p I g v D)
    (fun t s => (processReward_bound p I hp R g v D P H t s).1)
    (fun t s => (processReward_bound p I hp R g v D P H t s).2) n 0 s
  simpa only [processPotential, ↓reduceIte] using hb

lemma random_entry_reward_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) (I : Problem p) (hp : spec.valid p) (R : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (P : ProbabilityMeasure p.Ω)
    (H : OracleConditions p I g v D P) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ P Q)
    (m n : ℕ) (enter : (Fin m → p.Ω) → KilledState p) (hm : Measurable enter) :
    Q {ω | (8 * (precision p ^ 2 / 576)) ^ replicas p ≤
      AdaptiveReplicaProcess.blockReward (cost p) (processStep p I g v D)
        (processReward p I g v D) n 0 (enter (fun i => ξ i ω)) (fun k => ξ (m + k) ω)} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ replicas p) := by
  let F := AdaptiveReplicaProcess.blockReward (cost p) (processStep p I g v D)
    (processReward p I g v D) n 0
  have hF : Measurable (Function.uncurry F) :=
    AdaptiveReplicaProcess.blockReward_measurable (cost p) (processStep p I g v D)
      (measurable_processStep p I R g v D P H) (processReward p I g v D)
      (measurable_processReward p I hp R g v D P H) n 0
  have hF0 : ∀ s ω, 0 ≤ F s ω := fun s ω =>
    AdaptiveReplicaProcess.blockReward_nonneg (cost p) (processStep p I g v D)
      (processReward p I g v D) (processReward_nonneg p I g v D) n 0 s ω
  have hb := AdaptiveReplicaProcess.prefix_uniform_integral_bound (P : Measure p.Ω) Q ξ hξ
    m enter hm F hF hF0 ((2 * (precision p ^ 2 / 576)) ^ replicas p)
    (fun s => (epoch_reward_integral_bound p I hp R g v D P H n s).1)
    (fun s => (epoch_reward_integral_bound p I hp R g v D P H n s).2)
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  exact AdaptiveReplicaProbability.scaled_reward_probability _ hb.1
    (fun ω => hF0 _ _) (precision p ^ 2 / 576) (by positivity) (replicas p) hb.2

end LongTails.Proofs.StochasticMfcqEpochProcess
