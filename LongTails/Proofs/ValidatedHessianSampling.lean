import LongTails.Proofs.ValidatedHessianExecution
import LongTails.Proofs.GuardedHessianValidation
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.ScalarEstimatorLaw

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.ValidatedHessianExecution

namespace LongTails.Proofs.ValidatedHessianSampling

lemma finite_blocks_preserving {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K C : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun j : Fin K => fun i : Fin C => ξ (j.val * C + i.val))
      (Measure.infinitePi fun _ : ℕ => P)
      (Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin C => P) := by
  have hi := OracleTemplate.StochasticGeneralized.infinitePi_iid P
  exact (OracleTemplate.StochasticGeneralized.prefix_preserving
    (Measure.pi fun _ : Fin C => P) K).comp
    (OracleTemplate.FiniteVariance.infinite_block_law P _ hi.independent hi.marginal C)

lemma target_blocks_preserving {I Ω : Type*} [MeasurableSpace I] [MeasurableSpace Ω]
    (R : Measure I) (P : Measure Ω) [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    (K C : ℕ) :
    MeasurePreserving
      (fun w : (Fin K → I) × (ℕ → Ω) => fun j : Fin K =>
        (w.1 j, fun i : Fin C => w.2 (j.val * C + i.val)))
      ((Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P))
      (Measure.pi fun _ : Fin K => R.prod (Measure.pi fun _ : Fin C => P)) := by
  have hz := (measurePreserving_arrowProdEquivProdArrow I (Fin C → Ω) (Fin K)
    (fun _ => R) (fun _ => Measure.pi fun _ : Fin C => P)).symm
    (MeasurableEquiv.arrowProdEquivProdArrow I (Fin C → Ω) (Fin K))
  exact hz.comp ((MeasurePreserving.id (Measure.pi fun _ : Fin K => R)).prod
    (finite_blocks_preserving P K C))

noncomputable def finiteTrialPoint (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (w : Fin (c.steps + 1) × (Fin (trialCalls c) → ℝ × Ω)) : Space p :=
  let t := OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (fun t (z : ℝ × Ω) => update p c t z.1 (answer (query p c t z.1) z.2))
    (trialCalls c) (⟨p.x0, 0, 0, w.1, p.x0, true, .reset 0 0⟩ : State p c) w.2
  if t.alive then t.selected else p.x0

lemma finiteTrialPoint_eq (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    finiteTrialPoint p c answer (target, fun i => ξ i) = trialPoint p c answer target ξ := by
  simp only [finiteTrialPoint, trialPoint, HeavyTailedSospEpochIntegration.trajectory_finite]

lemma finiteTrialPoint_shift (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (offset : ℕ) :
    finiteTrialPoint p c answer (target, fun i => ξ (offset + i.val)) =
      trialPoint p c answer target (fun i => ξ (offset + i)) :=
  finiteTrialPoint_eq p c answer target (fun i => ξ (offset + i))

lemma measurable_finiteTrialPoint (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2))) :
    Measurable (finiteTrialPoint p c answer) := by
  exact (GuardedHessianMeasurable.measurable_output p c).comp
    ((OracleTemplate.GapStrongGrowth.iterateSamples_measurable hstep (trialCalls c)).comp
      (((measurable_of_finite (fun target : Fin (c.steps + 1) =>
        (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c))).comp measurable_fst).prodMk
        measurable_snd))

lemma finite_trial_law (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1)))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2))) :
    (R.prod (Measure.infinitePi fun _ : ℕ => P)).map
      (fun w => trialPoint p c answer w.1 w.2) =
    (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)).map (finiteTrialPoint p c answer) := by
  have hh := (MeasurePreserving.id R).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving P (trialCalls c))
  rw [← hh.map_eq, Measure.map_map (measurable_finiteTrialPoint p c answer hstep) hh.measurable]
  congr 1
  funext w
  exact (finiteTrialPoint_eq p c answer w.1 w.2).symm

lemma block_all_bad {I Ω : Type*} [MeasurableSpace I] [MeasurableSpace Ω]
    (R : Measure I) (P : Measure Ω) [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    (K C : ℕ) (A : Set (I × (Fin C → Ω))) (hA : MeasurableSet A) {δ : ℝ}
    (hb : (R.prod (Measure.pi fun _ : Fin C => P)).real A ≤ δ) :
    ((Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | ∀ j : Fin K, (w.1 j, fun i : Fin C => w.2 (j.val * C + i.val)) ∈ A} ≤ δ ^ K := by
  have hp := target_blocks_preserving R P K C
  have hm : MeasurableSet {w : Fin K → I × (Fin C → Ω) | ∀ j, w j ∈ A} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) hA)
  have hh := hp.measureReal_preimage hm.nullMeasurableSet
  exact hh.trans_le (GuardedHessianValidation.independent_all_bad _ K A hb)

lemma finite_trial_guarantees (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1)))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (g : Space p → Space p) (hg : Measurable g) {M r δ : ℝ}
    (hi : Integrable (fun w => ‖g (trialPoint p c answer w.1 w.2)‖ ^ 2)
      (R.prod (Measure.infinitePi fun _ : ℕ => P)))
    (hb : (∫ w, ‖g (trialPoint p c answer w.1 w.2)‖ ^ 2
      ∂R.prod (Measure.infinitePi fun _ : ℕ => P)) ≤ 9 * M ^ 2)
    (hbad : (R.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | r < ‖g (trialPoint p c answer w.1 w.2)‖} ≤ δ) :
    Integrable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ 2)
      (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) ∧
    (∫ w, ‖g (finiteTrialPoint p c answer w)‖ ^ 2
      ∂R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) ≤ 9 * M ^ 2 ∧
    (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)).real
      {w | r < ‖g (finiteTrialPoint p c answer w)‖} ≤ δ := by
  have hp := (MeasurePreserving.id R).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving P (trialCalls c))
  have hF : Measurable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ (2 : ℕ)) :=
    (hg.comp (measurable_finiteTrialPoint p c answer hstep)).norm.pow_const 2
  have hi' : Integrable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ 2)
      (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) :=
    (hp.integrable_comp hF.aestronglyMeasurable).mp (by
      simpa only [Function.comp_def, Prod.map, id_eq, finiteTrialPoint_eq] using hi)
  refine ⟨hi', ?_, ?_⟩
  · rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]
    simpa only [Function.comp_def, Prod.map, id_eq, finiteTrialPoint_eq] using hb
  · have hm : MeasurableSet {w | r < ‖g (finiteTrialPoint p c answer w)‖} :=
      measurableSet_lt measurable_const (hg.comp (measurable_finiteTrialPoint p c answer hstep)).norm
    have hh := hp.measureReal_preimage hm.nullMeasurableSet
    rw [← hh]
    simpa only [Set.preimage_ofPred_eq, Prod.map, id_eq, finiteTrialPoint_eq] using hbad

lemma measurable_blockCandidates (p : Params) (c : Config) (K : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2))) :
    Measurable (fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) =>
      blockCandidates p c K answer w.1 w.2) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact measurable_const
  · have hh := (measurable_finiteTrialPoint p c answer hstep).comp
      (show Measurable (fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) =>
        (w.1 k, fun i : Fin (trialCalls c) => w.2 (k.val * trialCalls c + i.val))) by fun_prop)
    simpa only [Function.comp_def, Function.eval, finiteTrialPoint_shift, blockCandidates, Fin.cases_succ] using hh

lemma block_trial_moment (p : Params) (c : Config) (K : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1))) [IsProbabilityMeasure R]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (g : Space p → Space p) (hg : Measurable g) {M : ℝ}
    (hi : Integrable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ 2)
      (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)))
    (hb : (∫ w, ‖g (finiteTrialPoint p c answer w)‖ ^ 2
      ∂R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) ≤ 9 * M ^ 2)
    (j : Fin K) :
    Integrable (fun w => ‖g (blockCandidates p c K answer w.1 w.2 j.succ)‖ ^ 2)
      ((Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)) ∧
    (∫ w, ‖g (blockCandidates p c K answer w.1 w.2 j.succ)‖ ^ 2
      ∂(Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)) ≤ 9 * M ^ 2 := by
  have hp := (measurePreserving_eval (fun _ : Fin K =>
    R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) j).comp
      (target_blocks_preserving R P K (trialCalls c))
  have hF : Measurable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ (2 : ℕ)) :=
    (hg.comp (measurable_finiteTrialPoint p c answer hstep)).norm.pow_const 2
  refine ⟨?_, ?_⟩
  · have hh := (hp.integrable_comp hF.aestronglyMeasurable).mpr hi
    simpa only [Function.comp_def, Function.eval, finiteTrialPoint_shift, blockCandidates, Fin.cases_succ] using hh
  · have hh : (∫ w, ‖g (finiteTrialPoint p c answer w)‖ ^ 2
        ∂R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) =
        ∫ w, ‖g (blockCandidates p c K answer w.1 w.2 j.succ)‖ ^ 2
          ∂(Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P) := by
      rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]
      simp only [Function.comp_def, Function.eval, finiteTrialPoint_shift, blockCandidates, Fin.cases_succ]
    rw [← hh]
    exact hb

lemma block_trials_failure (p : Params) (c : Config) (K : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1))) [IsProbabilityMeasure R]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (g : Space p → Space p) (hg : Measurable g) {r δ : ℝ}
    (hb : (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)).real
      {w | r < ‖g (finiteTrialPoint p c answer w)‖} ≤ δ) :
    ((Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | ∀ j : Fin K, r < ‖g (blockCandidates p c K answer w.1 w.2 j.succ)‖} ≤ δ ^ K := by
  have hh := block_all_bad R P K (trialCalls c)
    {w | r < ‖g (finiteTrialPoint p c answer w)‖}
    (measurableSet_lt measurable_const (hg.comp (measurable_finiteTrialPoint p c answer hstep)).norm) hb
  simpa only [Set.mem_ofPred_eq, finiteTrialPoint_shift, blockCandidates, Fin.cases_succ] using hh

noncomputable def finiteBlockCandidates (p : Params) (c : Config) (K : ℕ) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (w : (Fin K → Fin (c.steps + 1)) × (Fin (K * trialCalls c) → ℝ × Ω)) : Fin (K + 1) → Space p :=
  Fin.cases p.x0 (fun j => finiteTrialPoint p c answer (w.1 j, fun i =>
    w.2 ⟨j.val * trialCalls c + i.val, by
      have hh := Nat.mul_le_mul_right (trialCalls c) (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at hh
      have hi := i.isLt
      omega⟩))

lemma finiteBlockCandidates_eq (p : Params) (c : Config) (K : ℕ) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (targets : Fin K → Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    finiteBlockCandidates p c K answer (targets, fun i => ξ i.val) =
      blockCandidates p c K answer targets ξ := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  exact finiteTrialPoint_shift p c answer (targets k) ξ (k.val * trialCalls c)

lemma measurable_finiteBlockCandidates (p : Params) (c : Config) (K : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2))) :
    Measurable (finiteBlockCandidates p c K answer) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact measurable_const
  · apply (measurable_finiteTrialPoint p c answer hstep).comp
    fun_prop

lemma prefix_output_tail_preserving {I Ω V : Type*}
    [MeasurableSpace I] [MeasurableSpace Ω] [MeasurableSpace V]
    (R : Measure I) (P : Measure Ω) [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    (N : ℕ) (F : I × (Fin N → Ω) → V) (hF : Measurable F) :
    let Q := R.prod (Measure.infinitePi fun _ : ℕ => P)
    let G := fun w : I × (ℕ → Ω) => F (w.1, fun i => w.2 i.val)
    MeasurePreserving (fun w : I × (ℕ → Ω) => (G w, fun k => w.2 (N + k)))
      Q ((Q.map G).prod (Measure.infinitePi fun _ : ℕ => P)) := by
  intro Q G
  let μ := R.prod (Measure.pi fun _ : Fin N => P)
  have hs := OracleTemplate.ScalarHeavyTailEstimator.seed_prefix_tail_preserving (P := P) R N
  have hpre := measurePreserving_fst.comp hs
  have hf : MeasurePreserving F μ (μ.map F) := ⟨hF, rfl⟩
  have heq : Q.map G = μ.map F := by
    dsimp only [μ, Q]
    rw [← hpre.map_eq, Measure.map_map hF hpre.measurable]
    rfl
  rw [heq]
  exact (hf.prod (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => P))).comp hs

lemma candidates_tail_preserving (p : Params) (c : Config) (K : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1))) [IsProbabilityMeasure R]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2))) :
    let Q := (Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)
    let G := fun w => blockCandidates p c K answer w.1 w.2
    MeasurePreserving (fun w => (G w, fun k => w.2 (K * trialCalls c + k)))
      Q ((Q.map G).prod (Measure.infinitePi fun _ : ℕ => P)) := by
  intro Q G
  have hh := prefix_output_tail_preserving (Measure.pi fun _ : Fin K => R) P
    (K * trialCalls c) (finiteBlockCandidates p c K answer)
    (measurable_finiteBlockCandidates p c K answer hstep)
  simpa only [finiteBlockCandidates_eq] using hh

lemma finite_candidates_guarantees (p : Params) (c : Config) (K : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1))) [IsProbabilityMeasure R]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (g : Space p → Space p) (hg : Measurable g) {M r δ : ℝ}
    (hM : 0 ≤ M) (h0 : ‖g p.x0‖ ≤ M)
    (hi : Integrable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ 2)
      (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)))
    (hb : (∫ w, ‖g (finiteTrialPoint p c answer w)‖ ^ 2
      ∂R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) ≤ 9 * M ^ 2)
    (hbad : (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)).real
      {w | r < ‖g (finiteTrialPoint p c answer w)‖} ≤ δ) :
    let μ := (Measure.pi fun _ : Fin K => R).prod
      (Measure.pi fun _ : Fin (K * trialCalls c) => P)
    (∀ j, Integrable (fun w => ‖g (finiteBlockCandidates p c K answer w j)‖ ^ 2) μ ∧
      (∫ w, ‖g (finiteBlockCandidates p c K answer w j)‖ ^ 2 ∂μ) ≤ 9 * M ^ 2) ∧
    μ.real {w | ∀ j : Fin K, r < ‖g (finiteBlockCandidates p c K answer w j.succ)‖} ≤ δ ^ K := by
  intro μ
  let Q := (Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)
  have hall (j : Fin (K + 1)) :
      Integrable (fun w => ‖g (blockCandidates p c K answer w.1 w.2 j)‖ ^ 2) Q ∧
      (∫ w, ‖g (blockCandidates p c K answer w.1 w.2 j)‖ ^ 2 ∂Q) ≤ 9 * M ^ 2 := by
    refine Fin.cases ?_ (fun k => ?_) j
    · change Integrable (fun _ => ‖g p.x0‖ ^ 2) Q ∧ (∫ _, ‖g p.x0‖ ^ 2 ∂Q) ≤ 9 * M ^ 2
      refine ⟨integrable_const _, ?_⟩
      simp only [integral_const, probReal_univ, one_smul]
      nlinarith [norm_nonneg (g p.x0), sq_nonneg M]
    · exact block_trial_moment p c K P R answer hstep g hg hi hb k
  have hfullbad := block_trials_failure p c K P R answer hstep g hg hbad
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin K => R)).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving P (K * trialCalls c))
  have hV := measurable_finiteBlockCandidates p c K answer hstep
  refine ⟨fun j => ?_, ?_⟩
  · have hF : Measurable (fun w => ‖g (finiteBlockCandidates p c K answer w j)‖ ^ (2 : ℕ)) :=
      (hg.comp ((measurable_pi_apply j).comp hV)).norm.pow_const 2
    refine ⟨?_, ?_⟩
    · exact (hp.integrable_comp hF.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, Prod.map, id_eq, finiteBlockCandidates_eq] using (hall j).1)
    · dsimp only [μ]
      rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]
      simpa only [Prod.map, id_eq, finiteBlockCandidates_eq] using (hall j).2
  · have hm : MeasurableSet {w | ∀ j : Fin K,
        r < ‖g (finiteBlockCandidates p c K answer w j.succ)‖} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun j => measurableSet_lt measurable_const
        (hg.comp ((measurable_pi_apply j.succ).comp hV)).norm)
    dsimp only [μ]
    rw [← hp.measureReal_preimage hm.nullMeasurableSet]
    simpa only [Set.preimage_ofPred_eq, Prod.map, id_eq, finiteBlockCandidates_eq] using hfullbad

end LongTails.Proofs.ValidatedHessianSampling
