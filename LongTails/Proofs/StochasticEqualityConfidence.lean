import LongTails.Proofs.StochasticEqualityValidation
import LongTails.Proofs.StochasticEqualityEnergy
import LongTails.Proofs.MixedNoiseSelectors
import LongTails.Proofs.StochasticEqualityMoments
import LongTails.Proofs.StochasticEqualityRestoration
import LongTails.Proofs.StochasticEqualitySampling
import LongTails.Proofs.SymmetricThirdOrderSampling

namespace LongTails.Proofs.StochasticEqualityConfidence

open MeasureTheory OracleTemplate
open scoped ENNReal
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Proofs.StochasticEqualityMoments

lemma prefix_groups_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q) (n k b : ℕ) :
    MeasurePreserving (fun z => ((fun i : Fin n => ξ i z),
      (fun i : Fin k => fun j : Fin b => ξ (n + b * i.val + j.val) z))) Q
      ((Measure.pi fun _ : Fin n => P).prod
        (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin b => P)) := by
  have hi := StochasticGeneralized.infinitePi_iid P
  have hb := FiniteVariance.infinite_block_law P (Measure.infinitePi fun _ : ℕ => P)
    hi.independent hi.marginal b
  have hg := (StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin b => P) k).comp hb
  have hh := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => P)).prod hg).comp (h.prefix_tail_law n)
  simpa only [Function.comp_def, Prod.map, id_eq, Nat.mul_comm, Nat.add_assoc] using hh

set_option maxHeartbeats 1000000 in
lemma adaptive_pilot_confidence {Ω Ξ Y E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (n k b : ℕ) (hb : 0 < b) (x : (ℕ → Ω) → Y) (hx : Measurable x)
    (hdep : ∀ z w, (∀ i < n, z i = w i) → x z = x w)
    (g : Y → Ω → E) (hg : Measurable (Function.uncurry g))
    (u : Y → E) (hu : Measurable u) (hi : ∀ y, Integrable (g y) P)
    (hm : ∀ y, ∫ w, g y w ∂P = u y)
    (h2 : ∀ y, Integrable (fun w => ‖g y w - u y‖ ^ 2) P)
    {σ t : ℝ} (hv : ∀ y, (∫ w, ‖g y w - u y‖ ^ 2 ∂P) ≤ σ ^ 2)
    (ht : 0 < t) (hsize : σ ^ 2 / (b : ℝ) ≤ t ^ 2 / 144) :
    Q {z | t < ‖RobustGradient.pilotCenter (2 * t)
      (fun i : Fin k => (1 / (b : ℝ)) • ∑ j : Fin b,
        g (x (fun l => ξ l z)) (ξ (n + b * i.val + j.val) z)) -
      u (x (fun l => ξ l z))‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  obtain ⟨xp, hxp, hfactor⟩ := SymmetricThirdOrderSampling.measurable_prefix_factor P n x hx hdep
  let A : Set ((Fin n → Ω) × (Fin k → Fin b → Ω)) := {z | t <
    ‖RobustGradient.pilotCenter (2 * t)
      (fun i : Fin k => (1 / (b : ℝ)) • ∑ j : Fin b, g (xp z.1) (z.2 i j)) - u (xp z.1)‖}
  have hblocks : Measurable (fun z : (Fin n → Ω) × (Fin k → Fin b → Ω) =>
      fun i : Fin k => (1 / (b : ℝ)) • ∑ j : Fin b, g (xp z.1) (z.2 i j)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro j _
    exact hg.comp ((hxp.comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)))
  have hpilot := (RobustGradient.measurable_pilotCenter k).comp ((measurable_const (a := 2 * t)).prodMk hblocks)
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    ((hpilot.sub (hu.comp (hxp.comp measurable_fst))).norm)
  have hsection (v : Fin n → Ω) : (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin b => P)
      {w | (v, w) ∈ A} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    exact pilot_component_confidence (g (xp v))
      (hg.comp (measurable_const.prodMk measurable_id)) (hi (xp v)) (u (xp v))
      (hm (xp v)) (h2 (xp v)) (hv (xp v)) ht k b hb hsize
  have hlaw := prefix_groups_law h n k b
  have hmeasure := hlaw.measure_preimage hA.nullMeasurableSet
  have hbound : ((Measure.pi fun _ : Fin n => P).prod
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin b => P)) A ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    rw [Measure.prod_apply hA]
    exact (lintegral_mono hsection).trans_eq (by simp)
  rw [← hmeasure] at hbound
  have he (z : Ξ) : x (fun l => ξ l z) = xp (fun i : Fin n => ξ i z) := hfactor _
  simpa only [Set.preimage_ofPred_eq, A, Set.mem_ofPred_eq, he] using hbound

open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.StochasticEquality
open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.StochasticEqualityExecution
open LongTails.Proofs.StochasticEqualitySampling

lemma restoration_prefix_calls (cfg : Config) (n : ℕ) :
    slotCalls (fun _ => restoreUnitCalls cfg) n 0 = 2 * (cfg.restoreBatch * cfg.restoreGroups * n) := by
  simp [StochasticEnvelopeExecution.slotCalls_sum, restoreUnitCalls, Nat.mul_comm]
  ring

lemma measurable_restoration_trace {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (offset n : ℕ) :
    Measurable (fun z => restorationTrace p cfg g z offset n) :=
  measurable_restoration_segment p cfg g hg id measurable_id n 0 offset (fun _ => p.x0) measurable_const

lemma restoration_trace_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (z w : ℕ → Ω) (offset n : ℕ)
    (h : ∀ i, i < offset + cfg.restoreBatch * cfg.restoreGroups * n → z i = w i) :
    restorationTrace p cfg g z offset n = restorationTrace p cfg g w offset n := by
  simp only [restorationTrace, StochasticQuasar.sampled_eval_eq_indexed]
  apply StochasticEnvelopeExecution.evalAt_prefix_congr
  intro j hj y
  have hc := restoration_prefix_calls cfg n
  congr 1
  apply h
  change j < slotCalls (fun _ => restoreUnitCalls cfg) n 0 at hj
  omega

lemma restoration_estimate_samples {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (z : ℕ → Ω) (offset n : ℕ) :
    restorationEstimate p cfg g z offset n =
      let x := restorationTrace p cfg g z offset n
      let base := offset + cfg.restoreBatch * cfg.restoreGroups * n
      let values := fun i : Fin cfg.restoreGroups => (cfg.restoreBatch : ℝ)⁻¹ •
        ∑ j : Fin cfg.restoreBatch, g x (z (base + cfg.restoreBatch * i.val + j.val))
      (RobustGradient.pilotCenter (2 * cfg.restoreTolerance) (fun i => (values i).1),
        RobustGradient.pilotCenter (2 * cfg.restoreTolerance) (fun i => (values i).2.1),
        RobustGradient.pilotCenter (2 * cfg.restoreTolerance) (fun i => (values i).2.2)) := by
  rw [restorationEstimate, restoration_prefix_calls]
  rw [show 2 * offset + 2 * (cfg.restoreBatch * cfg.restoreGroups * n) =
    2 * (offset + cfg.restoreBatch * cfg.restoreGroups * n) by ring]
  exact sampled_robust p g z _ _ _ _ _

set_option maxHeartbeats 1000000 in
lemma restoration_estimate_failures {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ x, Integrable (g x) P)
    (hm : ∀ x, ∫ w, g x w ∂P = u x)
    (h2 : ∀ x, Integrable (fun w => ‖pack p (g x w) - pack p (u x)‖ ^ 2) P)
    (hv : ∀ x, (∫ w, ‖pack p (g x w) - pack p (u x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (ht : 0 < cfg.restoreTolerance)
    (hsize : p.σ ^ 2 / (cfg.restoreBatch : ℝ) ≤ cfg.restoreTolerance ^ 2 / 144)
    (offset n : ℕ) :
    Q {z | cfg.restoreTolerance <
      ‖(restorationEstimate p cfg g (fun l => ξ l z) offset n).2.1 -
        (u (restorationTrace p cfg g (fun l => ξ l z) offset n)).2.1‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ)) ∧
    Q {z | cfg.restoreTolerance <
      ‖(restorationEstimate p cfg g (fun l => ξ l z) offset n).2.2 -
        (u (restorationTrace p cfg g (fun l => ξ l z) offset n)).2.2‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ)) := by
  let x := fun z => restorationTrace p cfg g z offset n
  have hx : Measurable x := measurable_restoration_trace p cfg g hg offset n
  have hdep : ∀ z w, (∀ i < offset + cfg.restoreBatch * cfg.restoreGroups * n, z i = w i) → x z = x w :=
    fun z w hh => restoration_trace_prefix_congr p cfg g z w offset n hh
  have hcomponents (y : Point p.d) := component_variance_bounds p P (g y)
    (hg.comp (measurable_const.prodMk measurable_id)) (u y) (h2 y) (hv y)
  constructor
  · have hmean (y : Point p.d) : (∫ w, (g y w).2.1 ∂P) = (u y).2.1 := by
      have hh := congrArg (fun v : Reply p => v.2.1) (hm y)
      simpa only [snd_integral (hi y), fst_integral (hi y).snd] using hh
    have hh := adaptive_pilot_confidence h (offset + cfg.restoreBatch * cfg.restoreGroups * n)
      cfg.restoreGroups cfg.restoreBatch cfg.restoreBatch.pos x hx hdep
      (fun y w => (g y w).2.1) hg.snd.fst (fun y => (u y).2.1) hu.snd.fst
      (fun y => (hi y).snd.fst) hmean (fun y => (hcomponents y).2.1.1)
      (fun y => (hcomponents y).2.1.2) ht hsize
    simpa only [restoration_estimate_samples, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum,
      Prod.fst_sum, one_div, x] using hh
  · have hmean (y : Point p.d) : (∫ w, (g y w).2.2 ∂P) = (u y).2.2 := by
      have hh := congrArg (fun v : Reply p => v.2.2) (hm y)
      simpa only [snd_integral (hi y), snd_integral (hi y).snd] using hh
    have hh := adaptive_pilot_confidence h (offset + cfg.restoreBatch * cfg.restoreGroups * n)
      cfg.restoreGroups cfg.restoreBatch cfg.restoreBatch.pos x hx hdep
      (fun y w => (g y w).2.2) hg.snd.snd (fun y => (u y).2.2) hu.snd.snd
      (fun y => (hi y).snd.snd) hmean (fun y => (hcomponents y).2.2.1)
      (fun y => (hcomponents y).2.2.2) ht hsize
    simpa only [restoration_estimate_samples, Prod.smul_snd, Prod.snd_sum, one_div, x] using hh

def restorationGood {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (u : Point p.d → Reply p) (offset : ℕ) (z : ℕ → Ω) : Prop :=
  ∀ k : Fin cfg.restoreSteps,
    ‖(restorationEstimate p cfg g z offset k).2.1 -
      (u (restorationTrace p cfg g z offset k)).2.1‖ ≤ cfg.restoreTolerance ∧
    ‖(restorationEstimate p cfg g z offset k).2.2 -
      (u (restorationTrace p cfg g z offset k)).2.2‖ ≤ cfg.restoreTolerance

lemma measurable_restoration_estimate {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (offset n : ℕ) :
    Measurable (fun z => restorationEstimate p cfg g z offset n) := by
  simp only [restorationEstimate, restoration_prefix_calls]
  rw [show 2 * offset + 2 * (cfg.restoreBatch * cfg.restoreGroups * n) =
    2 * (offset + cfg.restoreBatch * cfg.restoreGroups * n) by ring]
  exact (measurable_sampled_robust p g hg cfg.restoreTolerance cfg.restoreBatch cfg.restoreGroups
    (offset + cfg.restoreBatch * cfg.restoreGroups * n)).comp
      ((measurable_restoration_trace p cfg g hg offset n).prodMk measurable_id)

lemma measurableSet_restorationGood {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (u : Point p.d → Reply p) (hu : Measurable u)
    (offset : ℕ) : MeasurableSet {z | restorationGood p cfg g u offset z} := by
  simp only [restorationGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have he := measurable_restoration_estimate p cfg g hg offset k
  have ht := hu.comp (measurable_restoration_trace p cfg g hg offset k)
  exact (measurableSet_le (he.snd.fst.sub ht.snd.fst).norm measurable_const).inter
    (measurableSet_le (he.snd.snd.sub ht.snd.snd).norm measurable_const)

lemma restoration_bad_probability {Ω Ξ : Type*} [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) (Q : Measure Ξ) (ξ : ℕ → Ξ → Ω)
    (g : Point p.d → Ω → Reply p) (u : Point p.d → Reply p) (offset : ℕ) (δ : ℝ≥0∞)
    (hfail : ∀ k : Fin cfg.restoreSteps,
      Q {z | cfg.restoreTolerance < ‖(restorationEstimate p cfg g (fun l => ξ l z) offset k).2.1 -
        (u (restorationTrace p cfg g (fun l => ξ l z) offset k)).2.1‖} ≤ δ ∧
      Q {z | cfg.restoreTolerance < ‖(restorationEstimate p cfg g (fun l => ξ l z) offset k).2.2 -
        (u (restorationTrace p cfg g (fun l => ξ l z) offset k)).2.2‖} ≤ δ) :
    Q {z | ¬ restorationGood p cfg g u offset (fun l => ξ l z)} ≤
      2 * (cfg.restoreSteps : ℝ≥0∞) * δ := by
  classical
  let A := fun k : Fin cfg.restoreSteps => {z | cfg.restoreTolerance <
    ‖(restorationEstimate p cfg g (fun l => ξ l z) offset k).2.1 -
      (u (restorationTrace p cfg g (fun l => ξ l z) offset k)).2.1‖}
  let B := fun k : Fin cfg.restoreSteps => {z | cfg.restoreTolerance <
    ‖(restorationEstimate p cfg g (fun l => ξ l z) offset k).2.2 -
      (u (restorationTrace p cfg g (fun l => ξ l z) offset k)).2.2‖}
  have he : {z | ¬ restorationGood p cfg g u offset (fun l => ξ l z)} =
      ⋃ k : Fin cfg.restoreSteps, A k ∪ B k := by
    ext z
    simp only [Set.mem_ofPred_eq, restorationGood, not_forall, not_and_or, not_le,
      Set.mem_iUnion, Set.mem_union, A, B]
  rw [he]
  calc
    _ ≤ ∑' k : Fin cfg.restoreSteps, Q (A k ∪ B k) := measure_iUnion_le _
    _ = ∑ k : Fin cfg.restoreSteps, Q (A k ∪ B k) := tsum_fintype _
    _ ≤ ∑ _k : Fin cfg.restoreSteps, (δ + δ) := Finset.sum_le_sum (fun k _ =>
      (measure_union_le (A k) (B k)).trans (add_le_add (hfail k).1 (hfail k).2))
    _ = _ := by simp; ring

lemma restoration_confidence {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ x, Integrable (g x) P)
    (hm : ∀ x, ∫ w, g x w ∂P = u x)
    (h2 : ∀ x, Integrable (fun w => ‖pack p (g x w) - pack p (u x)‖ ^ 2) P)
    (hv : ∀ x, (∫ w, ‖pack p (g x w) - pack p (u x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (ht : 0 < cfg.restoreTolerance)
    (hsize : p.σ ^ 2 / (cfg.restoreBatch : ℝ) ≤ cfg.restoreTolerance ^ 2 / 144)
    (offset : ℕ) :
    Q {z | ¬ restorationGood p cfg g u offset (fun l => ξ l z)} ≤
      2 * (cfg.restoreSteps : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ)) := by
  exact restoration_bad_probability p cfg Q ξ g u offset _
    (fun k => restoration_estimate_failures p cfg h g hg u hu hi hm h2 hv ht hsize offset k)

set_option maxHeartbeats 1000000 in
lemma restoration_good_initialization (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ x, fLower ≤ I.f x)
    (hgap : I.f p.x0 - fLower ≤ p.Δ) {Ω : Type*} (g : Point p.d → Ω → Reply p.toPublic)
    (z : ℕ → Ω) (offset : ℕ)
    (hgood : restorationGood p.toPublic (tuning p.toPublic) g (StochasticEqualityModel.truth I) offset z) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    let y := QueryPlan.sampledEval g (fun i => z (i / 2)) (restorePlan p.toPublic cfg) (2 * offset)
    ‖I.c y‖ ≤ 1 / (10 ^ 6 * S ^ 7) ∧ ‖gradient I.f y‖ ≤ cfg.gradientCap ∧
      ‖I.c y‖ ≤ cfg.constraintCap ∧
      StochasticEqualityDescent.merit I.f I.c (fun x => (fderiv ℝ I.c x).adjoint)
        (gradient I.f) (10 ^ 10 * S ^ 24) y - fLower ≤ 10 ^ 6 * S ^ 10 - 1 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let y := QueryPlan.sampledEval g (fun i => z (i / 2)) (restorePlan p.toPublic cfg) (2 * offset)
  have hpath := StochasticEqualityRestoration.admissible_restoration_path p hp I O hI g z offset
    (fun k hk => hgood ⟨k, hk⟩)
  have hSpos : 0 < S := by
    have hh := (StochasticEqualityTuning.scale_bounds p hp).1
    dsimp [S]
    linarith only [hh]
  have hr : 0 < 1 / (10 ^ 6 * S ^ 7) := by positivity
  have hc : ‖I.c y‖ ≤ 1 / (10 ^ 6 * S ^ 7) := by
    apply (sq_le_sq₀ (norm_nonneg _) hr.le).mp
    have hh := hpath.2
    change ‖I.c y‖ ^ 2 < (1 / (10 ^ 6 * S ^ 7)) ^ 2 / 8 at hh
    nlinarith only [hh, sq_nonneg (1 / (10 ^ 6 * S ^ 7))]
  have hg := StochasticEqualityRestoration.admissible_restored_gap p hp I O hI fLower hlow hgap g z offset
  exact ⟨hc, StochasticEqualityRestoration.restored_initial_bounds p hp I O hI fLower hlow y hg hc⟩

lemma tuned_restoration_confidence {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Params) (hp : spec.valid p) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p.toPublic) (hu : Measurable u) (hi : ∀ x, Integrable (g x) P)
    (hm : ∀ x, ∫ w, g x w ∂P = u x)
    (h2 : ∀ x, Integrable (fun w => ‖pack p.toPublic (g x w) - pack p.toPublic (u x)‖ ^ 2) P)
    (hv : ∀ x, (∫ w, ‖pack p.toPublic (g x w) - pack p.toPublic (u x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (offset : ℕ) :
    Q {z | ¬ restorationGood p.toPublic (tuning p.toPublic) g u offset (fun l => ξ l z)} ≤
      ENNReal.ofReal (1 / 100 : ℝ) := by
  let cfg := tuning p.toPublic
  have hS : 0 < StochasticEqualityTuning.scale p.toPublic := by
    have hh := (StochasticEqualityTuning.scale_bounds p hp).1
    linarith only [hh]
  have ht : 0 < cfg.restoreTolerance := by
    change 0 < 1 / (10 ^ 8 * (StochasticEqualityTuning.scale p.toPublic) ^ 9)
    positivity
  have hh := restoration_confidence p.toPublic cfg h g hg u hu hi hm h2 hv ht
    (StochasticEqualityTuning.tuning_robust_precision p hp).1 offset
  apply hh.trans
  have he : 2 * (cfg.restoreSteps : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ)) =
      ENNReal.ofReal (2 * (cfg.restoreSteps : ℝ) * (1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (cfg.restoreSteps : ℝ)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he]
  exact ENNReal.ofReal_le_ofReal (StochasticEqualityTuning.tuning_restoration_failure p hp)

set_option maxHeartbeats 1000000 in
lemma tuned_restoration_output_failure {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P)
    (hm : ∀ x, ∫ w, g x w ∂P = StochasticEqualityModel.truth I x)
    (h2 : ∀ x, Integrable (fun w => ‖pack p.toPublic (g x w) -
      pack p.toPublic (StochasticEqualityModel.truth I x)‖ ^ 2) P)
    (hv : ∀ x, (∫ w, ‖pack p.toPublic (g x w) -
      pack p.toPublic (StochasticEqualityModel.truth I x)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (offset : ℕ) :
    Q {z | 1 / (10 ^ 6 * (StochasticEqualityTuning.scale p.toPublic) ^ 7) <
      ‖I.c (QueryPlan.sampledEval g (fun i => ξ (i / 2) z)
        (restorePlan p.toPublic (tuning p.toPublic)) (2 * offset))‖} ≤
      ENNReal.ofReal (1 / 100 : ℝ) := by
  have ht := StochasticEqualityModel.admissible_truth_measurable p hp I O hI
  have hb := tuned_restoration_confidence p hp h g hg (StochasticEqualityModel.truth I) ht hi hm h2 hv offset
  apply le_trans (measure_mono ?_) hb
  intro z hz
  change ¬ restorationGood p.toPublic (tuning p.toPublic) g (StochasticEqualityModel.truth I)
    offset (fun l => ξ l z)
  intro hgood
  obtain ⟨fLower, hlow, hgap⟩ := hI.2.2.1
  have hh := restoration_good_initialization p hp I O hI fLower hlow hgap g (fun l => ξ l z) offset hgood
  exact (not_lt_of_ge hh.1) hz


lemma uniform_selected_failure {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [SFinite P] (T : ℕ+) (F : ℕ → Z → ℝ)
    (hm : ∀ k, Measurable (F k)) (hn : ∀ k z, 0 ≤ F k z)
    (hi : Integrable (fun z => ∑ k ∈ Finset.range T, F k z) P)
    {a : ℝ} (ha : 0 < a)
    (hb : (∫ z, ∑ k ∈ Finset.range T, F k z ∂P) / T ≤ a / 100) :
    ((PMF.uniformOfFintype (Fin T)).toMeasure.prod P)
      {z | a < F z.1.val z.2} ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
  have hfi (k : Fin T) : Integrable (F k.val) P := by
    apply hi.mono' (hm k.val).aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hn k.val z)]
    exact Finset.single_le_sum (fun j _ => hn j z) (Finset.mem_range.mpr k.isLt)
  have hfm : Measurable (fun z : Fin T × Z => F z.1.val z.2) :=
    measurable_from_prod_countable_right fun k => hm k.val
  have hpi : Integrable (fun z : Fin T × Z => F z.1.val z.2)
      ((PMF.uniformOfFintype (Fin T)).toMeasure.prod P) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall hfi, Integrable.of_finite⟩
  apply StochasticEqualityEnergy.nonnegative_budget_failure _ _ hpi
    (fun z => hn z.1.val z.2) ha
  rw [integral_prod _ hpi, OracleTemplate.MixedNoise.integral_uniform_finite]
  simp only [Fintype.card_fin]
  have hs : (∑ k : Fin T, ∫ z, F k.val z ∂P) =
      ∫ z, ∑ k ∈ Finset.range T, F k z ∂P := by
    rw [← integral_finsetSum _ (fun k _ => hfi k)]
    congr 1
    funext z
    exact Fin.sum_univ_eq_sum_range (fun k => F k z) T
  rw [hs]
  simpa only [div_eq_mul_inv, mul_comm] using hb

set_option maxHeartbeats 1000000 in
lemma restored_energy_statistics {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (offset : ℕ) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
    let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
    let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
    let E := ∑ k ∈ Finset.range cfg.steps,
      ∫ ξ, StochasticEqualityProcess.stoppedError p.toPublic cfg g (StochasticEqualityModel.truth I) x good τ k ξ ∂Q
    let R := fun ξ => ∑ k ∈ Finset.range cfg.steps,
      StochasticEqualityEnergy.stoppedResidual p.toPublic cfg (10 ^ 10 * S ^ 24) g
        (StochasticEqualityModel.truth I) x good τ k ξ
    Integrable R Q ∧
      cfg.step * (2 * 10 ^ 10 * S ^ 24) * (10 ^ 6 * S ^ 11) ^ 2 * E ≤ (10 ^ 6 * S ^ 10) / 100 ∧
      (∫ ξ, R ξ ∂Q) / cfg.steps ≤ (p.ε / (32 * S)) ^ 2 / 100 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
  let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
  let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
  obtain ⟨fLower, hlow, hgap, _⟩ := StochasticEqualityModel.admissible_merit_lower p hp I O hI
  have hx : Measurable x := measurable_restoration_trace p.toPublic cfg g hg offset cfg.restoreSteps
  have hc : Measurable I.c := (hI.2.1.continuous).measurable
  have hgood : MeasurableSet {ξ | good ξ} := measurableSet_le (hc.comp hx).norm measurable_const
  have hdx : ∀ ξ ζ, (∀ i, i < τ → ξ i = ζ i) → x ξ = x ζ :=
    fun ξ ζ hh => restoration_trace_prefix_congr p.toPublic cfg g ξ ζ offset cfg.restoreSteps hh
  have hdgood : ∀ ξ ζ, (∀ i, i < τ → ξ i = ζ i) → (good ξ ↔ good ζ) := by
    intro ξ ζ hh
    dsimp only [good]
    rw [hdx ξ ζ hh]
  apply StochasticEqualityEnergy.admissible_expected_energy p hp I O hI P fLower hlow
    g hg hi hmean hnoise2 hnoise hdiff2 hdiff x hx good hgood τ hdx hdgood
  · intro ξ
    exact StochasticEqualityRestoration.admissible_restored_gap p hp I O hI fLower hlow hgap g ξ offset
  · intro ξ hh
    exact hh

set_option maxHeartbeats 1000000 in
lemma restored_no_exit_failure {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (offset : ℕ) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
    let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
    let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
    Q {ξ | ¬ ∀ n : ℕ, n ≤ cfg.steps → StochasticEqualityProcess.active p.toPublic cfg (StochasticEqualityModel.truth I)
      (fun j z => (trainingTrace p.toPublic cfg g z (x z) τ j).point) good n ξ} ≤
      ENNReal.ofReal (2 / 100 : ℝ) := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
  let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
  let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
  let A := cfg.step * (2 * 10 ^ 10 * S ^ 24) * (10 ^ 6 * S ^ 11) ^ 2
  let W := 10 ^ 6 * S ^ 10
  let B := fun ξ => A * ∑ k ∈ Finset.range cfg.steps,
    StochasticEqualityProcess.stoppedError p.toPublic cfg g (StochasticEqualityModel.truth I) x good τ k ξ
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  obtain ⟨hη, hG, hM, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hx : Measurable x := measurable_restoration_trace p.toPublic cfg g hg offset cfg.restoreSteps
  have hc : Measurable I.c := hI.2.1.continuous.measurable
  have hgood : MeasurableSet {ξ | good ξ} := measurableSet_le (hc.comp hx).norm measurable_const
  have ht := StochasticEqualityModel.admissible_truth_measurable p hp I O hI
  have hs := restored_energy_statistics p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff offset
  have he : Q {ξ | W < B ξ} ≤ ENNReal.ofReal (1 / 100 : ℝ) :=
    StochasticEqualityEnergy.stopped_error_budget_failure p.toPublic cfg Q hG hM hp.2.2.2.2.2.1
      g hg (StochasticEqualityModel.truth I) ht hI.2.2.2.2.2.1 x hx good hgood τ cfg.steps
      (by dsimp [A]; positivity) (by dsimp [W]; positivity) hs.2.1
  have hr : Q {ξ | ¬ good ξ} ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
    have hh := tuned_restoration_output_failure p hp I O hI
      (ξ := fun k (ξ : ℕ → Ω) => ξ k) (P := P) (Q := Q)
      (OracleTemplate.StochasticGeneralized.infinitePi_iid P) g hg hi hmean hnoise2 hnoise offset
    simpa only [good, x, not_le, StochasticEqualityRestoration.restoration_trace_terminal] using hh
  have hh : Q {ξ | ¬ ∀ n : ℕ, n ≤ cfg.steps → StochasticEqualityProcess.active p.toPublic cfg
      (StochasticEqualityModel.truth I) (fun j z => (trainingTrace p.toPublic cfg g z (x z) τ j).point) good n ξ} ≤
      Q ({ξ | ¬ good ξ} ∪ {ξ | W < B ξ}) := by
    apply measure_mono
    intro ξ hbad
    by_cases hgoodξ : good ξ
    · right
      by_contra hnot
      have hb : B ξ ≤ W := not_lt.mp hnot
      obtain ⟨fLower, hlow, hgap⟩ := hI.2.2.1
      apply hbad
      exact StochasticEqualityEnergy.admissible_no_exit p hp I O hI fLower hlow g x good τ cfg.steps ξ hgoodξ
        (StochasticEqualityRestoration.admissible_restored_gap p hp I O hI fLower hlow hgap g ξ offset)
        hgoodξ hb
    · exact Or.inl hgoodξ
  apply hh.trans ((measure_union_le _ _).trans ((add_le_add hr he).trans ?_))
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  norm_num

lemma selected_unstopped_failure {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u)
    (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (good : (ℕ → Ω) → Prop) (hgood : MeasurableSet {z | good z}) (offset : ℕ)
    {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 < a)
    (hi : Integrable (fun ξ => ∑ k ∈ Finset.range cfg.steps,
      StochasticEqualityEnergy.stoppedResidual p cfg β g u x good offset k ξ) P)
    (hb : (∫ ξ, ∑ k ∈ Finset.range cfg.steps,
      StochasticEqualityEnergy.stoppedResidual p cfg β g u x good offset k ξ ∂P) / cfg.steps ≤ a / 100)
    (hn : P {ξ | ¬ StochasticEqualityProcess.active p cfg u
      (fun j z => (trainingTrace p cfg g z (x z) offset j).point) good cfg.steps ξ} ≤
      ENNReal.ofReal (2 / 100 : ℝ)) :
    ((PMF.uniformOfFintype (Fin cfg.steps)).toMeasure.prod P)
      {z | ¬ StochasticEqualityProcess.active p cfg u
        (fun j ξ => (trainingTrace p cfg g ξ (x ξ) offset j).point) good cfg.steps z.2 ∨
        a < StochasticEqualityEnergy.residual p u β
        (QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trainingPlan p cfg z.1 (x z.2)) (2 * offset))} ≤
      ENNReal.ofReal (3 / 100 : ℝ) := by
  let path := fun j z => (trainingTrace p cfg g z (x z) offset j).point
  let A := {ξ | ¬ StochasticEqualityProcess.active p cfg u path good cfg.steps ξ}
  let F := StochasticEqualityEnergy.stoppedResidual p cfg β g u x good offset
  let U := (PMF.uniformOfFintype (Fin cfg.steps)).toMeasure
  have hAm : MeasurableSet A := (StochasticEqualityProcess.measurableSet_active p cfg u hu path
    (fun k => (StochasticEqualityProcess.measurable_trace p cfg g hg id measurable_id x hx offset k).1)
    good hgood cfg.steps).compl
  have hA : (U.prod P) {z | z.2 ∈ A} ≤ ENNReal.ofReal (2 / 100 : ℝ) := by
    rw [show {z : Fin cfg.steps × (ℕ → Ω) | z.2 ∈ A} = Prod.snd ⁻¹' A from rfl,
      (measurePreserving_snd (μ := U) (ν := P)).measure_preimage hAm.nullMeasurableSet]
    exact hn
  have hF := uniform_selected_failure P cfg.steps F
    (fun k => StochasticEqualityEnergy.measurable_stoppedResidual p cfg β g hg u hu x hx good hgood offset k)
    (fun k ξ => StochasticEqualityEnergy.stoppedResidual_nonneg p cfg hβ g u x good offset k ξ)
    hi ha hb
  have hs : (U.prod P)
      {z | ¬ StochasticEqualityProcess.active p cfg u
        (fun j ξ => (trainingTrace p cfg g ξ (x ξ) offset j).point) good cfg.steps z.2 ∨
        a < StochasticEqualityEnergy.residual p u β
        (QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trainingPlan p cfg z.1 (x z.2)) (2 * offset))} ≤
      (U.prod P) ({z | z.2 ∈ A} ∪ {z | a < F z.1.val z.2}) := by
    apply measure_mono
    intro z hz
    by_cases haT : StochasticEqualityProcess.active p cfg u path good cfg.steps z.2
    · right
      have hak := StochasticEqualityProcess.active_mono p cfg u path good z.1.isLt.le z.2 haT
      simp only [Set.mem_ofPred_eq] at hz
      have hzSelected := hz.resolve_left (not_not_intro haT)
      rw [training_output_prefix] at hzSelected
      change a < StochasticEqualityEnergy.residual p u β
        (trainingTrace p cfg g z.2 (x z.2) offset z.1.val).point at hzSelected
      dsimp only [path] at hak
      change a < F z.1.val z.2
      dsimp only [F, StochasticEqualityEnergy.stoppedResidual]
      rw [ite_eq_left hak]
      exact hzSelected
    · exact Or.inl haT
  apply hs.trans ((measure_union_le _ _).trans ((add_le_add hA hF).trans ?_))
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 2 / 100) (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  norm_num

set_option maxHeartbeats 1000000 in
lemma restored_selected_failure {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (offset : ℕ) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
    let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
    let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
    ((PMF.uniformOfFintype (Fin cfg.steps)).toMeasure.prod Q)
      {z | ¬ StochasticEqualityProcess.active p.toPublic cfg (StochasticEqualityModel.truth I)
        (fun j ξ => (trainingTrace p.toPublic cfg g ξ (x ξ) τ j).point) good cfg.steps z.2 ∨
        (p.ε / (32 * S)) ^ 2 < StochasticEqualityEnergy.residual p.toPublic (StochasticEqualityModel.truth I)
          (10 ^ 10 * S ^ 24)
          (QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trainingPlan p.toPublic cfg z.1 (x z.2)) (2 * τ))} ≤
      ENNReal.ofReal (3 / 100 : ℝ) := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
  let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
  let τ := offset + cfg.restoreBatch * cfg.restoreGroups * cfg.restoreSteps
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hx : Measurable x := measurable_restoration_trace p.toPublic cfg g hg offset cfg.restoreSteps
  have hc : Measurable I.c := hI.2.1.continuous.measurable
  have hgood : MeasurableSet {ξ | good ξ} := measurableSet_le (hc.comp hx).norm measurable_const
  have ht := StochasticEqualityModel.admissible_truth_measurable p hp I O hI
  have hs := restored_energy_statistics p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff offset
  have hn := restored_no_exit_failure p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff offset
  apply selected_unstopped_failure p.toPublic cfg Q g hg (StochasticEqualityModel.truth I) ht
    x hx good hgood τ (by positivity) (by positivity) hs.1 hs.2.2
  apply le_trans (measure_mono ?_) hn
  intro ξ hbad hall
  exact hbad (hall cfg.steps le_rfl)


lemma adaptive_reply_confidence {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ y, Integrable (g y) P)
    (hm : ∀ y, ∫ w, g y w ∂P = u y)
    (h2 : ∀ y, Integrable (fun w => ‖pack p (g y w) - pack p (u y)‖ ^ 2) P)
    (hv : ∀ y, (∫ w, ‖pack p (g y w) - pack p (u y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (n k b : ℕ) (hb : 0 < b) (x : (ℕ → Ω) → Point p.d) (hx : Measurable x)
    (hdep : ∀ z w, (∀ i < n, z i = w i) → x z = x w)
    {t : ℝ} (ht : 0 < t) (hsize : p.σ ^ 2 / (b : ℝ) ≤ t ^ 2 / 144) :
    let V := fun z => QueryPlan.sampledEval g (fun i => ξ (i / 2) z)
      (robustPlan p t b k (x (fun l => ξ l z))) (2 * n)
    let U := fun z => u (x (fun l => ξ l z))
    Q {z | t < ‖(V z).1 - (U z).1‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ∧
      Q {z | t < ‖(V z).2.1 - (U z).2.1‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ∧
      Q {z | t < ‖(V z).2.2 - (U z).2.2‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have he (z : Ξ) := sampled_robust p g (fun l => ξ l z) (x (fun l => ξ l z)) t b k n
  have hcomponents (y : Point p.d) := component_variance_bounds p P (g y)
    (hg.comp (measurable_const.prodMk measurable_id)) (u y) (h2 y) (hv y)
  refine ⟨?_, ?_, ?_⟩
  · have hmean (y : Point p.d) : (∫ w, (g y w).1 ∂P) = (u y).1 := by
      have hh := congrArg (fun v : Reply p => v.1) (hm y)
      simpa only [fst_integral (hi y)] using hh
    have hh := adaptive_pilot_confidence h n k b hb x hx hdep
      (fun y w => (g y w).1) hg.fst (fun y => (u y).1) hu.fst
      (fun y => (hi y).fst) hmean (fun y => (hcomponents y).1.1)
      (fun y => (hcomponents y).1.2) ht hsize
    simpa only [he, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, one_div] using hh
  · have hmean (y : Point p.d) : (∫ w, (g y w).2.1 ∂P) = (u y).2.1 := by
      have hh := congrArg (fun v : Reply p => v.2.1) (hm y)
      simpa only [snd_integral (hi y), fst_integral (hi y).snd] using hh
    have hh := adaptive_pilot_confidence h n k b hb x hx hdep
      (fun y w => (g y w).2.1) hg.snd.fst (fun y => (u y).2.1) hu.snd.fst
      (fun y => (hi y).snd.fst) hmean (fun y => (hcomponents y).2.1.1)
      (fun y => (hcomponents y).2.1.2) ht hsize
    simpa only [he, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, one_div] using hh
  · have hmean (y : Point p.d) : (∫ w, (g y w).2.2 ∂P) = (u y).2.2 := by
      have hh := congrArg (fun v : Reply p => v.2.2) (hm y)
      simpa only [snd_integral (hi y), snd_integral (hi y).snd] using hh
    have hh := adaptive_pilot_confidence h n k b hb x hx hdep
      (fun y w => (g y w).2.2) hg.snd.snd (fun y => (u y).2.2) hu.snd.snd
      (fun y => (hi y).snd.snd) hmean (fun y => (hcomponents y).2.2.1)
      (fun y => (hcomponents y).2.2.2) ht hsize
    simpa only [he, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, one_div] using hh


lemma measurable_trialPoint {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (index : Fin cfg.steps) (offset : ℕ) :
    Measurable (fun ξ => trialPoint p cfg g ξ index offset) :=
  (measurable_training_output p cfg g hg index (trainingOffset cfg offset)).comp
    ((measurable_restoration_trace p cfg g hg offset cfg.restoreSteps).prodMk measurable_id)

lemma trialPoint_prefix_congr {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (index : Fin cfg.steps) (offset : ℕ)
    (ξ ζ : ℕ → Ω) (h : ∀ i, i < validationOffset cfg offset → ξ i = ζ i) :
    trialPoint p cfg g ξ index offset = trialPoint p cfg g ζ index offset := by
  let x := fun z => restorationTrace p cfg g z offset cfg.restoreSteps
  have hx : ∀ z w, (∀ i, i < trainingOffset cfg offset → z i = w i) → x z = x w :=
    fun z w hh => restoration_trace_prefix_congr p cfg g z w offset cfg.restoreSteps hh
  have hn : batchOffset cfg (trainingOffset cfg offset) index.val ≤ validationOffset cfg offset := by
    apply Nat.add_le_add_left
    exact Finset.sum_le_sum_of_subset (Finset.range_mono index.isLt.le)
  have hh := StochasticEqualityProcess.trace_random_start_prefix_congr p cfg g x
    (trainingOffset cfg offset) index.val hx ξ ζ (fun i hi => h i (lt_of_lt_of_le hi hn))
  simp only [trialPoint, training_output_prefix]
  exact congrArg TrainingState.point hh

lemma sampled_trial {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ) :
    QueryPlan.sampledEval g (fun i => ξ (i / 2)) (trialPlan p cfg index) (2 * offset) =
      validate p cfg (trialPoint p cfg g ξ index offset) (trialEstimate p cfg g ξ index offset) := by
  have hrestore : 2 * offset + restoreCalls cfg = 2 * trainingOffset cfg offset := by
    rw [restore_calls]
    unfold trainingOffset
    ring
  have htrain : 2 * trainingOffset cfg offset + trainingCalls cfg = 2 * validationOffset cfg offset := by
    rw [training_calls]
    unfold validationOffset batchOffset
    ring
  unfold trialPlan
  erw [QueryPlan.sampledEval_bind, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
  simp only [hrestore, htrain, trialPoint, trialEstimate,
    StochasticEqualityRestoration.restoration_trace_terminal]
  rfl


def replyAccurate (p : Public) (t : ℝ) (u v : Reply p) : Prop :=
  ‖v.1 - u.1‖ ≤ t ∧ ‖v.2.1 - u.2.1‖ ≤ t ∧ ‖v.2.2 - u.2.2‖ ≤ t

lemma measurableSet_replyAccurate {Z : Type*} [MeasurableSpace Z]
    (p : Public) (t : ℝ) (u v : Z → Reply p) (hu : Measurable u) (hv : Measurable v) :
    MeasurableSet {z | replyAccurate p t (u z) (v z)} :=
  (measurableSet_le (hv.fst.sub hu.fst).norm measurable_const).inter
    ((measurableSet_le (hv.snd.fst.sub hu.snd.fst).norm measurable_const).inter
      (measurableSet_le (hv.snd.snd.sub hu.snd.snd).norm measurable_const))

lemma reply_failure_union {Z : Type*} [MeasurableSpace Z]
    (p : Public) (t : ℝ) (P : Measure Z) (u v : Z → Reply p) (δ : ℝ≥0∞)
    (hg : P {z | t < ‖(v z).1 - (u z).1‖} ≤ δ)
    (hc : P {z | t < ‖(v z).2.1 - (u z).2.1‖} ≤ δ)
    (hJ : P {z | t < ‖(v z).2.2 - (u z).2.2‖} ≤ δ) :
    P {z | ¬ replyAccurate p t (u z) (v z)} ≤ 3 * δ := by
  have he : {z | ¬ replyAccurate p t (u z) (v z)} =
      {z | t < ‖(v z).1 - (u z).1‖} ∪
        ({z | t < ‖(v z).2.1 - (u z).2.1‖} ∪ {z | t < ‖(v z).2.2 - (u z).2.2‖}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, replyAccurate, not_and_or, not_le]
  rw [he]
  calc
    _ ≤ P {z | t < ‖(v z).1 - (u z).1‖} +
        P ({z | t < ‖(v z).2.1 - (u z).2.1‖} ∪ {z | t < ‖(v z).2.2 - (u z).2.2‖}) := measure_union_le _ _
    _ ≤ δ + (δ + δ) := add_le_add hg ((measure_union_le _ _).trans (add_le_add hc hJ))
    _ = 3 * δ := by ring

lemma trial_estimate_confidence {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ y, Integrable (g y) P)
    (hm : ∀ y, ∫ w, g y w ∂P = u y)
    (h2 : ∀ y, Integrable (fun w => ‖pack p (g y w) - pack p (u y)‖ ^ 2) P)
    (hv : ∀ y, (∫ w, ‖pack p (g y w) - pack p (u y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (ht : 0 < cfg.validationTolerance)
    (hsize : p.σ ^ 2 / (cfg.validationBatch : ℝ) ≤ cfg.validationTolerance ^ 2 / 144)
    (index : Fin cfg.steps) (offset : ℕ) :
    Q {z | ¬ replyAccurate p cfg.validationTolerance
      (u (trialPoint p cfg g (fun l => ξ l z) index offset))
      (trialEstimate p cfg g (fun l => ξ l z) index offset)} ≤
      3 * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) := by
  have hh := adaptive_reply_confidence p h g hg u hu hi hm h2 hv
    (validationOffset cfg offset) cfg.validationGroups cfg.validationBatch cfg.validationBatch.pos
    (fun z => trialPoint p cfg g z index offset) (measurable_trialPoint p cfg g hg index offset)
    (trialPoint_prefix_congr p cfg g index offset) ht hsize
  exact reply_failure_union p cfg.validationTolerance Q _ _ _ hh.1 hh.2.1 hh.2.2

lemma measurable_trialEstimate {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (index : Fin cfg.steps) (offset : ℕ) :
    Measurable (fun ξ => trialEstimate p cfg g ξ index offset) :=
  (measurable_sampled_robust p g hg cfg.validationTolerance cfg.validationBatch cfg.validationGroups
    (validationOffset cfg offset)).comp
      ((measurable_trialPoint p cfg g hg index offset).prodMk measurable_id)

lemma trial_estimate_confidence_product {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ y, Integrable (g y) P)
    (hm : ∀ y, ∫ w, g y w ∂P = u y)
    (h2 : ∀ y, Integrable (fun w => ‖pack p (g y w) - pack p (u y)‖ ^ 2) P)
    (hv : ∀ y, (∫ w, ‖pack p (g y w) - pack p (u y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (ht : 0 < cfg.validationTolerance)
    (hsize : p.σ ^ 2 / (cfg.validationBatch : ℝ) ≤ cfg.validationTolerance ^ 2 / 144)
    (ρ : Measure (Fin cfg.steps)) [IsProbabilityMeasure ρ] (offset : ℕ) :
    (ρ.prod Q) {z | ¬ replyAccurate p cfg.validationTolerance
      (u (trialPoint p cfg g (fun l => ξ l z.2) z.1 offset))
      (trialEstimate p cfg g (fun l => ξ l z.2) z.1 offset)} ≤
      3 * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) := by
  have hstream : Measurable (fun z k => ξ k z) := Measurable.of_eval h.measurable
  have hpoint : Measurable (fun z : Fin cfg.steps × Ξ => trialPoint p cfg g (fun l => ξ l z.2) z.1 offset) :=
    measurable_from_prod_countable_right fun i => (measurable_trialPoint p cfg g hg i offset).comp hstream
  have hvalue : Measurable (fun z : Fin cfg.steps × Ξ => trialEstimate p cfg g (fun l => ξ l z.2) z.1 offset) :=
    measurable_from_prod_countable_right fun i => (measurable_trialEstimate p cfg g hg i offset).comp hstream
  have hA : MeasurableSet {z : Fin cfg.steps × Ξ | ¬ replyAccurate p cfg.validationTolerance
      (u (trialPoint p cfg g (fun l => ξ l z.2) z.1 offset))
      (trialEstimate p cfg g (fun l => ξ l z.2) z.1 offset)} :=
    (measurableSet_replyAccurate p cfg.validationTolerance
      (fun z : Fin cfg.steps × Ξ => u (trialPoint p cfg g (fun l => ξ l z.2) z.1 offset))
      (fun z : Fin cfg.steps × Ξ => trialEstimate p cfg g (fun l => ξ l z.2) z.1 offset)
      (hu.comp hpoint) hvalue).compl
  rw [Measure.prod_apply hA]
  apply (lintegral_mono (fun i => trial_estimate_confidence p cfg h g hg u hu hi hm h2 hv ht hsize i offset)).trans_eq
  simp

set_option maxHeartbeats 1000000 in
lemma trial_rejection_probability {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    (offset : ℕ) :
    let cfg := tuning p.toPublic
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    ((PMF.uniformOfFintype (Fin cfg.steps)).toMeasure.prod Q)
      {z | QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trialPlan p.toPublic cfg z.1) (2 * offset) = none} ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let ρ := (PMF.uniformOfFintype (Fin cfg.steps)).toMeasure
  let x := fun ξ => restorationTrace p.toPublic cfg g ξ offset cfg.restoreSteps
  let good := fun ξ => ‖I.c (x ξ)‖ ≤ 1 / (10 ^ 6 * S ^ 7)
  let τ := trainingOffset cfg offset
  let path := fun j ξ => (trainingTrace p.toPublic cfg g ξ (x ξ) τ j).point
  let A : Set (Fin cfg.steps × (ℕ → Ω)) := {z |
    ¬ StochasticEqualityProcess.active p.toPublic cfg (StochasticEqualityModel.truth I) path good cfg.steps z.2 ∨
      (p.ε / (32 * S)) ^ 2 < StochasticEqualityEnergy.residual p.toPublic (StochasticEqualityModel.truth I)
        (10 ^ 10 * S ^ 24) (trialPoint p.toPublic cfg g z.2 z.1 offset)}
  let B : Set (Fin cfg.steps × (ℕ → Ω)) := {z | ¬ replyAccurate p.toPublic cfg.validationTolerance
    (StochasticEqualityModel.truth I (trialPoint p.toPublic cfg g z.2 z.1 offset))
    (trialEstimate p.toPublic cfg g z.2 z.1 offset)}
  have hA : (ρ.prod Q) A ≤ ENNReal.ofReal (3 / 100 : ℝ) :=
    restored_selected_failure p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff offset
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have ht : 0 < cfg.validationTolerance := by
    change 0 < p.ε / (10 ^ 6 * S ^ 7)
    positivity
  have hB : (ρ.prod Q) B ≤ 3 * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) :=
    trial_estimate_confidence_product p.toPublic cfg
      (ξ := fun k (ξ : ℕ → Ω) => ξ k) (P := P) (Q := Q)
      (OracleTemplate.StochasticGeneralized.infinitePi_iid P) g hg
      (StochasticEqualityModel.truth I) (StochasticEqualityModel.admissible_truth_measurable p hp I O hI)
      hi hmean hnoise2 hnoise ht (StochasticEqualityTuning.tuning_robust_precision p hp).2 ρ offset
  have hs : (ρ.prod Q)
      {z | QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trialPlan p.toPublic cfg z.1) (2 * offset) = none} ≤
      (ρ.prod Q) (A ∪ B) := by
    apply measure_mono
    intro z hz
    by_cases ha : z ∈ A
    · exact Or.inl ha
    by_cases hb : z ∈ B
    · exact Or.inr hb
    exfalso
    have ha' : StochasticEqualityProcess.active p.toPublic cfg (StochasticEqualityModel.truth I) path good cfg.steps z.2 :=
      not_not.mp (not_or.mp ha).1
    have hr : StochasticEqualityEnergy.residual p.toPublic (StochasticEqualityModel.truth I)
        (10 ^ 10 * S ^ 24) (trialPoint p.toPublic cfg g z.2 z.1 offset) ≤ (p.ε / (32 * S)) ^ 2 :=
      not_lt.mp (not_or.mp ha).2
    have hv : replyAccurate p.toPublic cfg.validationTolerance
        (StochasticEqualityModel.truth I (trialPoint p.toPublic cfg g z.2 z.1 offset))
        (trialEstimate p.toPublic cfg g z.2 z.1 offset) := not_not.mp hb
    have hcap : ‖gradient I.f (trialPoint p.toPublic cfg g z.2 z.1 offset)‖ ≤ cfg.gradientCap := by
      have hk := StochasticEqualityProcess.active_mono p.toPublic cfg (StochasticEqualityModel.truth I)
        path good z.1.isLt.le z.2 ha'
      have hh := (StochasticEqualityProcess.active_caps p.toPublic cfg (StochasticEqualityModel.truth I)
        path good z.1.val z.2 hk).1
      change ‖gradient I.f (trainingTrace p.toPublic cfg g z.2 (x z.2) τ z.1.val).point‖ ≤ _ at hh
      simpa only [trialPoint, training_output_prefix, trainingTrace, trainingPrefixPlan, x, τ] using hh
    obtain ⟨μ, hμ⟩ := StochasticEqualityValidation.admissible_validate_complete p hp I O hI
      (trialPoint p.toPublic cfg g z.2 z.1 offset) (trialEstimate p.toPublic cfg g z.2 z.1 offset)
      hcap hr hv.1 hv.2.1 hv.2.2
    change QueryPlan.sampledEval g (fun i => z.2 (i / 2)) (trialPlan p.toPublic cfg z.1) (2 * offset) = none at hz
    rw [sampled_trial, hμ] at hz
    cases hz
  have hraw := hs.trans ((measure_union_le A B).trans (add_le_add hA hB))
  apply hraw.trans
  have hSge : 2 ≤ S := (StochasticEqualityTuning.scale_bounds p hp).1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hratio : 1 ≤ S / p.ε := (le_div_iff₀ hε).mpr (by linarith only [hSge, hε1])
  have hl := Real.log_nonneg hratio
  have hk4 : 4 ≤ (cfg.validationGroups : ℕ) := by
    change 4 ≤ positiveCeil (300 * (1 + Real.log (S / p.ε)))
    have hh := StochasticEqualityTuning.positiveCeil_lower (300 * (1 + Real.log (S / p.ε)))
    have hr : (4 : ℝ) ≤ (positiveCeil (300 * (1 + Real.log (S / p.ε))) : ℝ) := by linarith only [hh, hl]
    exact_mod_cast hr
  have hpow : (1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ) ≤ 1 / 16 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hk4
    norm_num at hh ⊢
    exact hh
  have hthree : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [hthree, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 100) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hpow]

lemma independent_seed_blocks {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (R H T : ℕ) (ρ : Measure (Fin T)) [IsProbabilityMeasure ρ] :
    MeasurePreserving
      (fun z : (Fin R → Fin T) × Ξ => fun i : Fin R => (z.1 i, fun j : Fin H => ξ (H * i.val + j.val) z.2))
      ((Measure.pi fun _ : Fin R => ρ).prod Q)
      (Measure.pi fun _ : Fin R => ρ.prod (Measure.pi fun _ : Fin H => P)) := by
  have hb : MeasurePreserving (fun z => fun i : Fin R => fun j : Fin H => ξ (H * i.val + j.val) z)
      Q (Measure.pi fun _ : Fin R => Measure.pi fun _ : Fin H => P) := by
    have hh := (measurePreserving_snd (μ := Measure.pi fun _ : Fin 0 => P)
      (ν := Measure.pi fun _ : Fin R => Measure.pi fun _ : Fin H => P)).comp (prefix_groups_law h 0 R H)
    simpa only [Function.comp_def, Nat.zero_add] using hh
  have he := MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow (Fin T) (Fin H → Ω) (Fin R))
    (measurePreserving_arrowProdEquivProdArrow (Fin T) (Fin H → Ω) (Fin R)
      (fun _ => ρ) (fun _ => Measure.pi fun _ : Fin H => P))
  exact he.comp ((MeasurePreserving.id (Measure.pi fun _ : Fin R => ρ)).prod hb)

end LongTails.Proofs.StochasticEqualityConfidence
