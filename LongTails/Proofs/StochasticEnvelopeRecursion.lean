import LongTails.Proofs.StochasticEnvelopeOracle
import LongTails.Proofs.StochasticEnvelopeWork
import LongTails.Algorithms.StochasticEnvelope
import LongTails.Proofs.StochasticEnvelopeLocalization
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Proofs.StochasticEnvelopeGeometry
open scoped RealInnerProductSpace
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def tower (f : E → ℝ) (field : E → E) (L : ℕ → ℝ) :
    ℕ → (E → ℝ) × (E → E)
  | 0 => (f, field)
  | i + 1 =>
      let previous := tower f field L i
      (envelope previous.1 previous.2 (L (i + 1)), envelopeField previous.2 (L (i + 1)))

lemma tower_model {f : E → ℝ} {field : E → E} {L : ℕ → ℝ}
    (h : Model (L 0) f field) (hL : ∀ i, 0 < L i) (i : ℕ) :
    Model (L i) (tower f field L i).1 (tower f field L i).2 := by
  induction i with
  | zero => exact h
  | succ i ih => exact ih.envelope_model (hL (i + 1))

lemma tower_min {f : E → ℝ} {field : E → E} {L : ℕ → ℝ}
    (h : Model (L 0) f field) (hL : ∀ i, 0 < L i)
    {xs : E} (hm : ∀ x, f xs ≤ f x) (i : ℕ) :
    (tower f field L i).1 xs = f xs ∧ ∀ x, f xs ≤ (tower f field L i).1 x := by
  induction i with
  | zero => exact ⟨rfl, hm⟩
  | succ i ih =>
    have hh := (tower_model h hL i).envelope_min_value (hL (i + 1))
      (xs := xs) (by simpa only [ih.1] using ih.2)
    simpa only [tower, ih.1] using hh

lemma tower_initial_gap {f : E → ℝ} {field : E → E} {L : ℕ → ℝ}
    (h : Model (L 0) f field) (hL : ∀ i, 0 < L i)
    {xs : E} (hm : ∀ x, f xs ≤ f x) (x : E) (i : ℕ) :
    (tower f field L (i + 1)).1 x - f xs ≤ L (i + 1) / 2 * ‖x - xs‖ ^ 2 := by
  have hh := (tower_model h hL i).envelope_initial_gap (hL (i + 1)) xs x
  simpa only [tower, (tower_min h hL hm i).1] using hh

omit [CompleteSpace E] in
lemma recovery_telescope {f : E → ℝ} {field : E → E} {L : ℕ → ℝ}
    (hL : ∀ i, 0 ≤ L i) (x : ℕ → E) (e : ℕ → ℝ) (d : ℕ)
    (he : ∀ i, i < d → regularized (tower f field L i).1 (L (i + 1)) (x (i + 1)) (x i) -
      (tower f field L (i + 1)).1 (x (i + 1)) ≤ e i) :
    f (x 0) ≤ (tower f field L d).1 (x d) + ∑ i ∈ Finset.range d, e i := by
  induction d with
  | zero => simp [tower]
  | succ d ih =>
    have hi := ih (fun i hi => he i (by omega))
    have hd := he d (by omega)
    have hLd := hL (d + 1)
    have hn : 0 ≤ L (d + 1) / 2 * ‖x d - x (d + 1)‖ ^ 2 := by positivity
    unfold regularized at hd
    rw [Finset.sum_range_succ]
    linarith

lemma recovery_prox_radius {f : E → ℝ} {field : E → E} {L : ℕ → ℝ}
    (h : Model (L 0) f field) (hL : ∀ i, 0 < L i)
    {xs : E} (hm : ∀ x, f xs ≤ f x) {ε : ℝ} (hε : 0 ≤ ε)
    (center : E) (i : ℕ)
    (hgap : (tower f field L (i + 1)).1 center - f xs ≤ ε) :
    ‖center - prox (tower f field L i).2 (L (i + 1)) center‖ ≤
      Real.sqrt (2 * ε / L (i + 1)) := by
  have hlo := (tower_min h hL hm i).2 (prox (tower f field L i).2 (L (i + 1)) center)
  change (tower f field L i).1 (prox (tower f field L i).2 (L (i + 1)) center) +
    L (i + 1) / 2 * ‖prox (tower f field L i).2 (L (i + 1)) center - center‖ ^ 2 - f xs ≤ ε at hgap
  rw [norm_sub_rev] at hgap
  have hLi := hL (i + 1)
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
  apply (le_div_iff₀ (hL (i + 1))).2
  nlinarith
section RecoveryAccuracy
lemma recovery_sample_accuracy {B D q : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (hq : 0 < q) :
    B * (1 + (B / D) ^ q) ^ (-(1 / q)) ≤ D := by
  have hn : 0 < 1 + (B / D) ^ q := by positivity
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg hB hD.le) q)
    (show (B / D) ^ q ≤ 1 + (B / D) ^ q by linarith) (by positivity : 0 ≤ 1 / q)
  rw [← Real.rpow_mul (div_nonneg hB hD.le), mul_one_div_cancel hq.ne', Real.rpow_one] at hh
  rw [Real.rpow_neg hn.le]
  apply (mul_inv_le_iff₀ (Real.rpow_pos_of_pos hn (1 / q))).2
  have hh' := (div_le_iff₀ hD).1 hh
  linarith

open RecursiveEnvelopeGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
lemma regularized_gap_of_distance {L μ e : ℝ} {f : E → ℝ} {field : E → E}
    (h : Model L f field) (hμ : 0 < μ) (he : 0 ≤ e) (center x : E)
    (hx : ‖x - prox field μ center‖ ≤ Real.sqrt (2 * e / (L + μ))) :
    regularized f μ center x - envelope f field μ center ≤ e := by
  have hM : 0 < L + μ := add_pos h.pos hμ
  have hu := h.regularized_upper center (prox field μ center) x (μ := μ)
  rw [h.prox_stationary hμ center, inner_zero_left, add_zero] at hu
  have hs := pow_le_pow_left₀ (norm_nonneg _) hx 2
  rw [Real.sq_sqrt (by positivity)] at hs
  have hs' := (le_div_iff₀ hM).1 hs
  change regularized f μ center x - regularized f μ center (prox field μ center) ≤ e
  nlinarith

end RecoveryAccuracy

section RecoveryProbability
open MeasureTheory OracleTemplate
open RecursiveEnvelopeGeometry
open LongTails.Algorithms.StochasticEnvelopeProgram LongTails.Algorithms.StochasticEnvelopeLocalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma recovery_failure {Ω : Type} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U e : ℝ} (h : Model L f field) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (he : 0 < e)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) (hU : ‖center - prox field μ center‖ ≤ U) {η : ℝ} (hη : 0 < η) :
    let D := Real.sqrt (2 * e / (L + μ))
    let c := recoveryTuning L μ p s a U D η
    let Q := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (c.replicas + 1) =>
      Measure.infinitePi fun _ : ℕ => (π : Measure Ω)
    let X := fun ξ => refineRun g L μ p s a U c.accuracyScale center center
      c.innerSteps c.replicas ξ c.stages
    Q {ξ | e < regularized f μ center (X ξ) - envelope f field μ center} ≤ ENNReal.ofReal η := by
  let D := Real.sqrt (2 * e / (L + μ))
  let n := 1 + ((s / μ + a * U) / D) ^ (p / (p - 1))
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hU
  have hM : 0 < L + μ := add_pos h.pos hμ
  have hD : 0 < D := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hn : 1 ≤ n := le_add_of_nonneg_right (by positivity)
  have hacc := recovery_sample_accuracy (show 0 ≤ s / μ + a * U by positivity) hD hq
  have hexp : -(1 / (p / (p - 1))) = -(p - 1) / p := by field_simp
  rw [hexp] at hacc
  have hh := StochasticEnvelopeLocalization.refineRun_stopped_failure π h hμ hp hp2 hs ha hn
    hκ haκ hg hi hmean hpi hm center center hU hU hη
  refine (measure_mono ?_).trans hh
  intro ξ hbad
  dsimp only [Set.mem_ofPred_eq] at hbad ⊢
  by_contra hnot
  have hdist := (le_of_not_gt hnot).trans hacc
  exact (not_lt_of_ge (regularized_gap_of_distance h hμ he.le center _ hdist)) hbad

end RecoveryProbability

end LongTails.Proofs.StochasticEnvelopeRecursion

open MeasureTheory
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeExecution
lemma measurable_calls (c : Parameters) (i : ℕ) : Measurable (calls c i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    change Measurable (fun seed : ℕ × (ℕ → Seed i) =>
      slotCalls (fun j => calls c i (seed.2 j)) (levelCalls c i seed.1) 0)
    apply measurable_from_prod_countable_right
    intro n
    simp only [slotCalls_sum, Nat.zero_add]
    apply Finset.measurable_sum
    intro j hj
    exact ih.comp (measurable_pi_apply j)

lemma measurable_recoveryCalls (c : Parameters) (i : ℕ) : Measurable (recoveryCalls c i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    change Measurable (fun seed : (ℕ → Seed i) × RecoverySeed i =>
      recoveryCalls c i seed.2 + slotCalls (fun j => calls c i (seed.1 j)) (recoveryLevelTuning c i).calls 0)
    apply (ih.comp measurable_snd).add
    simp only [slotCalls_sum, Nat.zero_add]
    apply Finset.measurable_sum
    intro j hj
    exact (measurable_calls c i).comp ((measurable_pi_apply j).comp measurable_fst)
lemma calls_integral (c : Parameters)
    (hn : ∀ j, Integrable (fun n => (levelCalls c j n : ℝ))
      (ProbabilityTheory.geometricMeasure c.levelProbability)) (i : ℕ) :
    Integrable (fun seed => (calls c i seed : ℝ)) (seedLaw c.levelProbability i : Measure (Seed i)) ∧
      (∫ seed, (calls c i seed : ℝ) ∂(seedLaw c.levelProbability i : Measure (Seed i))) =
        (c.batchSize : ℝ) * ∏ j ∈ Finset.range i,
          ∫ n, (levelCalls c j n : ℝ) ∂ProbabilityTheory.geometricMeasure c.levelProbability := by
  induction i with
  | zero =>
    change Integrable (fun _ : Unit => (c.batchSize : ℝ)) (Measure.dirac ()) ∧ _
    refine ⟨integrable_const _, ?_⟩
    simp [calls, seedLaw]
  | succ i ih =>
    have hh := StochasticEnvelopeWork.random_slot_work
      (seedLaw c.levelProbability i : Measure (Seed i))
      (ProbabilityTheory.geometricMeasure c.levelProbability)
      (measurable_calls c i) ih.1 (levelCalls c i) (hn i)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [ih.2, Finset.prod_range_succ]
    ring

lemma recoveryCalls_integral (c : Parameters)
    (hn : ∀ j, Integrable (fun n => (levelCalls c j n : ℝ))
      (ProbabilityTheory.geometricMeasure c.levelProbability)) (i : ℕ) :
    Integrable (fun seed => (recoveryCalls c i seed : ℝ))
      (recoverySeedLaw c.levelProbability i : Measure (RecoverySeed i)) ∧
      (∫ seed, (recoveryCalls c i seed : ℝ)
        ∂(recoverySeedLaw c.levelProbability i : Measure (RecoverySeed i))) =
        ∑ j ∈ Finset.range i, ((recoveryLevelTuning c j).calls : ℝ) *
          ((c.batchSize : ℝ) * ∏ k ∈ Finset.range j,
            ∫ n, (levelCalls c k n : ℝ) ∂ProbabilityTheory.geometricMeasure c.levelProbability) := by
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [recoveryCalls, Nat.cast_zero]
      exact integrable_const _
    · simp [recoveryCalls, recoverySeedLaw]
  | succ i ih =>
    let P := (seedLaw c.levelProbability i : Measure (Seed i))
    let R := Measure.infinitePi fun _ : ℕ => P
    let Q := (recoverySeedLaw c.levelProbability i : Measure (RecoverySeed i))
    have hg := calls_integral c hn i
    have hs := StochasticEnvelopeWork.slot_work_integral P hg.1 (recoveryLevelTuning c i).calls
    have hfst : MeasurePreserving Prod.fst (R.prod Q) R := measurePreserving_fst
    have hsnd : MeasurePreserving Prod.snd (R.prod Q) Q := measurePreserving_snd
    have hi1 : Integrable (fun w : (ℕ → Seed i) × RecoverySeed i => (recoveryCalls c i w.2 : ℝ)) (R.prod Q) :=
      hsnd.integrable_comp_of_integrable ih.1
    have hi2 : Integrable (fun w : (ℕ → Seed i) × RecoverySeed i =>
      (slotCalls (fun j => calls c i (w.1 j)) (recoveryLevelTuning c i).calls 0 : ℝ)) (R.prod Q) :=
      hfst.integrable_comp_of_integrable hs.1
    have he1 := hsnd.hasLaw.integral_comp ih.1.aestronglyMeasurable
    have he2 := hfst.hasLaw.integral_comp hs.1.aestronglyMeasurable
    simp only [Function.comp_apply] at he1 he2
    change Integrable (fun w : (ℕ → Seed i) × RecoverySeed i =>
      ((recoveryCalls c i w.2 + slotCalls (fun j => calls c i (w.1 j)) (recoveryLevelTuning c i).calls 0 : ℕ) : ℝ)) (R.prod Q) ∧ _
    simp only [Nat.cast_add]
    refine ⟨hi1.add hi2, ?_⟩
    change (∫ w : (ℕ → Seed i) × RecoverySeed i,
      ((recoveryCalls c i w.2 +
        slotCalls (fun j => calls c i (w.1 j)) (recoveryLevelTuning c i).calls 0 : ℕ) : ℝ) ∂R.prod Q) = _
    simp only [Nat.cast_add]
    rw [integral_add hi1 hi2, he1, he2, ih.2, hs.2, hg.2, Finset.sum_range_succ]

lemma recoveryCalls_integral_le (c : Parameters) (M : ℝ)
    (hn : ∀ j, Integrable (fun n => (levelCalls c j n : ℝ))
      (ProbabilityTheory.geometricMeasure c.levelProbability)) (d : ℕ)
    (hmean : ∀ j < d, (∫ n, (levelCalls c j n : ℝ)
      ∂ProbabilityTheory.geometricMeasure c.levelProbability) ≤ M) :
    (∫ seed, (recoveryCalls c d seed : ℝ)
      ∂(recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))) ≤
      ∑ j ∈ Finset.range d, ((recoveryLevelTuning c j).calls : ℝ) * (c.batchSize : ℝ) * M ^ j := by
  rw [(recoveryCalls_integral c hn d).2]
  apply Finset.sum_le_sum
  intro j hj
  have hprod : (∏ k ∈ Finset.range j, ∫ n, (levelCalls c k n : ℝ)
      ∂ProbabilityTheory.geometricMeasure c.levelProbability) ≤ M ^ j := by
    calc
      _ ≤ ∏ _k ∈ Finset.range j, M := Finset.prod_le_prod₀
        (fun k _ => integral_nonneg (fun n => Nat.cast_nonneg _))
        (fun k hk => hmean k (lt_trans (Finset.mem_range.mp hk) (Finset.mem_range.mp hj)))
      _ = _ := by simp
  calc
    _ ≤ ((recoveryLevelTuning c j).calls : ℝ) * ((c.batchSize : ℝ) * M ^ j) := by gcongr
    _ = _ := by ring

end LongTails.Proofs.StochasticEnvelopeRecursion

open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeExecution RecursiveEnvelopeExecution

section ProductLaw
variable {A B C V : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace V]
lemma fibred_identDistrib (P : Measure A) (Q : Measure B) (R : Measure C)
    [SFinite Q] [SFinite R] {F : A → B → V} {G : A → C → V}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hd : ∀ a, ProbabilityTheory.IdentDistrib (F a) (G a) Q R) :
    ProbabilityTheory.IdentDistrib (Function.uncurry F) (Function.uncurry G) (P.prod Q) (P.prod R) := by
  refine ⟨hF.aemeasurable, hG.aemeasurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hFφ : Measurable (fun w : A × B => φ (F w.1 w.2)) := hφ.comp hF
  have hGφ : Measurable (fun w : A × C => φ (G w.1 w.2)) := hφ.comp hG
  rw [lintegral_map hφ hF, lintegral_map hφ hG]
  change (∫⁻ w : A × B, φ (F w.1 w.2) ∂P.prod Q) = ∫⁻ w : A × C, φ (G w.1 w.2) ∂P.prod R
  rw [lintegral_prod _ hFφ.aemeasurable, lintegral_prod _ hGφ.aemeasurable]
  apply lintegral_congr
  intro a
  exact ((hd a).comp hφ).lintegral_eq
end ProductLaw
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def gradientValue (c : Parameters) (g : E → Ω → E) (i : ℕ)
    (x : E) (w : Seed i × (ℕ → Ω)) : E :=
  evalAt (fun j q => g q (w.2 j)) (gradientPlan c i w.1 x) 0

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma evalAt_batchPlan (g : E → Ω → E) (B : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalAt (fun j q => g q (ξ j)) (batchPlan B x) 0 = (B : ℝ)⁻¹ • ∑ i : Fin B, g x (ξ i.val) := by
  rw [batchPlan, evalAt_map, evalAt_castPlan, evalAt_collectPlans]
  simp only [evalAt, Nat.zero_add, Nat.one_mul]

lemma measurable_gradientValue {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (i : ℕ) : Measurable (Function.uncurry (gradientValue c g i)) := by
  induction i with
  | zero =>
      change Measurable (fun w : E × (Unit × (ℕ → Ω)) =>
        evalAt (fun j q => g q (w.2.2 j)) (batchPlan c.batchSize w.1) 0)
      simp_rw [evalAt_batchPlan]
      apply Measurable.const_smul
      apply Finset.measurable_sum
      intro j hj
      exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply j.val).comp measurable_snd.snd))
  | succ i ih =>
      have hh : Measurable (fun w : ℕ × (E × ((ℕ → Seed i) × (ℕ → Ω))) =>
          gradientValue c g (i + 1) w.2.1 ((w.1, w.2.2.1), w.2.2.2)) := by
        apply measurable_from_prod_countable_right
        intro n
        exact PlanFamily.substituted_family_measurable
          (fun _ => calls c i) (fun _ => measurable_calls c i)
          (fun _ => gradientPlan c i) g (fun _ => ih)
          (PlanFamily.tunedEnvelope _ _ _ _ _ _ _ measurable_id n)
      exact hh.comp (show Measurable (fun w : E × (Seed (i + 1) × (ℕ → Ω)) =>
        (w.2.1.1, (w.1, (w.2.1.2, w.2.2)))) by fun_prop)

lemma gradientValue_succ_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (i : ℕ) (point : E) :
    ProbabilityTheory.IdentDistrib (gradientValue c g (i + 1) point)
      (fun w : ℕ × (ℕ → Seed i × (ℕ → Ω)) =>
        evalAt (fun j x => gradientValue c g i x (w.2 j))
          (tunedEnvelopePlan (c.smoothness i) (c.smoothness (i + 1)) (c.moment i)
            (c.additive i) (c.relative i) c.baseWork c.levelProbability point w.1) 0)
      ((seedLaw c.levelProbability (i + 1) : Measure (Seed (i + 1))).prod (Measure.infinitePi fun _ : ℕ => P))
      ((ProbabilityTheory.geometricMeasure c.levelProbability).prod
        (Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i)).prod
          (Measure.infinitePi fun _ : ℕ => P))) := by
  let S := (seedLaw c.levelProbability i : Measure (Seed i))
  let R := Measure.infinitePi fun _ : ℕ => P
  let W := Measure.infinitePi fun _ : ℕ => S
  let G₀ := ProbabilityTheory.geometricMeasure c.levelProbability
  let F := fun n (w : (ℕ → Seed i) × (ℕ → Ω)) => gradientValue c g (i + 1) point ((n, w.1), w.2)
  let G := fun n (samples : ℕ → Seed i × (ℕ → Ω)) =>
    evalAt (fun j x => gradientValue c g i x (samples j))
      (tunedEnvelopePlan (c.smoothness i) (c.smoothness (i + 1)) (c.moment i)
        (c.additive i) (c.relative i) c.baseWork c.levelProbability point n) 0
  have hi := measurable_gradientValue hg c i
  have hF : Measurable (Function.uncurry F) := (measurable_gradientValue hg c (i + 1)).comp
    (show Measurable (fun w : ℕ × ((ℕ → Seed i) × (ℕ → Ω)) => (point, ((w.1, w.2.1), w.2.2))) by fun_prop)
  have hG : Measurable (Function.uncurry G) :=
    (StochasticEnvelopeOracle.measurable_tunedEnvelopePlan hi _ _ _ _ _ _ _).comp measurable_prodMk_left
  have hd : ∀ n, ProbabilityTheory.IdentDistrib (F n) (G n) (W.prod R)
      (Measure.infinitePi fun _ : ℕ => S.prod R) := by
    intro n
    exact PlanFamily.substituted_family_identDistrib S P
      (fun _ => calls c i) (fun _ => measurable_calls c i) (fun _ => gradientPlan c i) g (fun _ => hi)
      (PlanFamily.tunedEnvelope _ _ _ _ _ _ _ measurable_id n) point
  have hfib := fibred_identDistrib G₀ (W.prod R) (Measure.infinitePi fun _ : ℕ => S.prod R) hF hG hd
  have ha := measurePreserving_prodAssoc G₀ W R
  have hassoc : ProbabilityTheory.IdentDistrib
      (MeasurableEquiv.prodAssoc : (ℕ × (ℕ → Seed i)) × (ℕ → Ω) ≃ᵐ ℕ × (ℕ → Seed i) × (ℕ → Ω))
      id ((G₀.prod W).prod R) (G₀.prod (W.prod R)) :=
    ⟨ha.measurable.aemeasurable, measurable_id.aemeasurable, by simpa using ha.map_eq⟩
  exact (hassoc.comp hF).trans hfib

lemma gradientValue_zero_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (x : E) :
    ProbabilityTheory.IdentDistrib (gradientValue c g 0 x)
      (fun ξ : Fin c.batchSize → Ω => (c.batchSize : ℝ)⁻¹ • ∑ j, g x (ξ j))
      ((seedLaw c.levelProbability 0 : Measure (Seed 0)).prod (Measure.infinitePi fun _ : ℕ => P))
      (Measure.pi fun _ : Fin c.batchSize => P) := by
  have hm := (StochasticGeneralized.prefix_preserving P c.batchSize).comp
    (measurePreserving_snd (μ := (seedLaw c.levelProbability 0 : Measure (Seed 0)))
      (ν := Measure.infinitePi fun _ : ℕ => P))
  simp only [Function.comp_def] at hm
  have hX : Measurable (fun ξ : Fin c.batchSize → Ω => (c.batchSize : ℝ)⁻¹ • ∑ j, g x (ξ j)) := by
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro j hj
    exact hg.comp (measurable_const.prodMk (measurable_pi_apply j))
  refine ⟨((measurable_gradientValue hg c 0).comp measurable_prodMk_left).aemeasurable,
    hX.aemeasurable, ?_⟩
  change (Measure.map (fun w : Seed 0 × (ℕ → Ω) =>
    evalAt (fun j q => g q (w.2 j)) (batchPlan c.batchSize x) 0) _) = _
  simp_rw [evalAt_batchPlan]
  calc
    _ = (((seedLaw c.levelProbability 0 : Measure (Seed 0)).prod (Measure.infinitePi fun _ : ℕ => P)).map
        (fun w : Seed 0 × (ℕ → Ω) => fun j : Fin c.batchSize => w.2 j)).map
        (fun ξ => (c.batchSize : ℝ)⁻¹ • ∑ j, g x (ξ j)) := (Measure.map_map hX hm.measurable).symm
    _ = _ := by rw [hm.map_eq]

lemma gradientValue_zero_contract [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    (c : Parameters) {s a : ℝ}
    (hp : 1 < c.moment 0) (hp2 : c.moment 0 ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hB : 0 < c.batchSize)
    (hs0 : 4 * (c.batchSize : ℝ) ^ (-(1 / (c.moment 0 / (c.moment 0 - 1)))) * s ≤ c.additive 0)
    (ha0 : 4 * (c.batchSize : ℝ) ^ (-(1 / (c.moment 0 / (c.moment 0 - 1)))) * a ≤ c.relative 0)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ c.moment 0) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ c.moment 0 ∂P) ≤
      s ^ c.moment 0 + a ^ c.moment 0 * ‖field x‖ ^ c.moment 0) (x : E) :
    let Q := (seedLaw c.levelProbability 0 : Measure (Seed 0)).prod (Measure.infinitePi fun _ : ℕ => P)
    let Y := gradientValue c g 0 x
    Integrable Y Q ∧ (∫ w, Y w ∂Q) = field x ∧
      Integrable (fun w => ‖Y w - field x‖ ^ c.moment 0) Q ∧
      (∫ w, ‖Y w - field x‖ ^ c.moment 0 ∂Q) ≤
        (c.additive 0) ^ c.moment 0 + (c.relative 0) ^ c.moment 0 * ‖field x‖ ^ c.moment 0 := by
  have hb := StochasticEnvelopeSampling.batch_affine_moment P hp hp2 hs ha hg hi hmean hpi hm c.batchSize hB x
  have hd := gradientValue_zero_identDistrib hg c P x
  have hd' := hd.comp (show Measurable (fun z : E => ‖z - field x‖ ^ c.moment 0) by fun_prop)
  refine ⟨hd.integrable_iff.mpr hb.1, hd.integral_eq.trans hb.2.1,
    hd'.integrable_iff.mpr hb.2.2.1, hd'.integral_eq.trans_le (hb.2.2.2.trans ?_)⟩
  exact add_le_add (Real.rpow_le_rpow (by positivity) hs0 (by linarith))
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) ha0 (by linarith)) (by positivity))

noncomputable def gradientLaw (c : Parameters) (P : Measure Ω) (i : ℕ) : Measure (Seed i × (ℕ → Ω)) :=
  (seedLaw c.levelProbability i : Measure (Seed i)).prod (Measure.infinitePi fun _ : ℕ => P)

instance gradientLaw_probability (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (i : ℕ) :
    IsProbabilityMeasure (gradientLaw c P i) := by unfold gradientLaw; infer_instance

lemma gradientValue_succ_contract [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E} {f : E → ℝ}
    (c : Parameters) (i : ℕ) {t : ℝ} (h : RecursiveEnvelopeGeometry.Model (c.smoothness i) f field)
    (hμ : 0 < c.smoothness (i + 1)) (hp : 1 < c.moment i) (hp2 : c.moment i ≤ 2)
    (hs : 0 ≤ c.additive i) (ha : 0 < c.relative i) (hm1 : 1 ≤ c.baseWork)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hv : c.levelProbability = levelProbability t ht.le ht1)
    (hκ : 2 ≤ (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1))
    (haκ : c.relative i ≤ ((c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)) ^ (-2 : ℝ))
    (hexp : c.moment (i + 1) =
      (c.moment i / (c.moment i - 1) * (1 + t)) / (c.moment i / (c.moment i - 1) * (1 + t) - 1))
    (hsnext : (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t *
      c.baseWork ^ (-(c.moment (i + 1) / (c.moment i / (c.moment i - 1)))) *
        (c.additive i) ^ c.moment (i + 1) ≤ (c.additive (i + 1)) ^ c.moment (i + 1))
    (hanext : (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t *
      c.baseWork ^ (-(c.moment (i + 1) / (c.moment i / (c.moment i - 1)))) *
        (c.relative i) ^ c.moment (i + 1) ≤ (c.relative (i + 1)) ^ c.moment (i + 1))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (gradientValue c g i x) (gradientLaw c P i))
    (hmean : ∀ x, ∫ w, gradientValue c g i x w ∂gradientLaw c P i = field x)
    (hpi : ∀ x, Integrable (fun w => ‖gradientValue c g i x w - field x‖ ^ c.moment i) (gradientLaw c P i))
    (hm : ∀ x, (∫ w, ‖gradientValue c g i x w - field x‖ ^ c.moment i ∂gradientLaw c P i) ≤
      (c.additive i) ^ c.moment i + (c.relative i) ^ c.moment i * ‖field x‖ ^ c.moment i)
    (x : E) :
    let Q := gradientLaw c P (i + 1)
    let Y := gradientValue c g (i + 1) x
    let target := RecursiveEnvelopeGeometry.envelopeField field (c.smoothness (i + 1)) x
    Integrable Y Q ∧ (∫ w, Y w ∂Q) = target ∧
      Integrable (fun w => ‖Y w - target‖ ^ c.moment (i + 1)) Q ∧
      (∫ w, ‖Y w - target‖ ^ c.moment (i + 1) ∂Q) ≤
        (c.additive (i + 1)) ^ c.moment (i + 1) +
          (c.relative (i + 1)) ^ c.moment (i + 1) * ‖target‖ ^ c.moment (i + 1) := by
  have hh := StochasticEnvelopeOracle.tunedEnvelopePlan_contract (gradientLaw c P i) h hμ hp hp2 hs ha hm1
    ht ht1 hκ haκ (measurable_gradientValue hg c i) hi hmean hpi hm x
  dsimp only at hh
  rw [← hexp, ← hv] at hh
  have hd := gradientValue_succ_identDistrib hg c P i x
  have hd' := hd.comp (show Measurable (fun z : E =>
    ‖z - RecursiveEnvelopeGeometry.envelopeField field (c.smoothness (i + 1)) x‖ ^ c.moment (i + 1)) by fun_prop)
  refine ⟨hd.integrable_iff.mpr hh.1, hd.integral_eq.trans hh.2.1,
    hd'.integrable_iff.mpr hh.2.2.1, hd'.integral_eq.trans_le (hh.2.2.2.trans ?_)⟩
  rw [mul_add, ← mul_assoc]
  exact add_le_add hsnext (mul_le_mul_of_nonneg_right hanext (by positivity))

lemma gradientValue_contract [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E} {f : E → ℝ}
    (c : Parameters) (d : ℕ) {s a t : ℝ}
    (h : RecursiveEnvelopeGeometry.Model (c.smoothness 0) f field)
    (hL : ∀ j, 0 < c.smoothness j)
    (hp : ∀ j, j ≤ d → 1 < c.moment j) (hp2 : ∀ j, j ≤ d → c.moment j ≤ 2)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hB : 0 < c.batchSize)
    (hs0 : 4 * (c.batchSize : ℝ) ^ (-(1 / (c.moment 0 / (c.moment 0 - 1)))) * s ≤ c.additive 0)
    (ha0 : 4 * (c.batchSize : ℝ) ^ (-(1 / (c.moment 0 / (c.moment 0 - 1)))) * a ≤ c.relative 0)
    (hsj : ∀ j, j < d → 0 ≤ c.additive j) (haj : ∀ j, j < d → 0 < c.relative j)
    (hm1 : 1 ≤ c.baseWork) (ht : 0 < t) (ht1 : t ≤ 1)
    (hv : c.levelProbability = levelProbability t ht.le ht1)
    (hκ : ∀ j, j < d → 2 ≤ (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1))
    (haκ : ∀ j, j < d → c.relative j ≤
      ((c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1)) ^ (-2 : ℝ))
    (hexp : ∀ j, j < d → c.moment (j + 1) =
      (c.moment j / (c.moment j - 1) * (1 + t)) / (c.moment j / (c.moment j - 1) * (1 + t) - 1))
    (hsnext : ∀ j, j < d → (2 : ℝ) ^ (28 : ℝ) * (c.moment j / (c.moment j - 1)) / t *
      c.baseWork ^ (-(c.moment (j + 1) / (c.moment j / (c.moment j - 1)))) *
        (c.additive j) ^ c.moment (j + 1) ≤ (c.additive (j + 1)) ^ c.moment (j + 1))
    (hanext : ∀ j, j < d → (2 : ℝ) ^ (28 : ℝ) * (c.moment j / (c.moment j - 1)) / t *
      c.baseWork ^ (-(c.moment (j + 1) / (c.moment j / (c.moment j - 1)))) *
        (c.relative j) ^ c.moment (j + 1) ≤ (c.relative (j + 1)) ^ c.moment (j + 1))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ c.moment 0) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ c.moment 0 ∂P) ≤
      s ^ c.moment 0 + a ^ c.moment 0 * ‖field x‖ ^ c.moment 0) :
    ∀ i, i ≤ d → ∀ x : E,
      Integrable (gradientValue c g i x) (gradientLaw c P i) ∧
      (∫ w, gradientValue c g i x w ∂gradientLaw c P i) = (tower f field c.smoothness i).2 x ∧
      Integrable (fun w => ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i)
        (gradientLaw c P i) ∧
      (∫ w, ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i ∂gradientLaw c P i) ≤
        (c.additive i) ^ c.moment i + (c.relative i) ^ c.moment i * ‖(tower f field c.smoothness i).2 x‖ ^ c.moment i := by
  intro i
  induction i with
  | zero =>
      intro _ x
      exact gradientValue_zero_contract P c (hp 0 (Nat.zero_le d)) (hp2 0 (Nat.zero_le d)) hs ha hB hs0 ha0
        hg hi hmean hpi hm x
  | succ i ih =>
      intro hid x
      have hid' : i < d := by omega
      have hprev := ih (by omega : i ≤ d)
      exact gradientValue_succ_contract P c i (tower_model h hL i) (hL (i + 1))
        (hp i (by omega)) (hp2 i (by omega)) (hsj i hid') (haj i hid') hm1 ht ht1 hv
        (hκ i hid') (haκ i hid') (hexp i hid') (hsnext i hid') (hanext i hid') hg
        (fun y => (hprev y).1) (fun y => (hprev y).2.1)
        (fun y => (hprev y).2.2.1) (fun y => (hprev y).2.2.2) x

lemma call_cap_probability {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsFiniteMeasure P] {cost : S → ℕ} (hi : Integrable (fun s => (cost s : ℝ)) P)
    {K : ℕ} (hK : 0 < K) {δ : ℝ}
    (hmean : (∫ s, (cost s : ℝ) ∂P) ≤ δ * (K : ℝ)) :
    P.real {s | K < cost s} ≤ δ := by
  have hreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun s => Nat.cast_nonneg (α := ℝ) (cost s))) hi (K : ℝ)
  have hset : {s | K < cost s} ⊆ {s | (K : ℝ) ≤ (cost s : ℝ)} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    exact_mod_cast (le_of_lt hs)
  have hprob := measureReal_mono (μ := P) hset
  nlinarith

end LongTails.Proofs.StochasticEnvelopeRecursion

open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Algorithms.StochasticEnvelopeLocalization
open StochasticEnvelopeExecution RecursiveEnvelopeExecution StochasticEnvelopeTransport RecursiveEnvelopeGeometry
variable {Ω : Type} [MeasurableSpace Ω]

abbrev RecoveryIndex (v : ℕ) := ℕ × Fin (v + 1) × ℕ

def recoveryUsed (K J v : ℕ) (i : RecoveryIndex v) : Prop := i.1 < J ∧ i.2.2 < K

def recoveryFlat (K v : ℕ) (i : RecoveryIndex v) : ℕ := K * (v + 1) * i.1 + K * i.2.1.val + i.2.2

lemma recoveryFlat_bound (K J v : ℕ) (i : RecoveryIndex v) (hi : recoveryUsed K J v i) :
    recoveryFlat K v i < K * (v + 1) * J := by
  have h1 := radix_lt i.2.1.isLt hi.1
  have h2 := radix_lt hi.2 h1
  dsimp [recoveryFlat]
  nlinarith

lemma recoveryFlat_inj (K J v : ℕ) : Set.InjOn (recoveryFlat K v) {i | recoveryUsed K J v i} := by
  rintro ⟨i, a, k⟩ hi ⟨j, b, l⟩ hj he
  have he' : K * ((v + 1) * i + a.val) + k = K * ((v + 1) * j + b.val) + l := by
    convert he using 1 <;> dsimp [recoveryFlat] <;> ring
  obtain ⟨hij, hkl⟩ := radix_inj hi.2 hj.2 he'
  obtain ⟨hij, hab⟩ := radix_inj a.isLt b.isLt hij
  have hab' : a = b := Fin.ext hab
  change k = l at hkl
  subst j; subst b; subst l
  rfl

noncomputable def coupledRecovery (K v J : ℕ) (ξ : ℕ → Ω) : ℕ → Fin (v + 1) → ℕ → Ω :=
  fun j i k => ξ (completeIndex (recoveryUsed K J v) (recoveryFlat K v) (K * (v + 1) * J) (j, i, k))

lemma coupledRecovery_preserving (P : Measure Ω) [IsProbabilityMeasure P] (K v J : ℕ) :
    MeasurePreserving (coupledRecovery (Ω := Ω) K v J) (Measure.infinitePi fun _ : ℕ => P)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (v + 1) => Measure.infinitePi fun _ : ℕ => P) := by
  have hh := (infinitePi_curry_three_preserving (A := ℕ) (B := Fin (v + 1)) (D := ℕ) P).comp
    (completeIndex_preserving P (recoveryUsed K J v) (recoveryFlat K v) (K * (v + 1) * J)
      (recoveryFlat_bound K J v) (recoveryFlat_inj K J v))
  unfold coupledRecovery
  have hpi : (Measure.infinitePi fun _ : Fin (v + 1) => Measure.infinitePi fun _ : ℕ => P) =
      (Measure.pi fun _ : Fin (v + 1) => Measure.infinitePi fun _ : ℕ => P) := Measure.infinitePi_eq_pi _
  rw [hpi] at hh
  convert hh using 1
  rfl

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [MeasurableSpace Ω] in
lemma evalAt_refinePlan_coupled (g : E → Ω → E) (L μ p s a U n : ℝ) (center start : E)
    (K v J : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun j x => g x (ξ j)) (refinePlan L μ p s a U n center start K v J) 0 =
      refineRun g L μ p s a U n center start K v (coupledRecovery K v J ξ) J := by
  rw [evalAt_refinePlan]
  apply refineRun_samples_congr
  intro j hj i k hk
  unfold coupledRecovery
  rw [completeIndex_used _ _ _ (j, i, k) (show recoveryUsed K J v (j, i, k) from ⟨hj, hk⟩)]
  simp only [Nat.zero_add, recoveryFlat]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_recoveryPlan {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a U D η : ℝ) :
    Measurable (fun w : E × (ℕ → Ω) => evalAt (fun j x => g x (w.2 j))
      (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan L μ p s a U D η w.1) 0) := by
  let c := recoveryTuning L μ p s a U D η
  have hh := StochasticEnvelopeMeasurability.measurable_refineRun_center hg L μ p s a c.accuracyScale
    measurable_fst (show Measurable (fun _ : E × (ℕ → Ω) => U) from measurable_const)
    measurable_fst c.innerSteps c.replicas
    (show Measurable (fun w : E × (ℕ → Ω) => coupledRecovery c.innerSteps c.replicas c.stages w.2) by
      unfold coupledRecovery; fun_prop) c.stages
  convert hh using 1
  funext w
  exact evalAt_refinePlan_coupled g L μ p s a U c.accuracyScale w.1 w.1 c.innerSteps c.replicas c.stages w.2

lemma recoveryPlan_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (P : Measure Ω) [IsProbabilityMeasure P] (L μ p s a U D η : ℝ) (center : E) :
    let c := recoveryTuning L μ p s a U D η
    ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Ω => evalAt (fun j x => g x (ξ j))
        (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan L μ p s a U D η center) 0)
      (fun ξ => refineRun g L μ p s a U c.accuracyScale center center c.innerSteps c.replicas ξ c.stages)
      (Measure.infinitePi fun _ : ℕ => P)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (c.replicas + 1) => Measure.infinitePi fun _ : ℕ => P) := by
  let c := recoveryTuning L μ p s a U D η
  have hc := coupledRecovery_preserving P c.innerSteps c.replicas c.stages
  have hX := StochasticEnvelopeLocalization.measurable_refineRun hg L μ p s a c.accuracyScale center
    (show Measurable (fun _ : ℕ → Fin (c.replicas + 1) → ℕ → Ω => U) from measurable_const)
    (show Measurable (fun _ : ℕ → Fin (c.replicas + 1) → ℕ → Ω => center) from measurable_const)
    c.innerSteps c.replicas measurable_id c.stages
  refine ⟨((measurable_recoveryPlan hg L μ p s a U D η).comp measurable_prodMk_left).aemeasurable,
    hX.aemeasurable, ?_⟩
  change (Measure.infinitePi fun _ : ℕ => P).map (fun ξ => evalAt (fun j x => g x (ξ j))
    (refinePlan L μ p s a U c.accuracyScale center center c.innerSteps c.replicas c.stages) 0) = _
  simp_rw [evalAt_refinePlan_coupled]
  calc
    _ = ((Measure.infinitePi fun _ : ℕ => P).map (coupledRecovery c.innerSteps c.replicas c.stages)).map
        (fun ξ => refineRun g L μ p s a U c.accuracyScale center center c.innerSteps c.replicas ξ c.stages) :=
      (Measure.map_map hX hc.measurable).symm
    _ = _ := by rw [hc.map_eq]


lemma recoveryPlan_failure [CompleteSpace E]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U e : ℝ} (h : Model L f field) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (he : 0 < e)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) (hU : ‖center - prox field μ center‖ ≤ U) {η : ℝ} (hη : 0 < η) :
    (Measure.infinitePi fun _ : ℕ => (π : Measure Ω))
      {ξ | e < regularized f μ center
        (evalAt (fun j x => g x (ξ j))
          (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan L μ p s a U
            (Real.sqrt (2 * e / (L + μ))) η center) 0) - envelope f field μ center}
      ≤ ENNReal.ofReal η := by
  have hd := recoveryPlan_identDistrib hg (π : Measure Ω) L μ p s a U
    (Real.sqrt (2 * e / (L + μ))) η center
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (StochasticEnvelopeGeometry.model_hasGradientAt h x).differentiableAt.continuousAt)
  have hmreg : Measurable (fun x => regularized f μ center x - envelope f field μ center) := by
    unfold regularized
    fun_prop
  have heq := hd.measure_mem_eq (s := {x | e < regularized f μ center x - envelope f field μ center})
    (measurableSet_lt measurable_const hmreg)
  exact heq.trans_le (recovery_failure π h hμ hp hp2 hs ha he hκ haκ hg hi hmean hpi hm center hU hη)


noncomputable def recoveryStepValue (c : Parameters) (g : E → Ω → E) (i : ℕ)
    (x : E) (w : (ℕ → Seed i) × (ℕ → Ω)) : E :=
  evalAt (fun j q => g q (w.2 j))
    (substitutePlan (fun j => calls c i (w.1 j)) (fun j => gradientPlan c i (w.1 j))
      (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan
        (c.smoothness i) (c.smoothness (i + 1)) (c.moment i) (c.additive i) (c.relative i)
        (c.recoveryRadius i) (c.recoveryDistance i) c.recoveryFailure x) 0) 0

lemma measurable_recoveryStepValue {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (i : ℕ) : Measurable (Function.uncurry (recoveryStepValue c g i)) := by
  exact PlanFamily.substituted_family_measurable
    (fun _ => calls c i) (fun _ => measurable_calls c i)
    (fun _ => gradientPlan c i) g (fun _ => measurable_gradientValue hg c i)
    (PlanFamily.recovery _ _ _ _ _ _ _ _ measurable_id)

lemma recoveryStepValue_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (i : ℕ) (point : E) :
    ProbabilityTheory.IdentDistrib (recoveryStepValue c g i point)
      (fun w : ℕ → Seed i × (ℕ → Ω) =>
        evalAt (fun j x => gradientValue c g i x (w j))
          (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan
            (c.smoothness i) (c.smoothness (i + 1)) (c.moment i) (c.additive i) (c.relative i)
            (c.recoveryRadius i) (c.recoveryDistance i) c.recoveryFailure point) 0)
      ((Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
        (Measure.infinitePi fun _ : ℕ => P))
      (Measure.infinitePi fun _ : ℕ => gradientLaw c P i) := by
  exact PlanFamily.substituted_family_identDistrib (seedLaw c.levelProbability i : Measure (Seed i)) P
    (fun _ => calls c i) (fun _ => measurable_calls c i) (fun _ => gradientPlan c i) g
    (fun _ => measurable_gradientValue hg c i) (PlanFamily.recovery _ _ _ _ _ _ _ _ measurable_id) point

end LongTails.Proofs.StochasticEnvelopeRecursion

open MeasureTheory OracleTemplate
open scoped ENNReal
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeExecution RecursiveEnvelopeExecution StochasticEnvelopeFreshness
section Generic
variable {S T Ω U : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace Ω] [MeasurableSpace U]

lemma bind_seed_prefix_preserving (Q : Measure S) (Tlaw : Measure T) (P : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Tlaw] [IsProbabilityMeasure P]
    {cost : S → ℕ} (hc : Measurable cost) (F : S × (ℕ → Ω) → U) (hF : Measurable F)
    (hdep : ∀ s ξ ζ, (∀ j, j < cost s → ξ j = ζ j) → F (s, ξ) = F (s, ζ)) :
    MeasurePreserving
      (fun w : (S × T) × (ℕ → Ω) =>
        ((w.1.1, F (w.1.1, w.2)), (w.1.2, fun j => w.2 (cost w.1.1 + j))))
      ((Q.prod Tlaw).prod (Measure.infinitePi fun _ : ℕ => P))
      (((Q.prod (Measure.infinitePi fun _ : ℕ => P)).map (fun w => (w.1, F w))).prod
        (Tlaw.prod (Measure.infinitePi fun _ : ℕ => P))) := by
  let R := Measure.infinitePi fun _ : ℕ => P
  let M := (Q.prod R).map (fun w => (w.1, F w))
  have h1 := swap_middle_preserving Q Tlaw R
  have h2 := (seed_prefix_tail_preserving P Q hc F hF hdep).prod (MeasurePreserving.id Tlaw)
  have h3 := swap_middle_preserving M R Tlaw
  have h4 := measurePreserving_prodAssoc M Tlaw R
  convert h4.comp (h3.comp (h2.comp h1)) using 1
  rfl


end Generic
variable {Ω : Type} [MeasurableSpace Ω]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def recoveryStepCalls (c : Parameters) (i : ℕ) (seed : ℕ → Seed i) : ℕ :=
  slotCalls (fun j => calls c i (seed j)) (recoveryLevelTuning c i).calls 0

lemma measurable_recoveryStepCalls (c : Parameters) (i : ℕ) : Measurable (recoveryStepCalls c i) := by
  unfold recoveryStepCalls
  simp only [slotCalls_sum, Nat.zero_add]
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_calls c i).comp (measurable_pi_apply j)

noncomputable def recoveryValue (c : Parameters) (g : E → Ω → E) (i : ℕ)
    (x : E) (w : RecoverySeed i × (ℕ → Ω)) : E :=
  evalAt (fun j q => g q (w.2 j)) (recoverPlan c i w.1 x) 0

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma recoveryValue_succ (c : Parameters) (g : E → Ω → E) (i : ℕ)
    (x : E) (w : RecoverySeed (i + 1) × (ℕ → Ω)) :
    recoveryValue c g (i + 1) x w =
      recoveryValue c g i (recoveryStepValue c g i x (w.1.1, w.2))
        (w.1.2, fun j => w.2 (recoveryStepCalls c i w.1.1 + j)) := by
  rcases w with ⟨⟨upper, lower⟩, ξ⟩
  let plan := substitutePlan (fun j => calls c i (upper j)) (fun j => gradientPlan c i (upper j))
    (LongTails.Algorithms.StochasticEnvelopeProgram.recoveryPlan (c.smoothness i) (c.smoothness (i + 1))
      (c.moment i) (c.additive i) (c.relative i) (c.recoveryRadius i) (c.recoveryDistance i)
      c.recoveryFailure x) 0
  change evalAt (fun j q => g q (ξ j)) (plan.bind (recoverPlan c i lower)) 0 =
    evalAt (fun j q => g q (ξ (recoveryStepCalls c i upper + j)))
      (recoverPlan c i lower (recoveryStepValue c g i x (upper, ξ))) 0
  rw [evalAt_bind]
  simp only [Nat.zero_add]
  exact (evalAt_shift _ _ _ 0).symm

lemma measurable_recoveryValue {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (i : ℕ) : Measurable (Function.uncurry (recoveryValue c g i)) := by
  induction i with
  | zero => exact measurable_fst
  | succ i ih =>
      have hS : Measurable (fun w : E × (RecoverySeed (i + 1) × (ℕ → Ω)) =>
          recoveryStepValue c g i w.1 (w.2.1.1, w.2.2)) :=
        (measurable_recoveryStepValue hg c i).comp
          (show Measurable (fun w : E × (((ℕ → Seed i) × RecoverySeed i) × (ℕ → Ω)) =>
            (w.1, (w.2.1.1, w.2.2))) by fun_prop)
      have hT : Measurable (fun w : E × (RecoverySeed (i + 1) × (ℕ → Ω)) =>
          fun j => w.2.2 (recoveryStepCalls c i w.2.1.1 + j)) :=
        (measurable_seed_shift (measurable_recoveryStepCalls c i)).comp
          (show Measurable (fun w : E × (((ℕ → Seed i) × RecoverySeed i) × (ℕ → Ω)) =>
            (w.2.1.1, w.2.2)) by fun_prop)
      convert ih.comp (hS.prodMk (measurable_snd.fst.snd.prodMk hT)) using 1
      funext w
      exact recoveryValue_succ c g i w.1 w.2

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma recoveryStepValue_prefix (c : Parameters) (g : E → Ω → E) (i : ℕ)
    (x : E) (seed : ℕ → Seed i) (ξ ζ : ℕ → Ω)
    (heq : ∀ j, j < recoveryStepCalls c i seed → ξ j = ζ j) :
    recoveryStepValue c g i x (seed, ξ) = recoveryStepValue c g i x (seed, ζ) := by
  apply evalAt_prefix_congr
  intro j hj q
  simp only [Nat.zero_add]
  rw [heq j hj]

lemma recovery_split_preserving {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (i : ℕ) (x : E) :
    MeasurePreserving
      (fun w : RecoverySeed (i + 1) × (ℕ → Ω) =>
        ((w.1.1, recoveryStepValue c g i x (w.1.1, w.2)),
          (w.1.2, fun j => w.2 (recoveryStepCalls c i w.1.1 + j))))
      ((recoverySeedLaw c.levelProbability (i + 1) : Measure (RecoverySeed (i + 1))).prod
        (Measure.infinitePi fun _ : ℕ => P))
      ((((Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
          (Measure.infinitePi fun _ : ℕ => P)).map
            (fun w => (w.1, recoveryStepValue c g i x w))).prod
        ((recoverySeedLaw c.levelProbability i : Measure (RecoverySeed i)).prod
          (Measure.infinitePi fun _ : ℕ => P))) := by
  exact bind_seed_prefix_preserving _ _ P (measurable_recoveryStepCalls c i)
    (recoveryStepValue c g i x)
    ((measurable_recoveryStepValue hg c i).comp measurable_prodMk_left)
    (recoveryStepValue_prefix c g i x)


lemma recoveryValue_failure_from_steps {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → E → ℝ) (hF : ∀ i, Measurable (F i)) (b : ℕ → ℝ)
    (η : ℝ≥0∞) (d : ℕ)
    (hstep : ∀ i, i < d → ∀ x, F (i + 1) x ≤ b (i + 1) →
      ((Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
        (Measure.infinitePi fun _ : ℕ => P))
        {w | b i < F i (recoveryStepValue c g i x w)} ≤ η)
    (x : E) (hx : F d x ≤ b d) :
    ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | b 0 < F 0 (recoveryValue c g d x w)} ≤ (d : ℝ≥0∞) * η := by
  induction d generalizing x with
  | zero =>
      have he : {w : RecoverySeed 0 × (ℕ → Ω) | b 0 < F 0 (recoveryValue c g 0 x w)} = ∅ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_lt_of_ge hx
      rw [he, measure_empty]
      simp
  | succ i ih =>
      let Q := (Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
        (Measure.infinitePi fun _ : ℕ => P)
      let M := Q.map (fun w => (w.1, recoveryStepValue c g i x w))
      let R := (recoverySeedLaw c.levelProbability i : Measure (RecoverySeed i)).prod
        (Measure.infinitePi fun _ : ℕ => P)
      let B : Set ((ℕ → Seed i) × E) := {u | b i < F i u.2}
      let bad : Set (((ℕ → Seed i) × E) × (RecoverySeed i × (ℕ → Ω))) :=
        {w | b 0 < F 0 (recoveryValue c g i w.1.2 w.2)}
      have hB : MeasurableSet B := measurableSet_lt measurable_const ((hF i).comp measurable_snd)
      have hbad : MeasurableSet bad := measurableSet_lt measurable_const
        ((hF 0).comp ((measurable_recoveryValue hg c i).comp (measurable_fst.snd.prodMk measurable_snd)))
      have hupper : M B ≤ η := by
        dsimp only [M]
        have hmap : Measurable (fun w : (ℕ → Seed i) × (ℕ → Ω) =>
            (w.1, recoveryStepValue c g i x w)) := measurable_fst.prodMk
              ((measurable_recoveryStepValue hg c i).comp (measurable_const.prodMk measurable_id))
        rw [Measure.map_apply hmap hB]
        exact hstep i (Nat.lt_succ_self i) x hx
      have htotal := product_failure_probability M R hbad hB hupper
        (show ∀ u, u ∉ B → R {v | (u, v) ∈ bad} ≤ (i : ℝ≥0∞) * η by
          intro u hu
          exact ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self i))) u.2 (le_of_not_gt hu))
      have hp := recovery_split_preserving hg c P i x
      have he : ((recoverySeedLaw c.levelProbability (i + 1) : Measure (RecoverySeed (i + 1))).prod
          (Measure.infinitePi fun _ : ℕ => P))
          {w | b 0 < F 0 (recoveryValue c g (i + 1) x w)} = (M.prod R) bad := by
        rw [← hp.map_eq, Measure.map_apply hp.measurable hbad]
        congr 1
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, bad, recoveryValue_succ]
      rw [he]
      convert htotal using 1
      push_cast
      ring

end LongTails.Proofs.StochasticEnvelopeRecursion

open MeasureTheory OracleTemplate
open scoped ENNReal
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeExecution RecursiveEnvelopeExecution RecursiveEnvelopeGeometry
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma recoveryStepValue_failure {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P] (i : ℕ)
    {f : E → ℝ} {field : E → E} {e : ℝ}
    (h : Model (c.smoothness i) f field) (hμ : 0 < c.smoothness (i + 1))
    (hp : 1 < c.moment i) (hp2 : c.moment i ≤ 2) (hs : 0 ≤ c.additive i)
    (ha : 0 < c.relative i) (he : 0 < e)
    (hκ : 2 ≤ (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1))
    (haκ : c.relative i ≤ ((c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)) ^ (-2 : ℝ))
    (hD : c.recoveryDistance i = Real.sqrt (2 * e / (c.smoothness i + c.smoothness (i + 1))))
    (hη : 0 < c.recoveryFailure)
    (hcontract : ∀ x, Integrable (gradientValue c g i x) (gradientLaw c P i) ∧
      (∫ w, gradientValue c g i x w ∂gradientLaw c P i) = field x ∧
      Integrable (fun w => ‖gradientValue c g i x w - field x‖ ^ c.moment i) (gradientLaw c P i) ∧
      (∫ w, ‖gradientValue c g i x w - field x‖ ^ c.moment i ∂gradientLaw c P i) ≤
        c.additive i ^ c.moment i + c.relative i ^ c.moment i * ‖field x‖ ^ c.moment i)
    (center : E) (hU : ‖center - prox field (c.smoothness (i + 1)) center‖ ≤ c.recoveryRadius i) :
    ((Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | e < regularized f (c.smoothness (i + 1)) center (recoveryStepValue c g i center w) -
        envelope f field (c.smoothness (i + 1)) center} ≤ ENNReal.ofReal c.recoveryFailure := by
  let π : ProbabilityMeasure (Seed i × (ℕ → Ω)) := ⟨gradientLaw c P i, inferInstance⟩
  have hr := recoveryPlan_failure π h hμ hp hp2 hs ha he hκ haκ (measurable_gradientValue hg c i)
    (fun x => (hcontract x).1) (fun x => (hcontract x).2.1)
    (fun x => (hcontract x).2.2.1) (fun x => (hcontract x).2.2.2) center hU hη
  have hd := recoveryStepValue_identDistrib hg c P i center
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (StochasticEnvelopeGeometry.model_hasGradientAt h x).differentiableAt.continuousAt)
  have hreg : Measurable (fun x => regularized f (c.smoothness (i + 1)) center x -
      envelope f field (c.smoothness (i + 1)) center) := by
    unfold regularized
    fun_prop
  have heq := hd.measure_mem_eq
    (s := {x | e < regularized f (c.smoothness (i + 1)) center x -
      envelope f field (c.smoothness (i + 1)) center}) (measurableSet_lt measurable_const hreg)
  rw [hD] at heq
  exact heq.trans_le hr


lemma recoveryValue_tower_failure {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (P : Measure Ω) [IsProbabilityMeasure P]
    {f : E → ℝ} {field : E → E} {xs : E} {ε e : ℝ} (d : ℕ)
    (h : Model (c.smoothness 0) f field) (hL : ∀ i, 0 < c.smoothness i)
    (hmin : ∀ x, f xs ≤ f x) (hε : 0 ≤ ε) (he : 0 < e)
    (hp : ∀ i, i < d → 1 < c.moment i) (hp2 : ∀ i, i < d → c.moment i ≤ 2)
    (hs : ∀ i, i < d → 0 ≤ c.additive i) (ha : ∀ i, i < d → 0 < c.relative i)
    (hκ : ∀ i, i < d → 2 ≤ (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1))
    (haκ : ∀ i, i < d → c.relative i ≤
      ((c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)) ^ (-2 : ℝ))
    (hD : ∀ i, i < d → c.recoveryDistance i = Real.sqrt (2 * e / (c.smoothness i + c.smoothness (i + 1))))
    (hU : ∀ i, i < d → Real.sqrt (2 * ε / c.smoothness (i + 1)) ≤ c.recoveryRadius i)
    (hη : 0 < c.recoveryFailure)
    (hcontract : ∀ i, i < d → ∀ x,
      Integrable (gradientValue c g i x) (gradientLaw c P i) ∧
      (∫ w, gradientValue c g i x w ∂gradientLaw c P i) = (tower f field c.smoothness i).2 x ∧
      Integrable (fun w => ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i)
        (gradientLaw c P i) ∧
      (∫ w, ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i
        ∂gradientLaw c P i) ≤ c.additive i ^ c.moment i +
        c.relative i ^ c.moment i * ‖(tower f field c.smoothness i).2 x‖ ^ c.moment i)
    (x : E) (hx : (tower f field c.smoothness d).1 x - f xs ≤ ε - (d : ℝ) * e) :
    ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | ε < f (recoveryValue c g d x w) - f xs} ≤ (d : ℝ≥0∞) * ENNReal.ofReal c.recoveryFailure := by
  have hFm : ∀ i, Measurable (fun z => (tower f field c.smoothness i).1 z - f xs) := by
    intro i
    have hc : Continuous (tower f field c.smoothness i).1 := continuous_iff_continuousAt.mpr
      (fun z => (StochasticEnvelopeGeometry.model_hasGradientAt (tower_model h hL i) z).differentiableAt.continuousAt)
    exact hc.measurable.sub_const _
  have hh := recoveryValue_failure_from_steps hg c P
    (fun i z => (tower f field c.smoothness i).1 z - f xs) hFm (fun i => ε - (i : ℝ) * e)
    (ENNReal.ofReal c.recoveryFailure) d
  have hstep : ∀ i, i < d → ∀ center,
      (tower f field c.smoothness (i + 1)).1 center - f xs ≤ ε - ((i + 1 : ℕ) : ℝ) * e →
      ((Measure.infinitePi fun _ : ℕ => (seedLaw c.levelProbability i : Measure (Seed i))).prod
        (Measure.infinitePi fun _ : ℕ => P))
        {w | ε - (i : ℝ) * e < (tower f field c.smoothness i).1 (recoveryStepValue c g i center w) - f xs}
        ≤ ENNReal.ofReal c.recoveryFailure := by
    intro i hi center hgap
    have hgapε : (tower f field c.smoothness (i + 1)).1 center - f xs ≤ ε := by
      have hn : 0 ≤ ((i + 1 : ℕ) : ℝ) * e := by positivity
      linarith
    have hradius := (recovery_prox_radius h hL hmin hε center i hgapε).trans (hU i hi)
    have hfail := recoveryStepValue_failure hg c P i (tower_model h hL i) (hL (i + 1))
      (hp i hi) (hp2 i hi) (hs i hi) (ha i hi) he (hκ i hi) (haκ i hi)
      (hD i hi) hη (hcontract i hi) center hradius
    refine (measure_mono ?_).trans hfail
    intro w hw
    change ε - (i : ℝ) * e < (tower f field c.smoothness i).1 (recoveryStepValue c g i center w) - f xs at hw
    change e < regularized (tower f field c.smoothness i).1 (c.smoothness (i + 1)) center
      (recoveryStepValue c g i center w) - (tower f field c.smoothness (i + 1)).1 center
    have hLi := hL (i + 1)
    have hn : 0 ≤ c.smoothness (i + 1) / 2 * ‖recoveryStepValue c g i center w - center‖ ^ 2 := by positivity
    unfold regularized
    push_cast at hgap
    linarith
  simpa only [Nat.cast_zero, zero_mul, sub_zero, tower] using hh hstep x hx

end LongTails.Proofs.StochasticEnvelopeRecursion
