import LongTails.Proofs.SurjectiveConfidenceTuning
import LongTails.Proofs.SurjectiveConfidenceExecution
import LongTails.Proofs.AdaptiveEntropicStateMeasurable
import LongTails.Proofs.ValidatedHessianSampling

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.SurjectiveConfidenceProbability

lemma replicated_bad_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω)
    (_hA : MeasurableSet A) (hB : MeasurableSet B) {a b : ℝ≥0∞}
    (ha : P A ≤ a) (hb : P B ≤ b) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P)
      {z | (∀ i, z i ∈ A) ∨ (∃ i, z i ∈ B)} ≤ a ^ n + n * b := by
  let Q := Measure.pi fun _ : Fin n => P
  have hAll : Q {z | ∀ i, z i ∈ A} ≤ a ^ n := by
    have hid : {z : Fin n → Ω | ∀ i, z i ∈ A} = Set.univ.pi (fun _ => A) := by
      ext z
      simp
    rw [hid, Measure.pi_pi]
    simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => ha)
  have hAny : Q {z | ∃ i, z i ∈ B} ≤ n * b := by
    have hid : {z : Fin n → Ω | ∃ i, z i ∈ B} = ⋃ i : Fin n, {z | z i ∈ B} := by
      ext z
      simp
    rw [hid]
    apply (measure_iUnion_le _).trans
    calc
      ∑' i : Fin n, Q {z | z i ∈ B} ≤ ∑' _ : Fin n, b := by
        apply ENNReal.tsum_le_tsum
        intro i
        have hi := (measurePreserving_eval (fun _ : Fin n => P) i).measure_preimage hB.nullMeasurableSet
        exact hi.trans_le hb
      _ = n * b := by simp
  exact (measure_union_le _ _).trans (add_le_add hAll hAny)

lemma block_replica_failure {T Ω Y : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace Y]
    (R : Measure T) (P : Measure Ω) [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    (F : T × (ℕ → Ω) → Y) (hF : Measurable F) (L n : ℕ)
    (hdep : ∀ t ξ η, (∀ j < L, ξ j = η j) → F (t, ξ) = F (t, η))
    (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) {a b : ℝ≥0∞}
    (ha : (R.prod (Measure.infinitePi fun _ : ℕ => P)) (F ⁻¹' A) ≤ a)
    (hb : (R.prod (Measure.infinitePi fun _ : ℕ => P)) (F ⁻¹' B) ≤ b) :
    ((Measure.pi fun _ : Fin n => R).prod (Measure.infinitePi fun _ : ℕ => P))
      {z | (∀ i : Fin n, F (z.1 i, fun j => z.2 (L * i.val + j)) ∈ A) ∨
        (∃ i : Fin n, F (z.1 i, fun j => z.2 (L * i.val + j)) ∈ B)} ≤ a ^ n + n * b := by
  obtain ⟨ω0, _⟩ := nonempty_of_measure_ne_zero (show P Set.univ ≠ 0 by simp)
  let G : T × (Fin L → Ω) → Y := fun z =>
    F (z.1, HessianAdaptiveCubicMoments.prefixExtend ω0 L z.2)
  have hG : Measurable G := hF.comp
    (measurable_fst.prodMk ((HessianAdaptiveCubicMoments.measurable_prefixExtend ω0 L).comp measurable_snd))
  have hGF (t : T) (ξ : ℕ → Ω) : G (t, fun i => ξ i) = F (t, ξ) := by
    symm
    apply hdep
    intro j hj
    simp [HessianAdaptiveCubicMoments.prefixExtend, hj]
  have hshift (t : T) (ξ : ℕ → Ω) (offset : ℕ) :
      G (t, fun i => ξ (offset + i.val)) = F (t, fun j => ξ (offset + j)) :=
    hGF t (fun j => ξ (offset + j))
  have hlaw := (MeasurePreserving.id R).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving P L)
  have hga : (R.prod (Measure.pi fun _ : Fin L => P)) (G ⁻¹' A) ≤ a := by
    rw [← hlaw.measure_preimage (hG hA).nullMeasurableSet]
    simpa only [Set.preimage_preimage, Function.comp_def, Prod.map, id_eq, hGF] using ha
  have hgb : (R.prod (Measure.pi fun _ : Fin L => P)) (G ⁻¹' B) ≤ b := by
    rw [← hlaw.measure_preimage (hG hB).nullMeasurableSet]
    simpa only [Set.preimage_preimage, Function.comp_def, Prod.map, id_eq, hGF] using hb
  have hrep := replicated_bad_bound (R.prod (Measure.pi fun _ : Fin L => P))
    (G ⁻¹' A) (G ⁻¹' B) (hG hA) (hG hB) hga hgb n
  have hblocks := ValidatedHessianSampling.target_blocks_preserving R P n L
  have hAllM : MeasurableSet {z : Fin n → T × (Fin L → Ω) | ∀ i, z i ∈ G ⁻¹' A} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i : Fin n => (measurable_pi_apply i) (hG hA))
  have hAnyM : MeasurableSet {z : Fin n → T × (Fin L → Ω) | ∃ i, z i ∈ G ⁻¹' B} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun i : Fin n => (measurable_pi_apply i) (hG hB))
  have hset : MeasurableSet {z : Fin n → T × (Fin L → Ω) |
      (∀ i, z i ∈ G ⁻¹' A) ∨ (∃ i, z i ∈ G ⁻¹' B)} := hAllM.union hAnyM
  have he := hblocks.measure_preimage hset.nullMeasurableSet
  rw [← he] at hrep
  simpa only [Set.preimage_ofPred_eq, Set.mem_preimage, hshift, Nat.mul_comm] using hrep

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearSampling
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma candidate_step_failure (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)))
      {z | radius p / 8 < ‖exactModelStep p I
        (trajectory p (jointOracle p g v D) z.2 z.1.val).1‖} ≤ ENNReal.ofReal (1 / 2) := by
  have hs := selected_step_second_moment p I hp H g v D μ O
  have hr := (variance_scales_positive p hp).2.1
  have h := RobustGradient.norm_tail_le_second_moment hs.1
    (by positivity : 0 < radius p / 8) hs.2
  have hh : (radius p ^ 2 / 128) / (radius p / 8) ^ 2 = (1 / 2 : ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hh] at h
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

end LongTails.Proofs.SurjectiveConfidenceProbability
