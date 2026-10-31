import LongTails.Proofs.AffineMomentBatch
import LongTails.Proofs.AffineMomentParameters
import LongTails.Proofs.RobustGeneralizedOracle

open MeasureTheory
open scoped BigOperators
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentParameters

namespace LongTails.Proofs.AffineMomentOracle

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pilotEstimate_congr (t : Tuning) (v w : ℕ → E)
    (h : ∀ i < sampleSize t, v i = w i) : pilotEstimate t v = pilotEstimate t w := by
  unfold pilotEstimate
  congr 1
  funext i
  unfold OracleTemplate.RobustGeneralized.meanBlock
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply h
  have hi := Nat.mul_le_mul_right (batchSize t) (Nat.succ_le_of_lt i.isLt)
  have hj := j.isLt
  simp only [Nat.succ_mul] at hi
  unfold sampleSize
  rw [Nat.mul_comm (batchSize t) (pilotGroups t)]
  omega

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma blockAdvance_congr (t : Tuning) (k : ℕ) (s : E × E) (v w : ℕ → E)
    (h : ∀ i < blockSize t, v i = w i) : blockAdvance t k s v = blockAdvance t k s w := by
  have hp := pilotEstimate_congr t v w (fun i hi => h i (by unfold blockSize; omega))
  unfold blockAdvance
  rw [hp]
  congr 1
  unfold OracleTemplate.RobustGeneralized.meanBlock
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply h
  have hi := i.isLt
  unfold blockSize
  omega

lemma pilot_failure {t : Tuning} (ht : Valid t) {oracle : E → Ω → E}
    (x q : E) (hV : Measurable (oracle x)) (hVi : Integrable (oracle x) P)
    (hmean : (∫ ω, oracle x ω ∂P) = q)
    (hVp : Integrable (fun ω => ‖oracle x ω - q‖ ^ t.p) P)
    (hm : (∫ ω, ‖oracle x ω - q‖ ^ t.p ∂P) ≤ t.σ0 ^ t.p + t.σ ^ t.p * ‖q‖ ^ t.p) :
    (Measure.pi fun _ : Fin (sampleSize t) => P)
      {ξ | (‖q‖ + pilotRadius t) / 8 < ‖pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle x ξ) - q‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ pilotGroups t) := by
  unfold sampleSize
  rw [Nat.mul_comm (batchSize t) (pilotGroups t)]
  let G := fun ξ : Fin (pilotGroups t * batchSize t) → Ω =>
    fun i : Fin (pilotGroups t) => fun j : Fin (batchSize t) => ξ ⟨i * batchSize t + j, by
      have hi := Nat.mul_le_mul_right (batchSize t) (Nat.succ_le_of_lt i.isLt)
      simp only [Nat.succ_mul] at hi
      have hj := j.isLt
      omega⟩
  let C := fun ξ : Fin (pilotGroups t) → Fin (batchSize t) → Ω =>
    OracleTemplate.AffineGradient.center (1 / 24) (pilotRadius t)
      (fun i => (1 / (batchSize t : ℝ)) • ∑ j, oracle x (ξ i j))
  have hG : MeasurePreserving G (Measure.pi fun _ : Fin (pilotGroups t * batchSize t) => P)
      (Measure.pi fun _ : Fin (pilotGroups t) => Measure.pi fun _ : Fin (batchSize t) => P) :=
    OracleTemplate.RobustGradient.finite_groups_preserving P (pilotGroups t) (batchSize t)
  have hC : Measurable C := (OracleTemplate.AffineGradient.measurable_center (pilotRadius t) (pilotGroups t)).comp
    (measurable_const.prodMk (by fun_prop))
  have he (ξ : Fin (pilotGroups t * batchSize t) → Ω) :
      pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle x ξ) = C (G ξ) := by
    unfold pilotEstimate C OracleTemplate.RobustGeneralized.meanBlock
    congr 1
    funext i
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hij : (i : ℕ) * batchSize t + j < pilotGroups t * batchSize t := by
      have hi := Nat.mul_le_mul_right (batchSize t) (Nat.succ_le_of_lt i.isLt)
      simp only [Nat.succ_mul] at hi
      have hj := j.isLt
      omega
    simp [OracleTemplate.RobustGeneralized.sampleReplies, hij, G]
  have hsize : 6 / (batchSize t : ℝ) ^ (t.p - 1) * (noiseScale t) ^ t.p ≤ ((1 / 24 : ℝ) / 8) ^ t.p / 16 := by
    norm_num
    exact batch_relative_moment ht
  have hscaled : (∫ ω, ‖oracle x ω - q‖ ^ t.p ∂P) ≤
      (noiseScale t) ^ t.p * (‖q‖ + pilotRadius t) ^ t.p :=
    hm.trans (AffineMomentBatch.affine_scale_bound (le_of_lt ht.exponent_gt) ht.noise_nonneg
      ht.additive_nonneg (pilotRadius_pos ht) (norm_nonneg q))
  have h := LongTails.Proofs.AffineMomentBatch.affine_means_failure ht.exponent_gt ht.exponent_le
    (pilotRadius_pos ht) hV hVi q hmean hVp hscaled (by norm_num : (0 : ℝ) < 1 / 24) (by norm_num)
    (pilotGroups t) (batchSize t) (batchSize_pos ht) hsize
  have hset : MeasurableSet {ξ | (‖q‖ + pilotRadius t) / 8 < ‖C ξ - q‖} :=
    measurableSet_lt measurable_const (hC.sub_const _).norm
  have hmapp := hG.measure_preimage hset.nullMeasurableSet
  have hcoef : (3 : ℝ) * (1 / 24) * (‖q‖ + pilotRadius t) = (‖q‖ + pilotRadius t) / 8 := by ring
  rw [hcoef] at h
  change (Measure.pi fun _ : Fin (pilotGroups t) => Measure.pi fun _ : Fin (batchSize t) => P)
    {ξ | (‖q‖ + pilotRadius t) / 8 < ‖C ξ - q‖} ≤ _ at h
  rw [← hmapp] at h
  simpa only [Set.preimage, Set.mem_ofPred_eq, ← he] using h

end LongTails.Proofs.AffineMomentOracle
