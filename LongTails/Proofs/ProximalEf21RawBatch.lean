import LongTails.Proofs.ProximalEf21StochasticContraction

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21RawBatch

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21StochasticContraction

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma ordered_noise_orthogonality {B : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ ‹MeasurableSpace Ω›)
    (ζ : Fin B → Ω → E)
    (hlp : ∀ j, MemLp (ζ j) 2 P)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[filtration j] (ζ i) P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0)) :
    ∀ i j, i ≠ j → (∫ ω, ⟪ζ i ω, ζ j ω⟫_ℝ ∂P) = 0 := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact predictable_inner_centered_noise P (filtration j) (hfiltration j)
      (ζ i) (ζ j) (hlp i) (hlp j) (hpast i j hlt) (hcentered j)
  · have h := predictable_inner_centered_noise P (filtration i) (hfiltration i)
      (ζ j) (ζ i) (hlp j) (hlp i) (hpast j i hgt) (hcentered i)
    calc
      (∫ ω, ⟪ζ i ω, ζ j ω⟫_ℝ ∂P) = (∫ ω, ⟪ζ j ω, ζ i ω⟫_ℝ ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun _ => real_inner_comm _ _)
      _ = 0 := h

lemma miniBatch_from_raw_samples {B : ℕ} (hB : 0 < B)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ ‹MeasurableSpace Ω›)
    (ζ : Fin B → Ω → E) (σ : ℝ)
    (hlp : ∀ j, MemLp (ζ j) 2 P)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[filtration j] (ζ i) P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0))
    (hvariance : ∀ j, ∀ᵐ ω ∂P,
      condExp (filtration j) P (fun ω' => ‖ζ j ω'‖ ^ 2) ω ≤ σ ^ 2) :
    MemLp (fun ω => (B : ℝ)⁻¹ • ∑ j, ζ j ω) 2 P ∧
    (∫ ω, ‖(B : ℝ)⁻¹ • ∑ j, ζ j ω‖ ^ 2 ∂P) ≤ σ ^ 2 / B := by
  refine ⟨workerMean_memLp P ζ hlp, ?_⟩
  apply miniBatch_second_moment hB P ζ (σ ^ 2)
  · intro i j
    exact integrable_inner_of_memLp_two P _ _ (hlp i) (hlp j)
  · exact ordered_noise_orthogonality P filtration hfiltration ζ hlp hpast hcentered
  · intro j
    exact conditional_variance_to_integral P (filtration j) (hfiltration j)
      (ζ j) (σ ^ 2) (hvariance j)

lemma miniBatch_orthogonal_to_initial_state {B : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ ‹MeasurableSpace Ω›)
    (ζ : Fin B → Ω → E) (u : Ω → E)
    (hlp : ∀ j, MemLp (ζ j) 2 P) (hu : MemLp u 2 P)
    (hpredictable : ∀ j, AEStronglyMeasurable[filtration j] u P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0)) :
    (∫ ω, ⟪u ω, (B : ℝ)⁻¹ • ∑ j, ζ j ω⟫_ℝ ∂P) = 0 := by
  have hz : ∀ j, (∫ ω, ⟪u ω, ζ j ω⟫_ℝ ∂P) = 0 := by
    intro j
    exact predictable_inner_centered_noise P (filtration j) (hfiltration j)
      u (ζ j) hu (hlp j) (hpredictable j) (hcentered j)
  simp_rw [real_inner_smul_right, inner_sum]
  rw [integral_const_mul, integral_finset_sum]
  · simp only [hz, Finset.sum_const_zero, mul_zero]
  · intro j hj
    exact integrable_inner_of_memLp_two P _ _ hu (hlp j)

lemma raw_sample_number (B K : ℕ) :
    (∑ _ ∈ Finset.range K, B) = B * K := by
  simp [Nat.mul_comm]

end LongTails.Proofs.ProximalEf21RawBatch
