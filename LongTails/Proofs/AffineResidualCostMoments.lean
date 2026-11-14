import LongTails.Proofs.AffineResidualOuterCost
import LongTails.Proofs.AffineSoftmaxCostMoments

namespace LongTails.Proofs.AffineResidualCostMoments

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle (localSteps)
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualBudget
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot)

lemma referenceMultilevelCost_moments (m : ℕ) [NeZero m] {τ μ L r δ : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hδ : 0 < δ) (J : ℕ) :
    Integrable (fun seed => (referenceMultilevelCost m τ μ L r δ J seed : ℝ))
      (multilevelLaw : Measure MultilevelSeed) ∧
    (∫ seed, (referenceMultilevelCost m τ μ L r δ J seed : ℝ)
      ∂(multilevelLaw : Measure MultilevelSeed)) ≤ (2 + 3 * (J : ℝ)) * localSteps m τ μ L r δ := by
  let s : Snapshot (Fin m) ℝ := ⟨0, fun _ => 0, fun _ => 0⟩
  let reply := fun _ : Fin m × ℝ => ((0 : ℝ), (0 : ℝ))
  have hi := (AffineResidualCost.multilevelPlan_cost_integral Set.univ s τ μ L r δ J reply).1
  have hb := AffineResidualCost.multilevelPlan_cost_bound Set.univ s (r := r) hτ hμ hL hδ J reply
  constructor
  · simpa only [AffineResidualMultilevel.multilevelPlan_cost, Fintype.card_fin, referenceMultilevelCost] using hi
  · simpa only [AffineResidualMultilevel.multilevelPlan_cost, Fintype.card_fin, referenceMultilevelCost] using hb

lemma referenceFinalCost_moments (m : ℕ) [NeZero m] {τ L r floor : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (H J : ℕ) (hH : 0 < H) :
    let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
    let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
    Integrable (fun seed => (referenceFinalCost m τ L r floor H J seed : ℝ))
      (finalLaw : Measure FinalSeed) ∧
    (∫ seed, (referenceFinalCost m τ L r floor H J seed : ℝ) ∂(finalLaw : Measure FinalSeed)) ≤
      m + 2 * localSteps m τ floor L r δp + (2 + 3 * (J : ℝ)) * localSteps m τ floor L r δm := by
  let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
  let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hδm : 0 < δm := by dsimp [δm]; positivity
  have hg := referenceMultilevelCost_moments m (r := r) hτ hf hL hδm J
  let c := fun seed : MultilevelSeed => (referenceMultilevelCost m τ floor L r δm J seed : ℝ)
  have hgi : Integrable c (multilevelLaw : Measure MultilevelSeed) := hg.1
  have he (seed : FinalSeed) : (referenceFinalCost m τ L r floor H J seed : ℝ) =
      (m : ℝ) + 2 * localSteps m τ floor L r δp + c seed.2 := by
    simp only [referenceFinalCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, c, δp, δm]
  dsimp only
  simp_rw [he]
  have hi := (integrable_const ((m : ℝ) + 2 * localSteps m τ floor L r δp)).add
    (hgi.comp_snd (localLaw : Measure LocalSeed))
  refine ⟨hi, ?_⟩
  simp only [finalLaw, ProbabilityMeasure.coe_mk]
  rw [integral_add (integrable_const _) (hgi.comp_snd (localLaw : Measure LocalSeed)),
    integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [integral_fun_snd c, probReal_univ, one_smul]
  exact add_le_add (le_refl _) hg.2

lemma referenceOuterCost_moments (m : ℕ) [NeZero m] {τ L r floor : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (H b J : ℕ) (hH : 0 < H) :
    Integrable (fun seed => (referenceOuterCost m τ L r floor H b J seed : ℝ))
      (outerLaw : Measure OuterSeed) ∧
    (∫ seed, (referenceOuterCost m τ L r floor H b J seed : ℝ) ∂(outerLaw : Measure OuterSeed)) =
      ((2 * H + 9 : ℕ) : ℝ) * referenceProbeCost m τ L r floor b +
        ∫ seed, (referenceFinalCost m τ L r floor H J seed : ℝ) ∂(finalLaw : Measure FinalSeed) := by
  let f := fun seed : FinalSeed => (referenceFinalCost m τ L r floor H J seed : ℝ)
  have hfint : Integrable f (finalLaw : Measure FinalSeed) :=
    (referenceFinalCost_moments m hτ hL hr hf H J hH).1
  have he (seed : OuterSeed) : (referenceOuterCost m τ L r floor H b J seed : ℝ) =
      ((2 * H + 9 : ℕ) : ℝ) * referenceProbeCost m τ L r floor b + f seed.2 := by
    simp only [referenceOuterCost, Nat.cast_add, Nat.cast_mul, f]
  simp_rw [he]
  have hi := hfint.comp_snd
    (Measure.infinitePi (fun _ : ℕ => (LongTails.Algorithms.AffineResidualSearch.probeLaw : Measure LongTails.Algorithms.AffineResidualSearch.ProbeSeed)))
  refine ⟨(integrable_const _).add hi, ?_⟩
  simp only [outerLaw, ProbabilityMeasure.coe_mk]
  rw [integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul, integral_fun_snd]
  simp [f]

lemma referenceRunCost_moments (m : ℕ) [NeZero m] {τ L r floor : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (H b N J : ℕ) (hH : 0 < H) :
    let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
    let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
    Integrable (fun seeds => (referenceRunCost m τ L r floor H b N J seeds : ℝ))
      (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed))) ∧
    (∫ seeds, (referenceRunCost m τ L r floor H b N J seeds : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) ≤
      N * (((2 * H + 9 : ℕ) : ℝ) * referenceProbeCost m τ L r floor b +
        (m + 2 * localSteps m τ floor L r δp + (2 + 3 * (J : ℝ)) * localSteps m τ floor L r δm)) := by
  have ho := referenceOuterCost_moments m hτ hL hr hf H b J hH
  have hh := AffineSoftmaxCostMoments.iid_sum_cost_moments outerLaw
    (fun seed => (referenceOuterCost m τ L r floor H b J seed : ℝ)) ho.1 N
  have he (seeds : ℕ → OuterSeed) : (referenceRunCost m τ L r floor H b N J seeds : ℝ) =
      ∑ k ∈ Finset.range N, (referenceOuterCost m τ L r floor H b J (seeds k) : ℝ) := by
    simp only [referenceRunCost, Nat.cast_sum]
  dsimp only
  simp_rw [he]
  refine ⟨hh.1, ?_⟩
  rw [hh.2, ho.2]
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
    (referenceFinalCost_moments m hτ hL hr hf H J hH).2) (Nat.cast_nonneg N)

end LongTails.Proofs.AffineResidualCostMoments
