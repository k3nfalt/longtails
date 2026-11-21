import LongTails.Algorithms.DistributedGrowthSgd
import LongTails.Proofs.StrongGrowthWeights
import LongTails.Proofs.WeightedInterpolationPrecision

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedGrowthSchedule

open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.DistributedGrowthSgd LongTails.Algorithms.StrongGrowthWeights
open StrongGrowthWeights


variable {p : Params}

lemma peak_pos (hp : spec.valid p) : 0 < peak p :=
  (signal_pos hp 0).trans_le (Finset.le_sup' (signal p) (Finset.mem_univ 0))

lemma signal_le_n (hp : spec.valid p) (i : Fin p.n) : signal p i ≤ p.n := by
  rw [← signal_sum hp]
  exact Finset.single_le_sum (fun j _ => (signal_pos hp j).le) (Finset.mem_univ i)

lemma cap_ge (hp : spec.valid p) (i : Fin p.n) : p.μ * signal p i ≤ cap p i := by
  unfold cap
  split
  · apply (le_div_iff₀ (signal_pos hp i)).mpr
    have h := mul_le_mul hp.2.2.1 (signal_le_n hp i) (signal_pos hp i).le
      (hp.2.1.trans_le hp.2.2.1).le
    have hh := mul_le_mul h (Finset.le_sup' (signal p) (Finset.mem_univ i))
      (signal_pos hp i).le (mul_nonneg (hp.2.1.trans_le hp.2.2.1).le (by positivity))
    change _ ≤ _ * peak p at hh
    nlinarith only [hh, mul_nonneg (mul_nonneg (show 0 ≤ (p.n : ℝ) by positivity)
      (hp.2.1.trans_le hp.2.2.1).le) (peak_pos hp).le]
  · exact le_rfl

lemma valid (hp : spec.valid p) : LongTails.Setups.DistributedWeakInterpolation.spec.valid (schedule p) := by
  refine ⟨hp.1,fun i => (mul_pos hp.2.1 (signal_pos hp i)).le.trans (cap_ge hp i),hp.2.1,?_,
    hp.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2⟩
  change p.n * p.μ ≤ ∑ i, cap p i
  rw [mul_comm, ← signal_sum hp, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => cap_ge hp i

lemma profile_eq (hp : spec.valid p) (i : Fin p.n) :
    Algorithms.WeakInterpolationDesign.profile (schedule p) i = p.μ * signal p i := by
  classical
  let c := p.μ * Finset.univ.sup' Finset.univ_nonempty (weight p)
  have hh (j : Fin p.n) : weight p j * (p.h j : ℝ) = signal p j :=
    div_mul_cancel₀ _ (speed hp j).ne'
  have hcap (j : Fin p.n) : min (cap p j) (c * p.h j) = p.μ * signal p j := by
    have hle : p.μ * signal p j ≤ c * p.h j := by
      rw [← hh j, ← mul_assoc]
      gcongr
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (weight p) (Finset.mem_univ j)) hp.2.1.le
    by_cases hj : weight p j = Finset.univ.sup' Finset.univ_nonempty (weight p)
    · have he : c * p.h j = p.μ * signal p j := by dsimp [c]; rw [← hj,mul_assoc,hh]
      rw [he,min_eq_right (cap_ge hp j)]
    · rw [show cap p j = _ from ite_eq_right hj, min_eq_left hle]
  have hsum := (WeakInterpolationDesign.threshold_spec (valid hp)).2
  have hm : ∑ j, Algorithms.WeakInterpolationDesign.profile (schedule p) j = ∑ j, p.μ * signal p j := by
    rw [hsum, ← Finset.mul_sum, signal_sum hp]
    change p.n * p.μ = _
    ring
  rcases le_total (Algorithms.WeakInterpolationDesign.threshold (schedule p)) c with h | h
  · apply (Finset.sum_eq_sum_iff_of_le (fun j _ => ?_)).mp hm i (Finset.mem_univ i)
    rw [← hcap]
    exact min_le_min_left _ (mul_le_mul_of_nonneg_right h (p.h j).coe_nonneg)
  · symm
    apply (Finset.sum_eq_sum_iff_of_le (fun j _ => ?_)).mp hm.symm i (Finset.mem_univ i)
    rw [← hcap]
    exact min_le_min_left _ (mul_le_mul_of_nonneg_right h (p.h j).coe_nonneg)

lemma weight_eq (hp : spec.valid p) (i : Fin p.n) :
    Algorithms.WeakInterpolationDesign.weights (schedule p) i = p.μ * weight p i := by
  change Algorithms.WeakInterpolationDesign.profile (schedule p) i / (p.h i : ℝ) = _
  rw [profile_eq hp, weight, mul_div_assoc]

lemma info_eq (hp : spec.valid p) :
    Algorithms.WeakInterpolationDesign.information (schedule p) = p.μ^2 * information p := by
  unfold Algorithms.WeakInterpolationDesign.information information
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weight_eq hp,profile_eq hp]
  ring

lemma largest_eq (hp : spec.valid p) :
    Algorithms.WeakInterpolationDesign.largestCurvature (schedule p) = p.μ * (3*p.n*p.L) * peak p := by
  classical
  have hL := hp.2.1.trans_le hp.2.2.1
  have ht (i : Fin p.n) (hi : weight p i = Finset.univ.sup' Finset.univ_nonempty (weight p)) :
      Algorithms.WeakInterpolationDesign.profile (schedule p) i * cap p i = p.μ * (3*p.n*p.L) * peak p := by
    rw [profile_eq hp, cap, ite_eq_left hi]
    field_simp [(signal_pos hp i).ne']
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    change Algorithms.WeakInterpolationDesign.profile (schedule p) i * cap p i ≤ _
    by_cases hi : weight p i = Finset.univ.sup' Finset.univ_nonempty (weight p)
    · exact (ht i hi).le
    rw [profile_eq hp, cap, ite_eq_right hi]
    have h := mul_le_mul hp.2.2.1 (signal_le_n hp i) (signal_pos hp i).le hL.le
    have h' := mul_le_mul h (Finset.le_sup' (signal p) (Finset.mem_univ i))
      (signal_pos hp i).le (mul_nonneg hL.le (by positivity))
    change _ ≤ _ * peak p at h'
    nlinarith only [mul_le_mul_of_nonneg_left h' hp.2.1.le,
      mul_nonneg (mul_nonneg (mul_nonneg hp.2.1.le hL.le)
        (show 0 ≤ (p.n : ℝ) by positivity)) (peak_pos hp).le]
  · obtain ⟨i,hi,he⟩ := Finset.univ.exists_mem_eq_sup' Finset.univ_nonempty (weight p)
    rw [← ht i he.symm]
    exact Finset.le_sup' (fun i => Algorithms.WeakInterpolationDesign.profile (schedule p) i * cap p i) hi

end LongTails.Proofs.DistributedGrowthSchedule
