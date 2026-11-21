import LongTails.Algorithms.GradientDiversitySgd
import LongTails.Proofs.StrongGrowthAlignment
import LongTails.Proofs.WeightedInterpolationPrecision

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GradientDiversitySchedule

open LongTails.Setups.DistributedGradientDiversity
open LongTails.Algorithms.GradientDiversityDesign LongTails.Algorithms.GradientDiversitySgd
open GradientDiversityProfile

namespace W
export LongTails.Algorithms.WeakInterpolationDesign (profile weights information largestCurvature
  smoothness noiseRadius threshold)
end W

variable {p : Params}

lemma curv_pos (hp : spec.valid p) (i : Fin p.n) : 0 < curvature p i :=
  mul_pos (half_pos hp.2.1) (amplitude_pos hp i)

lemma gain_pos (hp : spec.valid p) (i : Fin p.n) : 0 < gain p i :=
  div_pos (curv_pos hp i) (speed_pos hp i)

lemma le_peak (p : Params) (i : Fin p.n) : gain p i ≤ gain p (peak p) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (gain p) Finset.univ_nonempty)).2 i
    (Finset.mem_univ i)

lemma le_largest (p : Params) (i : Fin p.n) : curvature p i ≤ largest p :=
  Finset.le_sup' (curvature p) (Finset.mem_univ i)

lemma speed_sum_pos (hp : spec.valid p) : 0 < speed p :=
  Finset.sum_pos (fun i _ => inv_pos.mpr (speed_pos hp i)) Finset.univ_nonempty

lemma amp_spread (hp : spec.valid p) (i : Fin p.n) : amplitude p i ≤ spread p := by
  have h := StrongGrowthAlignment.individual_bound hp (amplitude p) (1 : ℝ)
    (by simpa [amplitude] using profile_sum hp (parameter_spec hp).1)
    (by simpa [Real.norm_eq_abs, sq_abs, moment, amplitude] using (parameter_spec hp).2.1) i
  apply le_min
  · exact (Finset.single_le_sum (fun j _ => (amplitude_pos hp j).le) (Finset.mem_univ i)).trans_eq
      (profile_sum hp (parameter_spec hp).1)
  · simpa [Real.norm_eq_abs, abs_of_pos (amplitude_pos hp i)] using h

lemma scale_signal (hp : spec.valid p) (i : Fin p.n) :
    curvature p i * (p.L * spread p) ≤ scale p := by
  have hsp : 0 ≤ spread p := by unfold spread; positivity
  have hL := hp.2.1.trans_le hp.2.2.1
  have := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (le_largest p i) hsp).trans
    (le_max_left _ (p.n * gain p (peak p) / speed p))) hL.le
  simpa only [scale, mul_left_comm, mul_assoc] using this

lemma cap_enough (hp : spec.valid p) (i : Fin p.n) : curvature p i ^ 2 ≤ scale p := by
  have h := hp.2.1
  have hL := hp.2.2.1
  have h₁ : curvature p i ≤ p.L * spread p :=
    mul_le_mul (by linarith : p.μ / 2 ≤ p.L) (amp_spread hp i) (amplitude_pos hp i).le
      (hp.2.1.trans_le hL).le
  exact (show curvature p i ^ 2 ≤ curvature p i * (p.L * spread p) by
    simpa only [sq] using mul_le_mul_of_nonneg_left h₁ (curv_pos hp i).le).trans (scale_signal hp i)

lemma capacity_ge (hp : spec.valid p) (i : Fin p.n) : curvature p i ≤ capacity p i := by
  unfold capacity
  split_ifs
  · exact (le_div_iff₀ (curv_pos hp i)).mpr (by simpa [sq] using cap_enough hp i)
  · exact le_rfl

lemma curv_sum (hp : spec.valid p) : ∑ i, curvature p i = (p.n : ℝ) * (p.μ / 2) := by
  simp only [curvature, ← Finset.mul_sum, amplitude, profile_sum hp (parameter_spec hp).1, mul_comm]

lemma schedule_valid (hp : spec.valid p) : LongTails.Setups.DistributedWeakInterpolation.spec.valid
    (schedule p) :=
  ⟨hp.1, fun i => (curv_pos hp i).le.trans (capacity_ge hp i), half_pos hp.2.1,
   (curv_sum hp).symm.le.trans (Finset.sum_le_sum (fun i _ => capacity_ge hp i)),
   hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩

lemma tuned (hp : spec.valid p) (i : Fin p.n) : W.profile (schedule p) i = curvature p i := by
  let u := curvature p
  let f := fun t i => min (capacity p i) (t * (p.h i : ℝ))
  let a := W.threshold (schedule p)
  let b := gain p (peak p)
  have hb (j : Fin p.n) : f b j = u j := by
    have hw := (div_le_iff₀ (speed_pos hp j)).mp (le_peak p j)
    by_cases hj : j = peak p
    · subst j
      have e : b * (p.h (peak p) : ℝ) = curvature p (peak p) := by
        dsimp [b, gain]; field_simp [(speed_pos hp _).ne']
      exact show min _ _ = _ by rw [e, min_eq_right (capacity_ge hp _)]
    · simpa [f, capacity, hj, u] using min_eq_left hw
  have he : ∑ j, f a j = ∑ j, f b j := by
    simp_rw [hb]
    exact (WeakInterpolationDesign.threshold_spec (schedule_valid hp)).2.trans (curv_sum hp).symm
  have hm {s t : ℝ} (h : s ≤ t) (j : Fin p.n) : f s j ≤ f t j :=
    min_le_min_left _ (mul_le_mul_of_nonneg_right h (p.h j).coe_nonneg)
  change f a i = u i
  rw [← hb i]
  rcases le_total a b with h | h
  · exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hm h j)).mp he) i (Finset.mem_univ _)
  · exact (((Finset.sum_eq_sum_iff_of_le (fun j _ => hm h j)).mp he.symm) i (Finset.mem_univ _)).symm

lemma weights_eq (hp : spec.valid p) (i : Fin p.n) : W.weights (schedule p) i = gain p i := by
  change W.profile (schedule p) i / _ = _
  rw [tuned hp]; rfl

lemma information_eq (hp : spec.valid p) :
    W.information (schedule p) = (p.μ / 2)^2 * information p := by
  unfold LongTails.Algorithms.WeakInterpolationDesign.information LongTails.Algorithms.GradientDiversityDesign.information
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weights_eq hp, tuned hp]
  unfold gain curvature weight
  ring

lemma largest_eq (hp : spec.valid p) : W.largestCurvature (schedule p) = scale p := by
  unfold LongTails.Algorithms.WeakInterpolationDesign.largestCurvature
  change Finset.univ.sup' Finset.univ_nonempty (fun i : Fin p.n => W.profile (schedule p) i * capacity p i) = _
  simp_rw [tuned hp]
  have he : curvature p (peak p) * capacity p (peak p) = scale p := by
    simp [capacity]
    field_simp [(curv_pos hp _).ne']
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    by_cases h : i = peak p
    · simpa [h] using he.le
    · simpa [capacity, h, sq] using cap_enough hp i
  · rw [← he]
    exact Finset.le_sup' (fun i => curvature p i * capacity p i) (Finset.mem_univ _)

lemma smooth_eq (hp : spec.valid p) : W.smoothness (schedule p) = 2 * speed p * scale p := by
  unfold LongTails.Algorithms.WeakInterpolationDesign.smoothness
  rw [largest_eq hp]; rfl

end LongTails.Proofs.GradientDiversitySchedule
