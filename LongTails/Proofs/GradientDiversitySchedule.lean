import LongTails.Algorithms.GradientDiversitySgd
import LongTails.Proofs.DistributedGrowthGeometry
import LongTails.Proofs.WeightedInterpolationPrecision

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GradientDiversitySchedule

open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.StrongGrowthWeights LongTails.Algorithms.GradientDiversitySgd
open scoped RealInnerProductSpace

namespace W
export LongTails.Algorithms.WeakInterpolationDesign (profile weights information largestCurvature
  smoothness noiseRadius threshold)
end W

variable {p : Params}

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma individual_bound {p : Params} (hp : spec.valid p) (v : Fin p.n → E) (g : E)
    (hmean : ∑ i, v i = (p.n : ℝ) • g)
    (hg : ∑ i, ‖v i‖ ^ 2 ≤ (p.n : ℝ) * p.ρ * ‖g‖ ^ 2) (i : Fin p.n) :
    ‖v i‖ ≤ (1 + Real.sqrt (p.n * (p.ρ - 1))) * ‖g‖ := by
  have hs : ∑ j, ‖v j - g‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 - p.n * ‖g‖ ^ 2 := by
    simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← sum_inner, hmean, real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hb := Finset.single_le_sum (fun j _ => sq_nonneg ‖v j - g‖) (Finset.mem_univ i)
  rw [hs] at hb
  have hρ := sub_nonneg.mpr hp.2.2.2.1
  have hsq := Real.sq_sqrt (mul_nonneg (show 0 ≤ (p.n : ℝ) by positivity) hρ)
  have h : ‖v i - g‖ ≤ Real.sqrt (p.n * (p.ρ - 1)) * ‖g‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, hsq]
    nlinarith only [hb, hg]
  linarith only [h, norm_le_norm_sub_add (v i) g]

lemma gradient_sq_of_upper {F : E → ℝ} {v : E → E} {B : ℝ} (hB : 0 < B)
    (hu : ∀ x y, F y ≤ F x + ⟪v x, y-x⟫ + B/2 * ‖y-x‖^2)
    {z : E} (hz : ∀ y, F z ≤ F y) (x : E) :
    ‖v x‖^2 ≤ 2*B*(F x - F z) := by
  let y := x - B⁻¹ • v x
  have he : y - x = -B⁻¹ • v x := by dsimp [y]; module
  have h := (hz y).trans (hu x y)
  rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_pos (inv_pos.mpr hB)] at h
  field_simp [hB.ne',hB] at h
  linarith

end

lemma curv_pos (hp : spec.valid p) (i : Fin p.n) : 0 < curvature p i :=
  mul_pos hp.2.1 (StrongGrowthWeights.signal_pos hp i)

lemma gain_pos (hp : spec.valid p) (i : Fin p.n) : 0 < gain p i :=
  div_pos (curv_pos hp i) (StrongGrowthWeights.speed hp i)

lemma le_peak (p : Params) (i : Fin p.n) : gain p i ≤ gain p (peak p) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (gain p) Finset.univ_nonempty)).2 i
    (Finset.mem_univ i)

lemma le_largest (p : Params) (i : Fin p.n) : curvature p i ≤ largest p :=
  Finset.le_sup' (curvature p) (Finset.mem_univ i)

lemma speed_sum_pos (hp : spec.valid p) : 0 < speed p :=
  Finset.sum_pos (fun i _ => inv_pos.mpr (StrongGrowthWeights.speed hp i)) Finset.univ_nonempty

lemma amp_spread (hp : spec.valid p) (i : Fin p.n) : signal p i ≤ spread p := by
  have h := individual_bound hp (signal p) (1 : ℝ)
    (by simpa using StrongGrowthWeights.signal_sum hp)
    (by simpa [Real.norm_eq_abs, sq_abs] using (StrongGrowthWeights.mixing_spec hp).2.1) i
  apply le_min
  · exact (Finset.single_le_sum (fun j _ => (StrongGrowthWeights.signal_pos hp j).le) (Finset.mem_univ i)).trans_eq
      (StrongGrowthWeights.signal_sum hp)
  · simpa [Real.norm_eq_abs, abs_of_pos (StrongGrowthWeights.signal_pos hp i)] using h

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
    mul_le_mul (by linarith : p.μ ≤ p.L) (amp_spread hp i) (StrongGrowthWeights.signal_pos hp i).le
      (hp.2.1.trans_le hL).le
  exact (show curvature p i ^ 2 ≤ curvature p i * (p.L * spread p) by
    simpa only [sq] using mul_le_mul_of_nonneg_left h₁ (curv_pos hp i).le).trans (scale_signal hp i)

lemma capacity_ge (hp : spec.valid p) (i : Fin p.n) : curvature p i ≤ capacity p i := by
  unfold capacity
  split_ifs
  · exact (le_div_iff₀ (curv_pos hp i)).mpr (by simpa [sq] using cap_enough hp i)
  · exact le_rfl

lemma curv_sum (hp : spec.valid p) : ∑ i, curvature p i = (p.n : ℝ) * p.μ := by
  simp only [curvature, ← Finset.mul_sum, StrongGrowthWeights.signal_sum hp, mul_comm]

lemma schedule_valid (hp : spec.valid p) : LongTails.Setups.DistributedWeakInterpolation.spec.valid
    (schedule p) :=
  ⟨hp.1, fun i => (curv_pos hp i).le.trans (capacity_ge hp i), hp.2.1,
   (curv_sum hp).symm.le.trans (Finset.sum_le_sum (fun i _ => capacity_ge hp i)),
   hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩

lemma tuned (hp : spec.valid p) (i : Fin p.n) : W.profile (schedule p) i = curvature p i := by
  let u := curvature p
  let f := fun t i => min (capacity p i) (t * (p.h i : ℝ))
  let a := W.threshold (schedule p)
  let b := gain p (peak p)
  have hb (j : Fin p.n) : f b j = u j := by
    have hw := (div_le_iff₀ (StrongGrowthWeights.speed hp j)).mp (le_peak p j)
    by_cases hj : j = peak p
    · subst j
      have e : b * (p.h (peak p) : ℝ) = curvature p (peak p) := by
        dsimp [b, gain]; field_simp [(StrongGrowthWeights.speed hp _).ne']
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
    W.information (schedule p) = p.μ^2 * information p := by
  unfold LongTails.Algorithms.WeakInterpolationDesign.information LongTails.Algorithms.StrongGrowthWeights.information
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
