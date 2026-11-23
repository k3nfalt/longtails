import LongTails.Proofs.AcceleratedFiniteSum
import LongTails.Proofs.GradientDiversitySchedule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GradientDiversityGeometry

open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.GradientDiversitySgd LongTails.Algorithms.StrongGrowthWeights
open GradientDiversitySchedule WeakInterpolationGeometry
open Set Metric
open scoped RealInnerProductSpace

variable {p : Params} {f : Functions p}

open DistributedGrowthGeometry (Geometry sum_grad)

variable (H : Geometry p f)
include H

lemma common_solutions : solutions p f = LongTails.Setups.DistributedWeakInterpolation.solutions
    (schedule p) f := Set.ext fun _ => DistributedGrowthGeometry.local_min H

lemma bregman_sum (x y : Point p) :
    ∑ i, (f i y - f i x - ⟪gradient (f i) x, y-x⟫) ≤
      (p.n : ℝ) * (p.L / 2 * ‖y-x‖^2) := by
  have hg t := (DistributedGrowthGeometry.avg_grad H t).gradient.symm ▸ (DistributedGrowthGeometry.avg_grad H t)
  have h := OracleTemplate.Gradient.smooth_upper_bound hg H.lip x y
  have hn' : 0 < (p.n : ℝ) := by exact_mod_cast p.n.pos
  change (∑ i, f i y) / (p.n : ℝ) ≤ (∑ i, f i x) / (p.n : ℝ) +
    ⟪gradient (objective p f) x, y-x⟫ + _ at h
  field_simp [hn'.ne',hn'] at h
  simp only [Finset.sum_sub_distrib, ← sum_inner, sum_grad H, real_inner_smul_left]
  linear_combination h / 2

lemma upper (x y : Point p) :
    surrogate (schedule p) f y ≤ surrogate (schedule p) f x +
      ⟪direction (schedule p) f x, y-x⟫ + W.smoothness (schedule p) / 2 * ‖y-x‖^2 := by
  let D := fun i => f i y - f i x - ⟪gradient (f i) x, y-x⟫
  have hn i : 0 ≤ D i := sub_nonneg.mpr
    (OracleTemplate.Gradient.convex_support (H.convex i) (H.grad i) x y)
  have hd := bregman_sum H x y
  change ∑ i, D i ≤ _ at hd
  have hw := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (le_peak p i) (hn i)
  rw [← Finset.mul_sum] at hw
  have hs := mul_le_mul_of_nonneg_left hd (gain_pos H.valid (peak p)).le
  have hL := H.valid.2.1.trans_le H.valid.2.2.1
  have hb : (p.n : ℝ) * gain p (peak p) * p.L ≤ W.smoothness (schedule p) := by
    have h := mul_le_mul_of_nonneg_left
      (le_max_right (largest p * spread p) (p.n * gain p (peak p) / speed p)) hL.le
    change _ ≤ scale p at h
    have ht := speed_sum_pos H.valid
    rw [← mul_div_assoc, div_le_iff₀ ht] at h
    rw [smooth_eq H.valid]
    nlinarith only [h, mul_nonneg hL.le
      (mul_nonneg (show 0 ≤ (p.n : ℝ) by positivity) (gain_pos H.valid (peak p)).le)]
  have wsum (i : Fin p.n) : gain p i * D i = gain p i * f i y - gain p i * f i x -
      gain p i * ⟪gradient (f i) x, y-x⟫ := by unfold D; ring
  simp only [wsum,Finset.sum_sub_distrib] at hw
  unfold surrogate direction
  simp only [sum_inner, real_inner_smul_left, weights_eq H.valid]
  change (∑ i : Fin p.n, gain p i * f i y) ≤ (∑ i : Fin p.n, gain p i * f i x) +
    (∑ i : Fin p.n, gain p i * ⟪gradient (f i) x, y-x⟫) + W.smoothness (schedule p) / 2 * ‖y-x‖^2
  linear_combination hw + hs + (‖y-x‖^2 / 2) * hb

lemma growth {z : Point p} (hz : z ∈ solutions p f) (x : Point p)
    (hq : p.μ / 2 * infDist x (solutions p f)^2 ≤ objective p f x - objective p f z) :
    W.information (schedule p) *
      (infDist x (LongTails.Setups.DistributedWeakInterpolation.solutions (schedule p) f)^2 / 2) ≤
      surrogate (schedule p) f x-surrogate (schedule p) f z := by
  have he (y : Point p) : surrogate (schedule p) f y = p.μ * DistributedGrowthGeometry.surrogate p f y := by
    unfold surrogate DistributedGrowthGeometry.surrogate
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [weights_eq H.valid]
    unfold gain curvature weight
    ring
  rw [← common_solutions H, information_eq H.valid, he, he]
  have h := mul_le_mul_of_nonneg_left hq (StrongGrowthWeights.information_pos H.valid).le
  have hg := DistributedGrowthGeometry.weighted_gap H hz x
  nlinarith only [mul_le_mul_of_nonneg_left (h.trans hg) H.valid.2.1.le]

lemma local_upper (i : Fin p.n) (x y : Point p) :
    f i y ≤ f i x + ⟪gradient (f i) x, y-x⟫ + (p.n * p.L)/2 * ‖y-x‖^2 := by
  have hb := Finset.single_le_sum (fun j _ => sub_nonneg.mpr
    (OracleTemplate.Gradient.convex_support (H.convex j) (H.grad j) x y)) (Finset.mem_univ i)
  linarith only [hb, bregman_sum H x y]

lemma local_norm {z : Point p} (hz : z ∈ solutions p f) (i : Fin p.n) (x : Point p) :
    ‖gradient (f i) x‖ ≤ (p.L * spread p) * ‖x-z‖ := by
  have hh : z ∈ LongTails.Setups.DistributedWeakInterpolation.solutions (schedule p) f := common_solutions H ▸ hz
  have hi : gradient (f i) z = 0 := by simp [gradient, ((hh i).isLocalMin Filter.univ_mem).fderiv_eq_zero]
  have hz' : gradient (objective p f) z = 0 := by
    simp [gradient, ((show IsMinOn _ univ z from hz).isLocalMin Filter.univ_mem).fderiv_eq_zero]
  have hL := H.valid.2.1.trans_le H.valid.2.2.1
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n.pos
  have hg := GradientDiversitySchedule.gradient_sq_of_upper (mul_pos hn hL) (local_upper H i)
    (fun y => hh i (mem_univ y)) x
  have hu := local_upper H i z x
  rw [hi, inner_zero_left, add_zero] at hu
  have h₁ : ‖gradient (f i) x‖ ≤ (p.n * p.L) * ‖x-z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hg, mul_le_mul_of_nonneg_left hu (mul_pos hn hL).le]
  have h₂ := GradientDiversitySchedule.individual_bound H.valid _ _ (sum_grad H x) (H.growth x) i
  have hg' := H.lip x z
  rw [hz', sub_zero] at hg'
  have h₃ := h₂.trans (mul_le_mul_of_nonneg_left hg' (by positivity))
  unfold spread
  rcases le_total (p.n : ℝ) (1+Real.sqrt (p.n*(p.ρ-1))) with h | h
  · rw [min_eq_left h, mul_comm p.L]
    exact h₁
  · rw [min_eq_right h]
    linarith only [h₃]

end LongTails.Proofs.GradientDiversityGeometry
