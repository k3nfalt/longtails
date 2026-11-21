import LongTails.Proofs.DistributedGrowthSchedule
import LongTails.Proofs.DistributedGrowthGeometry
import LongTails.Proofs.WeightedInterpolationConvergence
import LongTails.Proofs.WeightedInterpolationRuntime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedGrowthConvergence

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.StrongGrowthWeights LongTails.Algorithms.DistributedGrowthSgd
open StrongGrowthWeights DistributedGrowthSchedule DistributedGrowthGeometry
open Algorithms.WeightedInterpolationSgd
open scoped RealInnerProductSpace

variable {p : Params} {f : Functions p}

lemma solution_eq (D : Geometry p f) :
    Setups.DistributedWeakInterpolation.solutions (schedule p) f = solutions p f :=
  Set.ext fun _ => (local_min D).symm

lemma surrogate_eq (hp : spec.valid p) (x : Point p) :
    WeakInterpolationGeometry.surrogate (schedule p) f x = p.μ * surrogate p f x := by
  unfold WeakInterpolationGeometry.surrogate surrogate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weight_eq hp]
  ring

lemma direction_eq (hp : spec.valid p) (x : Point p) :
    WeakInterpolationGeometry.direction (schedule p) f x = p.μ • direction p f x := by
  unfold WeakInterpolationGeometry.direction direction
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weight_eq hp,smul_smul]

lemma smooth_majorant (hp : spec.valid p) :
    p.μ * ((∑ i, weight p i) * (3*p.n*p.L)) ≤
      Algorithms.WeakInterpolationDesign.smoothness (schedule p) := by
  let S := ∑ i, (p.h i : ℝ)⁻¹
  have hw : ∑ i, weight p i ≤ S * peak p := by
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [weight,div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (signal p) (Finset.mem_univ i))
      (inv_nonneg.mpr (p.h i).coe_nonneg)
  unfold Algorithms.WeakInterpolationDesign.smoothness
  rw [largest_eq hp]
  change _ ≤ 2 * S * _
  have hL := hp.2.1.trans_le hp.2.2.1
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (p.h i).coe_nonneg)
  have hB : 0 ≤ 3*(p.n:ℝ)*p.L := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hB) hp.2.1.le,
    mul_nonneg (mul_nonneg (mul_nonneg hp.2.1.le hB) (peak_pos hp).le) hS]

lemma direction_bound (D : Geometry p f) {y : Point p} (hy : y ∈ solutions p f) (x : Point p) :
    ‖WeakInterpolationGeometry.direction (schedule p) f x‖^2 ≤
      2*Algorithms.WeakInterpolationDesign.smoothness (schedule p)*
        (WeakInterpolationGeometry.surrogate (schedule p) f x -
          WeakInterpolationGeometry.surrogate (schedule p) f y) := by
  let C := (∑ i, weight p i)*(3*p.n*p.L)
  have hL := D.valid.2.1.trans_le D.valid.2.2.1
  have hw : 0 < ∑ i, weight p i := Finset.sum_pos (fun i _ =>
    div_pos (signal_pos D.valid i) (speed D.valid i)) Finset.univ_nonempty
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := OracleTemplate.Gradient.descent hC (weighted_grad D) (weighted_lip D) x
  have hmin (t : Point p) : surrogate p f y ≤ surrogate p f t :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      ((local_min D).mp hy i (Set.mem_univ t)) (div_pos (signal_pos D.valid i) (speed D.valid i)).le
  have hh : ‖direction p f x‖^2/(2*C) ≤ surrogate p f x-surrogate p f y := by
    linarith only [hs, hmin (x-(1/C) • direction p f x)]
  have hmul := (div_le_iff₀ (by positivity : 0 < 2*C)).mp hh
  rw [direction_eq D.valid, norm_smul, Real.norm_eq_abs, abs_of_pos D.valid.2.1,
    surrogate_eq D.valid,surrogate_eq D.valid]
  have hmajor : p.μ*C ≤ _ := smooth_majorant D.valid
  have hgap := sub_nonneg.mpr (hmin x)
  nlinarith only [mul_le_mul_of_nonneg_left hmul (sq_nonneg p.μ),
    mul_le_mul_of_nonneg_right hmajor (mul_nonneg D.valid.2.1.le hgap)]

lemma local_bound (D : Geometry p f) {z : Point p} (hz : z ∈ solutions p f)
    (hR : ‖p.x0-z‖ ≤ p.R) (k : ℕ) (i : Fin p.n) (x : Point p) :
    ‖WeightedInterpolationBatch.localMean (schedule p) k f x i‖ ≤ ‖x-p.x0‖ + p.R := by
  let q := schedule p
  let B : ℝ := 3*p.n*p.L
  have hL := D.valid.2.1.trans_le D.valid.2.2.1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let a := stepSize q k * Algorithms.WeakInterpolationDesign.weights q i / fraction q i
  have hv := valid D.valid
  obtain ⟨ha,_,_⟩ := WeightedInterpolationPrecision.alpha_bounds hv k i
  obtain ⟨hη,hηC⟩ := WeightedInterpolationAllocation.step_bounds hv k
  have hm : Algorithms.WeakInterpolationDesign.profile q i * B ≤
      Algorithms.WeakInterpolationDesign.largestCurvature q := by
    rw [profile_eq D.valid,largest_eq D.valid]
    dsimp only [B]
    have h := mul_le_mul_of_nonneg_left (Finset.le_sup' (signal p) (Finset.mem_univ i))
      (mul_nonneg D.valid.2.1.le hB)
    change _ ≤ _ * peak p at h
    dsimp only [B] at h
    linarith only [h]
  have hα := WeightedInterpolationPrecision.alpha_profile hv i
  have hS := WeakInterpolationDesign.speed_pos hv
  have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hα hB) hη
  have h2 := mul_le_mul_of_nonneg_left hm (mul_nonneg hη (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hS.le))
  have hab : a*B ≤ 1 := by
    unfold Algorithms.WeakInterpolationDesign.smoothness at hηC
    dsimp [a]
    rw [mul_div_assoc]
    linarith only [h1,h2,hηC]
  have hg := component_lip D i x z
  have hzero : gradient (f i) z = 0 := by
    simp [gradient, (((local_min D).mp hz i).isLocalMin Filter.univ_mem).fderiv_eq_zero]
  rw [hzero,sub_zero] at hg
  change ‖a • gradient (f i) x‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
  change _ ≤ B * _ at hg
  linarith only [mul_le_mul_of_nonneg_left hg ha, mul_le_mul_of_nonneg_right hab (norm_nonneg (x-z)),
    norm_sub_le_norm_sub_add_norm_sub x p.x0 z,hR]

lemma bounds (D : Geometry p f) {z : Point p} (hz : z ∈ solutions p f)
    (hR : ‖p.x0-z‖ ≤ p.R) (hQ : ∀ x, p.μ/2 * Metric.infDist x (solutions p f)^2 ≤
      objective p f x - objective p f z)
    (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hi : ∀ i, Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
      (ν i : Measure _) (P : Measure _) ∧ Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (ν i) (f i) (g i) p.σ) :
    WeightedInterpolationStep.Bounds (schedule p) f g z (P : Measure (Samples p)) ν where
  valid := valid D.valid
  convex := D.convex
  differentiable := D.grad
  solution := (local_min D).mp hz
  initial := hR
  localMeanBound := fun k i x => local_bound D hz hR k i x
  directionBound := fun y hy x => direction_bound D ((local_min D).mpr hy) x
  growth x := by
    rw [solution_eq D,info_eq D.valid,surrogate_eq D.valid,surrogate_eq D.valid]
    have hh := mul_le_mul_of_nonneg_left (hQ x) (information_pos D.valid).le
    have hg := weighted_gap D hz x
    linarith only [mul_le_mul_of_nonneg_left (hh.trans hg) D.valid.2.1.le]
  workers := hw
  samples := fun i => (hi i).1
  stochastic := fun i => (hi i).2

end LongTails.Proofs.DistributedGrowthConvergence
