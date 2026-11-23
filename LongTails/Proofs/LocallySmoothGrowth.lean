import LongTails.Algorithms.LocallySmoothGrowthSgd
import LongTails.Proofs.GradientDiversityConvergence
import LongTails.Proofs.DashaDistributedSimplification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.LocallySmoothGrowth

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedLocallySmoothGrowth
open LongTails.Algorithms.LocallySmoothGrowthSgd
open LongTails.Algorithms.GradientDiversitySgd (curvature gain speed)
open GradientDiversitySchedule
open LongTails.Algorithms.WeightedInterpolationSgd (stepSize fraction)

variable {p : Params}

lemma scale_bounds (hp : spec.valid p) (i : Fin p.n) :
    curvature (aggregate p) i ^ 2 ≤ scale p ∧ curvature (aggregate p) i * p.L i ≤ scale p := by
  let a := curvature (aggregate p)
  have h : a i * max (a i) (p.L i) ≤ scale p :=
    Finset.le_sup' (fun j => a j * max (a j) (p.L j)) (Finset.mem_univ i)
  have ha : 0 ≤ a i := (curv_pos hp.1 i).le
  change a i ^ 2 ≤ scale p ∧ a i * p.L i ≤ scale p
  exact ⟨by simpa only [sq] using (mul_le_mul_of_nonneg_left (le_max_left _ _) ha).trans h,
    (mul_le_mul_of_nonneg_left (le_max_right _ _) ha).trans h⟩

lemma bounds (hp : spec.valid p) {f : Functions p}
    (G : DistributedGrowthGeometry.Geometry (aggregate p) f)
    (hL : ∀ i x y, ‖gradient (f i) x-gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    {z : Point p}
    (hz : z ∈ Setups.DistributedMeanStrongGrowth.solutions (aggregate p) f) (hR : ‖p.x0-z‖ ≤ p.R)
    (hq : ∀ x, p.μ / 2 * Metric.infDist x (Setups.DistributedMeanStrongGrowth.solutions (aggregate p) f)^2 ≤
      Setups.DistributedMeanStrongGrowth.objective (aggregate p) f x -
      Setups.DistributedMeanStrongGrowth.objective (aggregate p) f z)
    {g : Algorithms.WeightedInterpolationSgd.LocalOracle (schedule p)} {P : ProbabilityMeasure (Samples p)}
    {ν : Fin p.n → ProbabilityMeasure p.Ω}
    (hw : ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hi : ∀ i, Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
      (ν i : Measure p.Ω) (P : Measure (Samples p)) ∧
      Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i : Measure p.Ω) (f i) (g i) p.σ) :
    WeightedInterpolationStep.Bounds (schedule p) f g z (P : Measure (Samples p)) ν := by
  let r := aggregate p
  let q := schedule p
  have hM i := (scale_bounds hp i).1
  have hcap i := (scale_bounds hp i).2
  have hv := schedule_valid_at hp.1 hM
  have hS := (speed_sum_pos hp.1).le
  have hpos := (sq_nonneg _).trans (hM 0)
  have hsol : z ∈ Setups.DistributedWeakInterpolation.solutions q f := (DistributedGrowthGeometry.local_min G).mp hz
  have hs : ∑ i, W.weights q i * p.L i ≤ W.smoothness q := calc
    _ ≤ ∑ i, (p.h i : ℝ)⁻¹ * scale p := by
      apply Finset.sum_le_sum
      intro i _
      rw [weights_eq_at hp.1 hM, gain, div_mul_eq_mul_div, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hcap i) (inv_nonneg.mpr (p.h i).coe_nonneg)
    _ = speed r * scale p := by rw [← Finset.sum_mul]; rfl
    _ ≤ 2 * speed r * scale p := by nlinarith only [mul_nonneg hS hpos]
    _ = _ := (smooth_eq_at hp.1 hM).symm
  refine ⟨hv, G.convex, G.grad, hsol, hR, ?_, ?_, fun x =>
    GradientDiversityGeometry.growth_at G hM hz x (hq x), hw, fun i => (hi i).1, fun i => (hi i).2⟩
  · intro k i x
    change Point p at x
    change Fin p.n at i
    let α := stepSize q k * W.weights q i / fraction q i
    have ha := (WeightedInterpolationPrecision.alpha_bounds hv k i).1
    have ht := WeightedInterpolationAllocation.step_bounds hv k
    have hw' := WeightedInterpolationPrecision.alpha_profile hv i
    rw [tuned_at hp.1 hM] at hw'
    change W.weights q i / fraction q i ≤ 2 * speed r * curvature r i at hw'
    have h : α * p.L i ≤ 1 := calc
      _ = stepSize q k * ((W.weights q i / fraction q i) * p.L i) := by dsimp [α]; ring
      _ ≤ stepSize q k * (2 * speed r * (curvature r i * p.L i)) := by
        rw [← mul_assoc (2 * speed r)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw' (hp.2 i)) ht.1
      _ ≤ stepSize q k * (2 * speed r * scale p) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcap i) (by positivity)) ht.1
      _ ≤ 1 := by rw [← smooth_eq_at hp.1 hM]; linarith only [ht.2]
    have hzero : gradient (f i) z = 0 := by
      simp [gradient, ((hsol i).isLocalMin Filter.univ_mem).fderiv_eq_zero]
    have hg := hL i x z
    rw [hzero, sub_zero] at hg
    change ‖α • gradient (f i) x‖ ≤ ‖x-p.x0‖ + p.R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    have hd := norm_sub_le_norm_sub_add_norm_sub x p.x0 z
    nlinarith only [mul_le_mul_of_nonneg_left hg ha, mul_le_mul_of_nonneg_right h (norm_nonneg (x-z)), hd, hR]
  · intro y hy x
    apply GradientDiversitySchedule.gradient_sq_of_upper (WeakInterpolationDesign.smoothness_pos hv) _
      (WeakInterpolationGeometry.surrogate_min (WeakInterpolationDesign.weight_nonneg hv) hy) x
    intro x y
    linarith only [WeakInterpolationGeometry.surrogate_upper_of_caps (WeakInterpolationDesign.weight_nonneg hv) G.grad hL hs x y]

lemma runtime (hp : spec.valid p) (T : Time)
    (hT : let r := aggregate p
          let I := ∑ i, curvature r i ^ 2 / (p.h i : ℝ)
          let A := 2 * speed r * scale p / I
          let w := 1 + 2 * Real.log (4 + p.d + A +
            (p.R^2 + (p.σ * Algorithms.GradientDiversitySgd.largest r / scale p)^2)/p.ε)
          2048 * (p.σ^2/(I*p.ε) + A * (1 + Real.log (1+p.R^2/p.ε)) *
            (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b*(64 + 1024*(p.d : ℝ)*w))) ≤ (T : ℝ)) :
    Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (schedule p))
      (Algorithms.WeightedInterpolationSgd.config (schedule p) T) = T := by
  let r := aggregate p
  have hM i := (scale_bounds hp i).1
  apply GradientDiversityConvergence.runtime_at hp.1 hM
  let I := ∑ i, curvature r i ^ 2 / (p.h i : ℝ)
  let A := 2 * speed r * scale p / I
  let E := (p.R^2 + (p.σ * Algorithms.GradientDiversitySgd.largest r / scale p)^2)/p.ε
  have hε : 0 < p.ε := hp.1.2.2.2.2.2.2
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (p.h i).coe_nonneg)
  have hscale := (sq_nonneg _).trans (hM 0)
  have hS := (speed_sum_pos hp.1).le
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (by positivity) hscale) hI
  have hE : 0 ≤ E := div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hε.le
  have hb := Real.log_nonneg (show 1 ≤ 1 + p.R^2 / p.ε from le_add_of_nonneg_right (by positivity))
  have hw := DashaDistributedSimplification.size_ceil_le_log (2 + (p.d : ℝ) + A + E) (by positivity)
  rw [show 2 + (2 + (p.d : ℝ) + A + E) = 4 + p.d + A + E by ring] at hw
  refine le_trans ?_ hT
  change 2048 * (p.σ^2/(I*p.ε) + A * (1+Real.log (1+p.R^2/p.ε)) * (_+_+_*(_+_*_*_))) ≤ _
  gcongr

end LongTails.Proofs.LocallySmoothGrowth
