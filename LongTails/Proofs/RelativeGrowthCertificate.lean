import LongTails.Proofs.RelativeGrowthGeometry
import LongTails.Proofs.RelativeGrowthTuning
import LongTails.Proofs.WeightedInterpolationConvergence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RelativeGrowthCertificate

open Set MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.DistributedRelativeGrowth
open LongTails.Setups.DistributedWeakInterpolation (solutions objective)
open LongTails.Algorithms.RelativeGrowthBatches
open LongTails.Algorithms.WeakInterpolationDesign (information weights smoothness)
open LongTails.Algorithms.WeightedInterpolationSgd (stepSize fraction)
open RelativeGrowthTuning WeakInterpolationGeometry

variable {p : Params} {f : Functions p}

lemma smooth_bound (hp : spec.valid p) :
    ∑ i, weights (tuning p) i * p.L i ≤ smoothness (tuning p) := by
  let S := ∑ i, (p.h i : ℝ)⁻¹
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (p.h i).coe_nonneg
  have hM : 0 ≤ scale p := (sq_nonneg _).trans (scale_bound hp 0).1
  calc
    _ ≤ ∑ i, (p.h i : ℝ)⁻¹ * scale p := by
      apply Finset.sum_le_sum
      intro i _
      rw [weight_eq hp, gain, div_mul_eq_mul_div, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (scale_bound hp i).2 (inv_nonneg.mpr (p.h i).coe_nonneg)
    _ = S * scale p := by rw [← Finset.sum_mul]
    _ ≤ 2*S*scale p := by nlinarith [mul_nonneg hS hM]
    _ = _ := by unfold smoothness; rw [scale_eq hp]; rfl

lemma weighted_gap (hp : spec.valid p) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x-gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (hr : ∀ x, ∑ i, ‖gradient (f i) x‖^2 ≤ (p.n : ℝ)*p.ρ*‖gradient (objective p.toParams f) x‖^2)
    {z : Point p} (hz : z ∈ solutions p.toParams f)
    (hq : ∀ x, p.μ / 2 * Metric.infDist x (solutions p.toParams f)^2 ≤ objective p.toParams f x-objective p.toParams f z)
    (x : Point p) : information (tuning p) * (Metric.infDist x (solutions (tuning p) f)^2 / 2) ≤
      ∑ i, weights (tuning p) i * (f i x-f i z) := by
  let q := tuning p
  let h := fun i : Fin p.n => (p.h i : ℝ)
  let u := Algorithms.GrowthProfile.profile h p.ρ
  let I := ∑ i, u i / h i * u i
  let G := gradient (objective p.toParams f)
  have hh (i : Fin p.n) : 0 < h i := by exact_mod_cast hp.1 i
  have hw (i : Fin p.n) : weights q i = p.μ * (u i / h i) := by
    rw [weight_eq hp i]; unfold gain signal; ring
  have hi : information q = p.μ^2*I := by
    unfold Algorithms.WeakInterpolationDesign.information I
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw, profile_eq hp i]
    change _ * (p.μ*u i) = _
    ring
  have hμ := hp.2.2.1
  have hpos : 0 < p.μ*I := by
    have H := WeakInterpolationDesign.information_pos (valid hp)
    rw [hi, sq, mul_assoc] at H
    exact pos_of_mul_pos_right H hμ.le
  have halign (y : Point p) : (p.μ*I)*‖G y‖^2 ≤ ⟪direction q f y,G y⟫ := by
    have H := RelativeGrowthGeometry.alignment hh hp.2.2.2.1 hg hr y
    change I * ‖G y‖^2 ≤ _ at H
    have hd : direction q f y = p.μ • ∑ i, (u i / h i) • gradient (f i) y := by
      unfold direction
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hw, smul_smul]
    rw [hd, real_inner_smul_left, mul_assoc]
    exact mul_le_mul_of_nonneg_left H hμ.le
  let L := Finset.univ.sup' Finset.univ_nonempty p.L
  have hgl (a b : Point p) : ‖G a-G b‖ ≤ L*‖a-b‖ := by
    dsimp only [G]
    rw [RelativeGrowthGeometry.gradient_eq hg, RelativeGrowthGeometry.gradient_eq hg]
    exact OracleTemplate.FiniteSum.fullGradient_lipschitz
      (g := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2)
      (fun i a b => (hl i a b).trans (mul_le_mul_of_nonneg_right
        (Finset.le_sup' p.L (Finset.mem_univ i)) (norm_nonneg _))) a b
  have hobj : objective p.toParams f = Setups.FiniteSumSmoothAndConvex.objective f := by
    funext y; simp [objective, Setups.FiniteSumSmoothAndConvex.objective, div_eq_inv_mul]
  have hgc : ConvexOn ℝ univ (objective p.toParams f) := hobj ▸ OracleTemplate.FiniteSum.objective_convex hc
  have hgg (y : Point p) : HasGradientAt (objective p.toParams f) (G y) y := by
    dsimp only [G]; rw [RelativeGrowthGeometry.gradient_eq hg y, hobj]
    exact OracleTemplate.FiniteSum.objective_gradient (oracle := fun ix : Fin p.n × Point p =>
      gradient (f ix.1) ix.2) hg y
  have H := RelativeGrowthGeometry.gap_comparison hpos hgc hgg hgl
    (H := surrogate q f) (v := direction q f) (M := smoothness q)
    (fun a b => by
      have H := surrogate_upper_of_bounds (WeakInterpolationDesign.weight_nonneg (valid hp))
        hg hl (smooth_bound hp) a b
      linarith only [H]) halign x z (surrogate_min (WeakInterpolationDesign.weight_nonneg (valid hp)) hz)
  have H' := mul_le_mul_of_nonneg_left (hq x) hpos.le
  rw [hi]
  simp only [mul_sub, Finset.sum_sub_distrib]
  change p.μ^2*I * (Metric.infDist x (solutions p.toParams f)^2/2) ≤ surrogate q f x-surrogate q f z
  linarith only [H, H']

lemma certificate (hp : spec.valid p) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x-gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (hr : ∀ x, ∑ i, ‖gradient (f i) x‖^2 ≤ (p.n : ℝ)*p.ρ*‖gradient (objective p.toParams f) x‖^2)
    {z : Point p} (hz : z ∈ solutions p.toParams f) (hR : ‖p.x0-z‖ ≤ p.R)
    (hq : ∀ x, p.μ / 2 * Metric.infDist x (solutions p.toParams f)^2 ≤ objective p.toParams f x-objective p.toParams f z)
    {P : ProbabilityMeasure (Samples p)} {g : Fin p.n → Point p → p.Ω → Point p}
    {ν : Fin p.n → ProbabilityMeasure p.Ω}
    (hw : ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hi : ∀ i, Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
      (ν i : Measure _) (P : Measure _) ∧
      Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ) :
    WeightedInterpolationStep.Certificate (tuning p) f g z (P : Measure (Samples p)) ν where
  valid := valid hp
  convex := hc
  differentiable := hg
  solution := hz
  initial := hR
  workers := hw
  samples i := (hi i).1
  stochastic i := (hi i).2
  radius k i x := by
    change Point p at x
    change Fin p.n at i
    let q := tuning p
    let a := stepSize q k * weights q i / fraction q i
    have ha : 0 ≤ a := (WeightedInterpolationPrecision.alpha_bounds (valid hp) k i).1
    have h0 : gradient (f i) z = 0 := by simp [gradient, ((hz i).isLocalMin Filter.univ_mem).fderiv_eq_zero]
    have H := hl i x z
    rw [h0, sub_zero] at H
    change ‖a • gradient (f i) x‖ ≤ ‖x-p.x0‖ + p.R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    calc
      _ ≤ a * (p.L i * ‖x-z‖) := mul_le_mul_of_nonneg_left H ha
      _ ≤ 1 * ‖x-z‖ := by rw [← mul_assoc]; gcongr; exact local_factor hp k i
      _ ≤ _ := by linarith only [norm_sub_le_norm_sub_add_norm_sub x p.x0 z, hR]
  gradient_sq _ hy x := direction_sq_of_bounds (WeakInterpolationDesign.weight_nonneg (valid hp))
    hg hl (WeakInterpolationDesign.smoothness_pos (valid hp)) (smooth_bound hp) hy x
  weighted_growth := weighted_gap hp hc hg hl hr hz hq

end LongTails.Proofs.RelativeGrowthCertificate
