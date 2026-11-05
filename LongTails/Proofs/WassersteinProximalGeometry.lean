import LongTails.Proofs.WassersteinCouplings
import LongTails.Proofs.WassersteinAccelerationEnergy

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Proofs.WassersteinCouplings
open LongTails.Proofs.WassersteinAccelerationEnergy

namespace LongTails.Proofs.WassersteinProximalGeometry

lemma joint_interpolation_cost {d : ℕ} {base μ ν : Distribution d}
    (π : JointPlan base μ ν) (θ : ℝ) :
    (∫ z, ‖z.1 - ((1 - θ) • z.2.1 + θ • z.2.2)‖ ^ 2
      ∂(π.law : Measure (Space d × Space d × Space d))) =
    (1 - θ) * (∫ z, ‖z.1 - z.2.1‖ ^ 2
      ∂(π.law : Measure (Space d × Space d × Space d))) +
    θ * (∫ z, ‖z.1 - z.2.2‖ ^ 2
      ∂(π.law : Measure (Space d × Space d × Space d))) -
    θ * (1 - θ) * (∫ z, ‖z.2.1 - z.2.2‖ ^ 2
      ∂(π.law : Measure (Space d × Space d × Space d))) := by
  have h1 := integrable_sq_sub_of_maps (π.law : Measure (Space d × Space d × Space d)) base μ
    (fun z => z.1) (fun z => z.2.1) (by fun_prop) (by fun_prop)
    π.baseMarginal π.firstMarginal
  have h2 := integrable_sq_sub_of_maps (π.law : Measure (Space d × Space d × Space d)) base ν
    (fun z => z.1) (fun z => z.2.2) (by fun_prop) (by fun_prop)
    π.baseMarginal π.secondMarginal
  have h3 := integrable_sq_sub_of_maps (π.law : Measure (Space d × Space d × Space d)) μ ν
    (fun z => z.2.1) (fun z => z.2.2) (by fun_prop) (by fun_prop)
    π.firstMarginal π.secondMarginal
  simp_rw [interpolated_norm_identity]
  have hs := integral_sub ((h1.const_mul (1 - θ)).add (h2.const_mul θ))
    (h3.const_mul (θ * (1 - θ)))
  simp only [Pi.add_apply] at hs
  rw [hs, integral_add (h1.const_mul (1 - θ)) (h2.const_mul θ)]
  simp only [integral_const_mul]

lemma joint_interpolation_distance {d : ℕ} {base μ ν ρ : Distribution d}
    (π : OptimalJointPlan base μ ν) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hρ : (ρ.law : Measure (Space d)) =
      (π.law : Measure (Space d × Space d × Space d)).map
        (fun z => (1 - θ) • z.2.1 + θ • z.2.2)) :
    squaredDistance base ρ ≤ (1 - θ) * squaredDistance base μ +
      θ * squaredDistance base ν - θ * (1 - θ) * squaredDistance μ ν := by
  have hc := squaredDistance_le_cost (couplingOfMaps π.law base ρ
    (fun z => z.1) (fun z => (1 - θ) • z.2.1 + θ • z.2.2)
    (by fun_prop) (by fun_prop) π.baseMarginal hρ.symm)
  rw [couplingOfMaps_cost, joint_interpolation_cost π.toJointPlan θ,
    π.firstOptimal, π.secondOptimal] at hc
  have hd := squaredDistance_le_joint_cost π.toJointPlan
  have hm := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2))
  linarith

lemma proximal_evi {d : ℕ} {Q : Set (Distribution d)} {H : Distribution d → ℝ}
    (hconv : GeneralizedGeodesicConvex Q H) (base u v : Distribution d)
    (hu : u ∈ Q) (hv : v ∈ Q) (h : ℝ) (hh : 0 < h)
    (hmin : ∀ ρ ∈ Q, 2 * h * H u + squaredDistance base u ≤
      2 * h * H ρ + squaredDistance base ρ) :
    2 * h * (H u - H v) ≤ squaredDistance base v - squaredDistance base u -
      squaredDistance u v := by
  obtain ⟨π, hπ⟩ := hconv base u v hu hv
  apply remove_interpolation_error _ _ (squaredDistance u v)
    (squaredDistance_nonnegative u v)
  intro θ hθ hθ1
  obtain ⟨ρ, hρ, hρQ, hρH⟩ := hπ θ ⟨le_of_lt hθ, hθ1⟩
  have hd := joint_interpolation_distance π θ ⟨le_of_lt hθ, hθ1⟩ hρ
  have hm := hmin ρ hρQ
  have he := mul_le_mul_of_nonneg_left hρH (by positivity : 0 ≤ 2 * h)
  apply (mul_le_mul_iff_left₀ hθ).mp
  nlinarith

end LongTails.Proofs.WassersteinProximalGeometry
