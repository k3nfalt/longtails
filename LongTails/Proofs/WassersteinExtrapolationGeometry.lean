import LongTails.Proofs.WassersteinCouplings
import LongTails.Proofs.WassersteinAccelerationEnergy

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Proofs.WassersteinCouplings
open LongTails.Proofs.WassersteinAccelerationEnergy

namespace LongTails.Proofs.WassersteinExtrapolationGeometry

lemma extrapolated_joint_cost {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ ν ρ : Distribution d) (f g q : Ω → Space d)
    (hf : Measurable f) (hg : Measurable g) (hq : Measurable q)
    (hfm : P.map f = μ.law) (hgm : P.map g = ν.law) (hqm : P.map q = ρ.law)
    (t : ℝ) :
    (∫ ω, ‖t • f ω - (t - 1) • g ω - q ω‖ ^ 2 ∂P) =
      t * (∫ ω, ‖f ω - q ω‖ ^ 2 ∂P) -
      (t - 1) * (∫ ω, ‖g ω - q ω‖ ^ 2 ∂P) +
      t * (t - 1) * (∫ ω, ‖f ω - g ω‖ ^ 2 ∂P) := by
  have h1 := integrable_sq_sub_of_maps P μ ρ f q hf hq hfm hqm
  have h2 := integrable_sq_sub_of_maps P ν ρ g q hg hq hgm hqm
  have h3 := integrable_sq_sub_of_maps P μ ν f g hf hg hfm hgm
  simp_rw [extrapolated_norm_identity]
  have ha := integral_add ((h1.const_mul t).sub (h2.const_mul (t - 1)))
    (h3.const_mul (t * (t - 1)))
  simp only [Pi.sub_apply] at ha
  rw [ha, integral_sub (h1.const_mul t) (h2.const_mul (t - 1))]
  simp only [integral_const_mul]

lemma transport_energy_nonnegative {d : ℕ} (μ ν ρ : Distribution d)
    (A : OptimalTransport μ ν) (B : OptimalTransport μ ρ) (t : ℝ) (ht : 1 ≤ t) :
    0 ≤ t * squaredDistance μ ρ - (t - 1) * squaredDistance ν ρ +
      t * (t - 1) * squaredDistance μ ν := by
  have he := extrapolated_joint_cost (μ.law : Measure (Space d)) μ ν ρ
    id A.toFun B.toFun measurable_id A.measurable B.measurable
    (Measure.map_id) A.pushforward B.pushforward t
  have hA := squaredDistance_eq_map_cost A.toFun A.measurable A.pushforward
    A.finiteCost A.optimal
  have hB := squaredDistance_eq_map_cost B.toFun B.measurable B.pushforward
    B.finiteCost B.optimal
  simp only [id_eq] at he
  rw [← hA, ← hB] at he
  have hp : 0 ≤ ∫ x, ‖t • x - (t - 1) • A.toFun x - B.toFun x‖ ^ 2
      ∂(μ.law : Measure (Space d)) := integral_nonneg (fun _ => sq_nonneg _)
  have hd := squaredDistance_le_cost (couplingOfMaps μ.law ν ρ A.toFun B.toFun
    A.measurable B.measurable A.pushforward B.pushforward)
  rw [couplingOfMaps_cost] at hd
  have hm := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht)
  linarith

lemma extrapolation_distance_upper {d : ℕ} (μ ν ρ y : Distribution d)
    (A : OptimalTransport μ ν) (B : OptimalTransport μ ρ) (β : ℝ) (hβ : 0 ≤ β)
    (hy : (μ.law : Measure (Space d)).map
      (fun x => (1 + β) • x - β • A.toFun x) = y.law) :
    squaredDistance y ρ ≤ (1 + β) * squaredDistance μ ρ - β * squaredDistance ν ρ +
      β * (1 + β) * squaredDistance μ ν := by
  have he := extrapolated_joint_cost (μ.law : Measure (Space d)) μ ν ρ
    id A.toFun B.toFun measurable_id A.measurable B.measurable
    (Measure.map_id) A.pushforward B.pushforward (1 + β)
  have hA := squaredDistance_eq_map_cost A.toFun A.measurable A.pushforward
    A.finiteCost A.optimal
  have hB := squaredDistance_eq_map_cost B.toFun B.measurable B.pushforward
    B.finiteCost B.optimal
  have hc := squaredDistance_le_cost (couplingOfMaps μ.law y ρ
    (fun x => (1 + β) • x - β • A.toFun x) B.toFun
    (by have hAmeas := A.measurable; fun_prop) B.measurable hy B.pushforward)
  rw [couplingOfMaps_cost] at hc
  have hd := squaredDistance_le_cost (couplingOfMaps μ.law ν ρ A.toFun B.toFun
    A.measurable B.measurable A.pushforward B.pushforward)
  rw [couplingOfMaps_cost] at hd
  simp only [id_eq, add_sub_cancel_left] at he
  rw [← hA, ← hB] at he
  have hm := mul_le_mul_of_nonneg_left hd hβ
  nlinarith

lemma extrapolation_movement_upper {d : ℕ} (μ ν y : Distribution d)
    (A : OptimalTransport μ ν) (β : ℝ)
    (hy : (μ.law : Measure (Space d)).map
      (fun x => (1 + β) • x - β • A.toFun x) = y.law) :
    squaredDistance y μ ≤ β ^ 2 * squaredDistance μ ν := by
  have hc := squaredDistance_le_cost (couplingOfMaps μ.law y μ
    (fun x => (1 + β) • x - β • A.toFun x) id
    (by have hAmeas := A.measurable; fun_prop) measurable_id hy (Measure.map_id))
  rw [couplingOfMaps_cost] at hc
  have he : ∀ x, ‖(1 + β) • x - β • A.toFun x - id x‖ ^ 2 =
      β ^ 2 * ‖x - A.toFun x‖ ^ 2 := by
    intro x
    have hv : (1 + β) • x - β • A.toFun x - id x = β • (x - A.toFun x) := by
      simp only [id_eq]
      module
    rw [hv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [he] at hc
  rw [integral_const_mul] at hc
  rwa [← squaredDistance_eq_map_cost A.toFun A.measurable A.pushforward
    A.finiteCost A.optimal] at hc

lemma extrapolated_second_moment {d : ℕ} {μ ν : Distribution d}
    (A : Transport μ ν) (β : ℝ) :
    Integrable (fun x => ‖(1 + β) • x - β • A.toFun x‖ ^ 2)
      (μ.law : Measure (Space d)) := by
  have hi : Integrable (fun x => ‖A.toFun x‖ ^ 2) (μ.law : Measure (Space d)) :=
    integrable_of_marginal (μ.law : Measure (Space d)) ν A.toFun A.measurable
      A.pushforward (fun x => ‖x‖ ^ 2) ν.secondMoment
  have hm := ((μ.secondMoment.const_mul ((1 + β) ^ 2)).add
    (hi.const_mul (β ^ 2))).const_mul 2
  apply hm.mono'
  · have hAmeas := A.measurable
    fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖(1 + β) • x - β • A.toFun x‖ ^ 2 ≤
      2 * ((1 + β) ^ 2 * ‖x‖ ^ 2 + β ^ 2 * ‖A.toFun x‖ ^ 2)
    have hn := norm_sub_le ((1 + β) • x) (β • A.toFun x)
    have hs : ‖(1 + β) • x - β • A.toFun x‖ ^ 2 ≤
        2 * (‖(1 + β) • x‖ ^ 2 + ‖β • A.toFun x‖ ^ 2) := by
      nlinarith [norm_nonneg ((1 + β) • x - β • A.toFun x),
        norm_nonneg ((1 + β) • x), norm_nonneg (β • A.toFun x),
        sq_nonneg (‖(1 + β) • x‖ - ‖β • A.toFun x‖)]
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hs

end LongTails.Proofs.WassersteinExtrapolationGeometry
