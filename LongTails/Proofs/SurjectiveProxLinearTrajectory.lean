import LongTails.Proofs.SurjectiveProxLinearOracle

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearTrajectory

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearModel

noncomputable def initialEstimator (p : Params) (Z : p.E → p.Ω → JointSpace p)
    (ξ : ℕ → p.Ω) : JointSpace p :=
  (1 / (initialBatch p : ℝ)) • ∑ i : Fin (initialBatch p), Z p.x0 (ξ i)

noncomputable def nextPoint (p : Params) (z : p.E × JointSpace p) : p.E :=
  z.1 + relaxation p • modelStep p ((jointEquiv p).symm z.2)

noncomputable def trajectory (p : Params) (Z : p.E → p.Ω → JointSpace p)
    (ξ : ℕ → p.Ω) : ℕ → p.E × JointSpace p
  | 0 => (p.x0, initialEstimator p Z ξ)
  | k + 1 =>
    let z := trajectory p Z ξ k
    (nextPoint p z, Z (nextPoint p z) (ξ (initialBatch p + k)) +
      (1 - beta p) • (z.2 - Z z.1 (ξ (initialBatch p + k))))

lemma initialEstimator_congr (p : Params) (Z : p.E → p.Ω → JointSpace p)
    {ξ ξ' : ℕ → p.Ω} (h : ∀ i, i < initialBatch p → ξ i = ξ' i) :
    initialEstimator p Z ξ = initialEstimator p Z ξ' := by
  unfold initialEstimator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h i i.isLt]

lemma trajectory_congr (p : Params) (Z : p.E → p.Ω → JointSpace p)
    {ξ ξ' : ℕ → p.Ω} : ∀ k, (∀ i, i < initialBatch p + k → ξ i = ξ' i) →
      trajectory p Z ξ k = trajectory p Z ξ' k
  | 0, h => by
    simp only [trajectory]
    rw [initialEstimator_congr p Z (fun i hi => h i (by omega))]
  | k + 1, h => by
    simp only [trajectory]
    rw [trajectory_congr p Z k (fun i hi => h i (by omega)), h (initialBatch p + k) (by omega)]

lemma continuous_nextPoint (p : Params) (hp : spec.valid p) : Continuous (nextPoint p) := by
  have hs := continuous_modelStep p hp
  have hj := (jointEquiv p).symm.continuous
  unfold nextPoint
  fun_prop

lemma measurable_initialEstimator (p : Params) (Z : p.E → p.Ω → JointSpace p)
    (hZ : Measurable (Function.uncurry Z)) : Measurable (initialEstimator p Z) := by
  unfold initialEstimator
  have hs : Measurable (fun ξ : ℕ → p.Ω =>
      ∑ i : Fin (initialBatch p), Z p.x0 (ξ i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hZ.comp (measurable_const.prodMk (measurable_pi_apply i.val))
  exact hs.const_smul (1 / (initialBatch p : ℝ))

lemma measurable_trajectory (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z)) :
    ∀ k, Measurable (fun ξ => trajectory p Z ξ k)
  | 0 => measurable_const.prodMk (measurable_initialEstimator p Z hZ)
  | k + 1 => by
    have hk := measurable_trajectory p hp Z hZ k
    have hn := (continuous_nextPoint p hp).measurable.comp hk
    have hnew := hZ.comp (hn.prodMk (measurable_pi_apply (initialBatch p + k)))
    have hold := hZ.comp (hk.fst.prodMk (measurable_pi_apply (initialBatch p + k)))
    exact hn.prodMk (hnew.add ((hk.snd.sub hold).const_smul (1 - beta p)))

lemma trajectory_displacement (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (ξ : ℕ → p.Ω)
    (hθ : 0 ≤ relaxation p) : ∀ k,
    ‖(trajectory p Z ξ k).1 - p.x0‖ ≤
      k * relaxation p * (eta p * (p.H + (rho p * p.m) * p.H))
  | 0 => by simp [trajectory]
  | k + 1 => by
    have hk := trajectory_displacement p hp Z ξ hθ k
    have hs := norm_modelStep_le p hp ((jointEquiv p).symm (trajectory p Z ξ k).2)
    have heq : (trajectory p Z ξ (k + 1)).1 - p.x0 =
        ((trajectory p Z ξ k).1 - p.x0) +
        relaxation p • modelStep p ((jointEquiv p).symm (trajectory p Z ξ k).2) := by
      simp only [trajectory, nextPoint]
      abel
    rw [heq]
    have ht := norm_add_le ((trajectory p Z ξ k).1 - p.x0)
      (relaxation p • modelStep p ((jointEquiv p).symm (trajectory p Z ξ k).2))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] at ht
    have hscaled := mul_le_mul_of_nonneg_left hs hθ
    push_cast
    nlinarith

end LongTails.Proofs.SurjectiveProxLinearTrajectory
