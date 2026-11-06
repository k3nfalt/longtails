import LongTails.Proofs.SurjectiveProxLinearProcess

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearMoments

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearProcess
open LongTails.Proofs.SurjectiveProxLinearTuning

noncomputable def innovation (p : Params) (I : Problem p) (Z : p.E → p.Ω → JointSpace p)
    (z : p.E × JointSpace p) (ω : p.Ω) : JointSpace p :=
  Z (nextPoint p z) ω - jointMean p I (nextPoint p z) -
    (1 - beta p) • (Z z.1 ω - jointMean p I z.1)

lemma innovation_measurable (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (Z : p.E → p.Ω → JointSpace p)
    (hZ : Measurable (Function.uncurry Z)) :
    Measurable (Function.uncurry (innovation p I Z)) := by
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  have hn : Measurable (fun z : (p.E × JointSpace p) × p.Ω => nextPoint p z.1) :=
    (continuous_nextPoint p hp).measurable.comp measurable_fst
  have hx : Measurable (fun z : (p.E × JointSpace p) × p.Ω => z.1.1) := measurable_fst.fst
  exact ((hZ.comp (hn.prodMk measurable_snd)).sub (hM.comp hn)).sub
    (((hZ.comp (hx.prodMk measurable_snd)).sub (hM.comp hx)).const_smul (1 - beta p))

lemma innovation_moments (p : Params) (I : Problem p) (hp : spec.valid p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (z : p.E × JointSpace p) :
    Integrable (innovation p I (jointOracle p g v D) z) μ ∧
    (∫ ω, innovation p I (jointOracle p g v D) z ω ∂μ) = 0 ∧
    Integrable (fun ω => ‖innovation p I (jointOracle p g v D) z ω‖ ^ 2) μ ∧
    (∫ ω, ‖innovation p I (jointOracle p g v D) z ω‖ ^ 2 ∂μ) ≤
      2 * beta p ^ 2 * p.σ ^ 2 + 2 * p.H ^ 2 * ‖nextPoint p z - z.1‖ ^ 2 := by
  have hb := variance_scales_positive p hp
  have h := ProxLinearOracleMoments.recursive_noise_moment
    (jointOracle_integrable p I g v D μ O (nextPoint p z))
    (jointOracle_integrable p I g v D μ O z.1)
    (jointMean p I (nextPoint p z)) (jointMean p I z.1)
    (jointOracle_mean p I g v D μ O (nextPoint p z))
    (jointOracle_mean p I g v D μ O z.1)
    (jointOracle_variance p I g v D μ O (nextPoint p z)).1
    (jointOracle_difference p I g v D μ O (nextPoint p z) z.1).1
    hb.2.2.2.1.le hb.2.2.2.2.1
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans ?_⟩
  have hvar := mul_le_mul_of_nonneg_left
    (jointOracle_variance p I g v D μ O (nextPoint p z)).2
    (show 0 ≤ 2 * beta p ^ 2 by positivity)
  have hdiff := mul_le_mul_of_nonneg_left
    (jointOracle_difference p I g v D μ O (nextPoint p z) z.1).2
    (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma error_recursion (p : Params) (I : Problem p) (Z : p.E → p.Ω → JointSpace p)
    (ξ : ℕ → p.Ω) (k : ℕ) :
    estimatorError p I Z ξ (k + 1) = (1 - beta p) • estimatorError p I Z ξ k +
      innovation p I Z (trajectory p Z ξ k) (ξ (initialBatch p + k)) := by
  simp only [estimatorError, trajectory, innovation]
  module

lemma measurable_estimatorError (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (Z : p.E → p.Ω → JointSpace p)
    (hZ : Measurable (Function.uncurry Z)) (k : ℕ) :
    Measurable (fun ξ => estimatorError p I Z ξ k) := by
  have hs := measurable_trajectory p hp Z hZ k
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  exact hs.snd.sub (hM.comp hs.fst)

end LongTails.Proofs.SurjectiveProxLinearMoments
