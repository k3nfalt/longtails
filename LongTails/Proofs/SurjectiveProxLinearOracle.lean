import LongTails.Proofs.SurjectiveProxLinearExactModel
import LongTails.Proofs.SymmetricThirdOrderSampling
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearOracle

open LongTails.Setups.StochasticSurjectiveInequalities

abbrev JointSpace (p : Params) := WithLp 2 (p.E × WithLp 2 (Constraint p × Jacobian p))

instance (p : Params) : MeasurableSpace (JointSpace p) := borel (JointSpace p)
instance (p : Params) : BorelSpace (JointSpace p) := ⟨rfl⟩

noncomputable def jointEquiv (p : Params) : Primitive p ≃L[ℝ] JointSpace p :=
  ((ContinuousLinearEquiv.refl ℝ p.E).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Constraint p) (Jacobian p)).symm).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ p.E (WithLp 2 (Constraint p × Jacobian p))).symm

lemma jointEquiv_apply (p : Params) (v : Primitive p) :
    jointEquiv p v = WithLp.toLp 2 (v.1, WithLp.toLp 2 v.2) := rfl

lemma jointEquiv_norm_sq (p : Params) (v : Primitive p) :
    ‖jointEquiv p v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2 := by
  simp only [jointEquiv_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

lemma jointEquiv_sub_norm_sq (p : Params) (v w : Primitive p) :
    ‖jointEquiv p v - jointEquiv p w‖ ^ 2 =
      ‖v.1 - w.1‖ ^ 2 + ‖v.2.1 - w.2.1‖ ^ 2 + ‖v.2.2 - w.2.2‖ ^ 2 := by
  rw [← map_sub, jointEquiv_norm_sq]
  rfl

noncomputable def jointMean (p : Params) (I : Problem p) (x : p.E) : JointSpace p :=
  jointEquiv p (gradient I.f x, I.c x, I.J x)

noncomputable def jointOracle (p : Params) (g : p.E → p.Ω → p.E)
    (v : p.E → p.Ω → Constraint p) (D : p.E → p.Ω → Jacobian p)
    (x : p.E) (ω : p.Ω) : JointSpace p := jointEquiv p (g x ω, v x ω, D x ω)

lemma jointOracle_measurable (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    Measurable (Function.uncurry (jointOracle p g v D)) := by
  exact (jointEquiv p).continuous.measurable.comp
    (O.gradientMeasurable.prodMk (O.valueMeasurable.prodMk O.jacobianMeasurable))

lemma jointOracle_integrable (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (x : p.E) :
    Integrable (jointOracle p g v D x) μ := by
  exact (jointEquiv p).toContinuousLinearMap.integrable_comp
    ((O.integrable x).1.prodMk ((O.integrable x).2.1.prodMk (O.integrable x).2.2))

lemma jointOracle_mean (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (x : p.E) :
    (∫ ω, jointOracle p g v D x ω ∂μ) = jointMean p I x := by
  unfold jointOracle jointMean
  calc
    _ = (jointEquiv p).toContinuousLinearMap (∫ ω, (g x ω, v x ω, D x ω) ∂μ) :=
      (jointEquiv p).toContinuousLinearMap.integral_comp_comm
        ((O.integrable x).1.prodMk ((O.integrable x).2.1.prodMk (O.integrable x).2.2))
    _ = _ := by
      rw [integral_pair (O.integrable x).1
        ((O.integrable x).2.1.prodMk (O.integrable x).2.2),
        integral_pair (O.integrable x).2.1 (O.integrable x).2.2,
        O.gradientMean, O.valueMean, O.jacobianMean]
      rfl

lemma jointOracle_variance (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (x : p.E) :
    Integrable (fun ω => ‖jointOracle p g v D x ω - jointMean p I x‖ ^ 2) μ ∧
    (∫ ω, ‖jointOracle p g v D x ω - jointMean p I x‖ ^ 2 ∂μ) ≤ p.σ ^ 2 := by
  simp only [jointOracle, jointMean, jointEquiv_sub_norm_sq]
  exact ⟨O.varianceIntegrable x, O.variance x⟩

lemma jointOracle_difference (p : Params) (I : Problem p)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (x y : p.E) :
    Integrable (fun ω => ‖jointOracle p g v D x ω - jointOracle p g v D y ω‖ ^ 2) μ ∧
    (∫ ω, ‖jointOracle p g v D x ω - jointOracle p g v D y ω‖ ^ 2 ∂μ) ≤
      p.H ^ 2 * ‖x - y‖ ^ 2 := by
  simp only [jointOracle, jointEquiv_sub_norm_sq]
  exact ⟨O.differenceIntegrable x y, O.meanSquaredSmooth x y⟩

lemma jointMean_continuous (p : Params) (I : Problem p) (H : Regularity p I) (hH : 0 ≤ p.H) :
    Continuous (jointMean p I) := by
  exact (jointEquiv p).continuous.comp
    ((SurjectiveProxLinearExactModel.gradient_continuous p I H hH).prodMk
      ((SurjectiveProxLinearExactModel.constraints_continuous p I H).prodMk
        (SurjectiveProxLinearExactModel.jacobian_continuous p I H hH)))

lemma adaptive_batch_variance (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (ξ : ℕ → Ξ → p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure _) P)
    (n m : ℕ) (hm : 0 < m) (x : (Fin n → p.Ω) → p.E) (hx : Measurable x) :
    Integrable (fun ω => ‖(1 / (m : ℝ)) • ∑ i : Fin m,
      jointOracle p g v D (x (fun j => ξ j ω)) (ξ (n + i) ω) -
      jointMean p I (x (fun j => ξ j ω))‖ ^ 2) P ∧
    (∫ ω, ‖(1 / (m : ℝ)) • ∑ i : Fin m,
      jointOracle p g v D (x (fun j => ξ j ω)) (ξ (n + i) ω) -
      jointMean p I (x (fun j => ξ j ω))‖ ^ 2 ∂P) ≤ p.σ ^ 2 / m := by
  let F : (Fin n → p.Ω) × (Fin m → p.Ω) → ℝ := fun z =>
    ‖(1 / (m : ℝ)) • ∑ i : Fin m, jointOracle p g v D (x z.1) (z.2 i) -
      jointMean p I (x z.1)‖ ^ 2
  have hZ := jointOracle_measurable p I g v D μ O
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub
    · have hs : Measurable (fun z : (Fin n → p.Ω) × (Fin m → p.Ω) =>
          ∑ i : Fin m, jointOracle p g v D (x z.1) (z.2 i)) := by
        apply Finset.measurable_sum
        intro i _
        exact hZ.comp ((hx.comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))
      exact hs.const_smul (1 / (m : ℝ))
    · exact hM.comp (hx.comp measurable_fst)
  have hv (u : Fin n → p.Ω) := OracleTemplate.RobustGradient.finite_mean_variance
    (hZ.comp (measurable_const.prodMk measurable_id))
    (jointOracle_integrable p I g v D μ O (x u)) (jointMean p I (x u))
    (jointOracle_variance p I g v D μ O (x u)).1
    (jointOracle_mean p I g v D μ O (x u)) m hm
  exact SymmetricThirdOrderSampling.prefix_block_nonnegative_bound hξ n m F (p.σ ^ 2 / m)
    hF (fun _ => sq_nonneg _) (fun u => (hv u).1) (fun u => (hv u).2.le.trans
      (div_le_div_of_nonneg_right (jointOracle_variance p I g v D μ O (x u)).2
        (Nat.cast_nonneg m)))

end LongTails.Proofs.SurjectiveProxLinearOracle
