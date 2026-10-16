import LongTails.Algorithms.RelativeQuasar
import LongTails.Proofs.RelativeQuasarEnergy
import LongTails.Proofs.RelativeQuasarHolding
import LongTails.Proofs.ContinuizedQuasarStep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeQuasar

open ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
set_option maxHeartbeats 1000000 in
lemma advance_measurable (L μ γ θ : ℝ) {g : E → E} (hm : Measurable g) :
    Measurable (fun q : (E × E) × ℝ => advance L μ γ θ g q.1 q.2) := by
  have hy : Measurable (fun q : (E × E) × ℝ => flow γ θ (max 0 q.2) q.1) :=
    (flow_continuous γ θ).measurable.comp
      ((measurable_const.max measurable_snd).prodMk measurable_fst)
  have hv := hm.comp hy.fst
  exact (hy.fst.sub (hv.const_smul (1 / L))).prodMk
    (hy.snd.sub (hv.const_smul (2 * θ / μ)))

lemma sample_energy_step {f : E → ℝ} {G g : E → E} {L μ γ θ δ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm : Measurable g)
    (hstep : 16 * L * θ ^ 2 ≤ μ)
    (hcoef : (δ ^ 2 - 1) / (2 * L) + 4 * θ ^ 2 / μ +
      2 * θ * δ ^ 2 / (γ * μ) ≤ 0)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (he : ∀ x, ‖g x - G x‖ ≤ δ * ‖G x‖)
    (u : E) (hmin : ∀ x, f u ≤ f x)
    (hquasar : ∀ x, γ * f x + ⟪G x, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (s : E × E) :
    Integrable (fun t => SimilarQuasar.energy f (μ / 2) u (advance L μ γ θ g s t))
      (holdingLaw : Measure ℝ) ∧
    (∫ t, SimilarQuasar.energy f (μ / 2) u (advance L μ γ θ g s t) ∂(holdingLaw : Measure ℝ)) ≤
      4 / (4 + γ * θ) * SimilarQuasar.energy f (μ / 2) u s := by
  let V := SimilarQuasar.energy f (μ / 2) u
  let D := fun v : E × E => θ * ⟪G v.1, v.2 - v.1⟫ +
    (μ / 2) * γ * θ * ⟪v.2 - u, v.1 - v.2⟫
  let J := fun v : E × E => V (RelativeQuasar.jump L μ θ v (g v.1))
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hG : Continuous G :=
    (show LipschitzWith ⟨L, hL.le⟩ G from lipschitzWith_iff_norm_sub_le.mpr hlip).continuous
  have hV : Continuous V := energy_continuous hf (μ / 2) u
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hJ : Measurable J := by
    have hv := hm.comp (measurable_fst : Measurable (fun v : E × E => v.1))
    exact hV.measurable.comp ((measurable_fst.sub (hv.const_smul (1 / L))).prodMk
      (measurable_snd.sub (hv.const_smul (2 * θ / μ))))
  have hV0 (v : E × E) : 0 ≤ V v := SimilarQuasar.energy_nonneg (by positivity) hmin v
  have hJ0 (v : E × E) : 0 ≤ J v := hV0 _
  have hmodel (x w : E) := Gradient.smooth_upper_bound hg hlip x (x - (1 / L) • w)
  have hJB (v : E × E) : J v ≤ 4 * V v :=
    decoupled_jump_growth hL hμ hδ hδ1 hstep v.1 v.2 u (G v.1) (g v.1)
      hmin (hmodel v.1) (he v.1)
  have hgen (v : E × E) : D v + J v - V v ≤ -(γ * θ) * V v :=
    relative_generator hL hμ hγ hθ hδ hδ1 hcoef v.1 v.2 u (G v.1) (g v.1)
      (hquasar v.1) (hmodel v.1 (g v.1)) (he v.1)
  obtain ⟨CB, hCB⟩ := continuous_flow_bounded hγ.le hθ V hV s
  obtain ⟨CD, hCD⟩ := continuous_flow_bounded hγ.le hθ D hD s
  have hjb (t : ℝ) (ht : 0 ≤ t) : ‖J (flow γ θ t s)‖ ≤ 4 * CB := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hJ0 _)]
    have hb := hCB t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 _)] at hb
    exact (hJB _).trans (by linarith)
  have hflow : Continuous (fun t : ℝ => flow γ θ t s) :=
    (flow_continuous γ θ).comp (continuous_id.prodMk continuous_const)
  have hInt : Integrable (fun t => V (advance L μ γ θ g s t)) (holdingLaw : Measure ℝ) := by
    apply (integrable_const (4 * CB)).mono'
      (hV.measurable.comp ((advance_measurable L μ γ θ hm).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => hjb (max 0 t) (le_max_left _ _))
  have hc := measurable_holding_contraction (b := 0) (A := 0)
    (show 0 ≤ γ * θ by positivity) (hV.comp hflow) (hD.comp hflow)
    (hJ.comp hflow.measurable) (flow_energy_hasDerivAt hγ.le hg s u)
    hCB hCD hjb
    (fun t _ => by simpa only [Function.comp_def, mul_zero, add_zero] using hgen (flow γ θ t s))
    (fun t _ => by simpa only [Function.comp_def, mul_zero, add_zero] using hJB (flow γ θ t s))
  have hi : (∫ t, V (advance L μ γ θ g s t) ∂(holdingLaw : Measure ℝ)) =
      ∫ t, J (flow γ θ t s) ∂expMeasure 1 := by
    change (∫ t, V (advance L μ γ θ g s t) ∂expMeasure 1) = _
    rw [integral_expMeasure_one, integral_expMeasure_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [advance, max_eq_right (Set.mem_Ioi.mp ht).le]
    rfl
  refine ⟨hInt, ?_⟩
  rw [hi]
  have hzero : flow γ θ 0 s = s := by simp [flow, flowWeight]
  simpa only [Function.comp_def, hzero, mul_zero, add_zero] using hc

end OracleTemplate.RelativeQuasar
