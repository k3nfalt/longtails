import LongTails.Proofs.ContinuizedQuasarFlow
import LongTails.Proofs.ExponentialHolding
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma energy_continuous {f : E → ℝ} (hf : Continuous f) (μ : ℝ) (u : E) :
    Continuous (SimilarQuasar.energy f μ u) := by
  unfold SimilarQuasar.energy
  fun_prop

lemma sample_energy_step {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    (g : Fin n × E → E) {L μ γ θ δ : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hθ : 0 < θ) (hrt : γ * θ ≤ 1) (hδ : 0 ≤ δ) (hstep : θ ^ 2 * L ≤ μ)
    (hsmall : 8 * θ ^ 2 * δ ^ 2 / (γ * μ ^ 2) ≤ γ * θ / 64)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2)
    (u : E) (hmin : ∀ x, f u ≤ f x)
    (hquasar : ∀ x, γ * f x + ⟪G x, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (hqg : ∀ x, γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u)
    (w : E) (s : E × E) :
    let b := 8 * θ ^ 2 * δ ^ 2 / (γ * μ ^ 2)
    let c := γ * θ - b
    Integrable (fun q => SimilarQuasar.energy f μ u (sampleUpdate γ θ μ g w s q))
      (sampleLaw n : Measure (ℝ × Fin n)) ∧
    (∫ q, SimilarQuasar.energy f μ u (sampleUpdate γ θ μ g w s q)
      ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤
      4 / (4 + c) * SimilarQuasar.energy f μ u s + b * (f w - f u) := by
  classical
  let b := 8 * θ ^ 2 * δ ^ 2 / (γ * μ ^ 2)
  let c := γ * θ - b
  let V := SimilarQuasar.energy f μ u
  let A := f w - f u
  let H := fun (i : Fin n) (v : E × E) => V (jump θ μ v (FiniteSum.estimator g w v.1 i))
  let J := fun v => 𝔼 i, H i v
  let D := fun v : E × E => θ * ⟪G v.1, v.2 - v.1⟫ +
    μ * γ * θ * ⟪v.2 - u, v.1 - v.2⟫
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c, b]; nlinarith [mul_pos hγ hθ]
  have hG : Continuous G :=
    (show LipschitzWith ⟨L, hL⟩ G from lipschitzWith_iff_norm_sub_le.mpr hlip).continuous
  have hcomp := components_continuous g G hδ hG hsim
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hV : Continuous V := energy_continuous hf μ u
  have hH (i : Fin n) : Continuous (H i) := by
    have he : Continuous (fun v : E × E => FiniteSum.estimator g w v.1 i) :=
      (((hcomp i).comp continuous_fst).sub continuous_const).add continuous_const
    exact hV.comp ((continuous_fst.sub (he.const_smul (θ ^ 2 / μ))).prodMk
      (continuous_snd.sub (he.const_smul (θ / μ))))
  have hJ : Continuous J := by
    dsimp [J]
    simp only [Fintype.expect_eq_sum_div_card]
    fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hV0 (v : E × E) : 0 ≤ V v := SimilarQuasar.energy_nonneg hμ.le hmin v
  have hraw (v : E × E) : J v ≤ V v - θ * ⟪G v.1, v.2 - u⟫ + b * (V v + A) :=
    estimator_jump_bound g hμ hγ hγ1 hstep hg hlip hfull hsim u hmin hqg w v
  have hjump (v : E × E) : J v ≤ 4 * V v + b * A := by
    have hcross := jump_cross_bound hμ hstep hg hlip u hmin v
    have hvb := mul_le_mul_of_nonneg_right hb1 (hV0 v)
    dsimp only [V] at hraw ⊢
    nlinarith [hraw v, hV0 v]
  have hgen (v : E × E) : D v + J v - V v ≤ -c * V v + b * A := by
    have hh := generator_model hθ.le v.1 v.2 u (G v.1) (hquasar v.1) (hraw v)
    have hn : 0 ≤ γ * μ * θ / 2 * ‖v.2 - v.1‖ ^ 2 := by positivity
    dsimp only [D, c, V] at hh ⊢
    nlinarith
  have hfc : Continuous (fun t => flow γ θ t s) :=
    (flow_continuous γ θ).comp (continuous_id.prodMk continuous_const)
  obtain ⟨CB, hCB⟩ := continuous_flow_bounded hγ.le hθ.le V hV s
  obtain ⟨CD, hCD⟩ := continuous_flow_bounded hγ.le hθ.le D hD s
  obtain ⟨CJ, hCJ⟩ := continuous_flow_bounded hγ.le hθ.le J hJ s
  have hh := holding_contraction hc (hV.comp hfc) (hD.comp hfc) (hJ.comp hfc)
    (fun t => flow_energy_hasDerivAt hγ.le hg s u t) hCB hCD hCJ
    (fun t _ => hgen (flow γ θ t s)) (fun t _ => hjump (flow γ θ t s))
  have hInt := sample_flow_integrable hγ.le hθ.le H hH s (sampleLaw n)
  refine ⟨hInt, ?_⟩
  have he : (∫ q, V (sampleUpdate γ θ μ g w s q) ∂(sampleLaw n : Measure (ℝ × Fin n))) =
      ∫ t, J (flow γ θ t s) ∂expMeasure 1 := by
    let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
    change (∫ q, H q.2 (flow γ θ (max 0 q.1) s)
      ∂(expMeasure 1).prod (PMF.uniformOfFintype (Fin n)).toMeasure) = _
    rw [integral_prod _ hInt]
    simp_rw [FiniteSum.uniform_integral]
    rw [integral_expMeasure_one, integral_expMeasure_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    simp only [max_eq_right ht.le]
    rfl
  change (∫ q, V (sampleUpdate γ θ μ g w s q) ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤ _
  rw [he]
  simpa only [Function.comp_apply, flow, flowWeight, mul_zero, Real.exp_zero,
    sub_self, zero_div, sub_zero, one_smul, zero_smul, add_zero, zero_add] using hh

end OracleTemplate.ContinuizedSimilarQuasar
