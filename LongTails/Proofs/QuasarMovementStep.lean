import LongTails.Proofs.QuasarMovementEnergy
import LongTails.Proofs.QuasarMovementFlow

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma sample_energy_slack {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    (g : Fin n × E → E) {L μ γ θ δ : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hstep : 2 * θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2)
    (u : E) (hmin : ∀ x, f u ≤ f x)
    (hquasar : ∀ x, γ * f x + ⟪G x, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (w : E) (s : E × E) :
    let q := 4 / (4 + γ * θ)
    let Id := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2
    let Ig := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖G (flow γ θ t s).1‖ ^ 2
    let Ih := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).1 - w‖ ^ 2
    Integrable (fun a => SimilarQuasar.energy f μ u (sampleUpdate γ θ μ g w s a))
      (sampleLaw n : Measure (ℝ × Fin n)) ∧
    (∫ a, SimilarQuasar.energy f μ u (sampleUpdate γ θ μ g w s a)
      ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤
      q * SimilarQuasar.energy f μ u s - q * (γ * μ * θ / 2) * Id -
        q * (θ ^ 2 / (4 * μ)) * Ig + (θ ^ 2 / μ * δ ^ 2) * Ih := by
  classical
  dsimp only
  let V := SimilarQuasar.energy f μ u
  let H := fun (i : Fin n) (v : E × E) => V (jump θ μ v (FiniteSum.estimator g w v.1 i))
  let J := fun v => 𝔼 i, H i v
  let D := fun v : E × E => θ * ⟪G v.1, v.2 - v.1⟫ +
    μ * γ * θ * ⟪v.2 - u, v.1 - v.2⟫
  let N := fun v : E × E => (θ ^ 2 / μ * δ ^ 2) * ‖v.1 - w‖ ^ 2
  let T := fun v : E × E => γ * μ * θ / 2 * ‖v.2 - v.1‖ ^ 2 +
    θ ^ 2 / (4 * μ) * ‖G v.1‖ ^ 2
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
  have hN : Continuous N := by dsimp [N]; fun_prop
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hraw (v : E × E) : J v ≤ V v - θ * ⟪G v.1, v.2 - u⟫ -
      θ ^ 2 / (4 * μ) * ‖G v.1‖ ^ 2 + N v :=
    estimator_jump_slack g hμ hstep hg hlip hfull hsim u w v
  have hweak : θ ^ 2 * L ≤ μ := by nlinarith [mul_nonneg (sq_nonneg θ) hL]
  have hjump (v : E × E) : J v ≤ 4 * V v + N v := by
    have hh := jump_cross_bound hμ hweak hg hlip u hmin v
    have hv := SimilarQuasar.energy_nonneg hμ.le hmin v
    have hn : 0 ≤ θ ^ 2 / (4 * μ) * ‖G v.1‖ ^ 2 := by positivity
    dsimp only [V] at hraw ⊢
    linarith [hraw v]
  have hgen (v : E × E) : D v + J v - V v ≤ -(γ * θ) * V v - T v + N v := by
    have hh := generator_model (J := J v) hθ v.1 v.2 u (G v.1) (hquasar v.1)
      (Vnoise := N v - θ ^ 2 / (4 * μ) * ‖G v.1‖ ^ 2) (by linarith [hraw v])
    dsimp only [D, T, V] at hh ⊢
    linarith
  have hfc : Continuous (fun t => flow γ θ t s) :=
    (flow_continuous γ θ).comp (continuous_id.prodMk continuous_const)
  obtain ⟨CB, hCB⟩ := continuous_flow_bounded hγ hθ V hV s
  obtain ⟨CD, hCD⟩ := continuous_flow_bounded hγ hθ D hD s
  obtain ⟨CJ, hCJ⟩ := continuous_flow_bounded hγ hθ J hJ s
  obtain ⟨CN, hCN⟩ := continuous_flow_bounded hγ hθ N hN s
  obtain ⟨CT, hCT⟩ := continuous_flow_bounded hγ hθ T hT s
  have hh := weighted_resolvent (mul_nonneg hγ hθ) (hV.comp hfc) (hD.comp hfc)
    (hJ.comp hfc) (hN.comp hfc) (hT.comp hfc)
    (fun t => flow_energy_hasDerivAt hγ hg s u t) hCB hCD hCJ hCN hCT
    (fun t _ => hgen (flow γ θ t s)) (fun t _ => hjump (flow γ θ t s))
  have hInt := sample_flow_integrable hγ hθ H hH s (sampleLaw n)
  refine ⟨hInt, ?_⟩
  have he := sample_flow_integral hγ hθ H hH s
  change (∫ a, H a.2 (flow γ θ (max 0 a.1) s) ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤ _
  rw [he]
  have hAc : Continuous (fun v : E × E => ‖v.2 - v.1‖ ^ 2) := by fun_prop
  have hKc : Continuous (fun v : E × E => ‖G v.1‖ ^ 2) := by fun_prop
  obtain ⟨CA, hCA⟩ := continuous_flow_bounded hγ hθ _ hAc s
  obtain ⟨CK, hCK⟩ := continuous_flow_bounded hγ hθ _ hKc s
  have hAi := weighted_integrable (hAc.comp hfc) hCA
  have hKi := weighted_integrable (hKc.comp hfc) hCK
  simp only [Function.comp_apply, T, N, mul_add] at hh
  simp_rw [show ∀ t : ℝ, Real.exp (-t) * (γ * μ * θ / 2 *
      ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2) = γ * μ * θ / 2 *
      (Real.exp (-t) * ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2) by intro t; ring,
    show ∀ t : ℝ, Real.exp (-t) * (θ ^ 2 / (4 * μ) * ‖G (flow γ θ t s).1‖ ^ 2) =
      θ ^ 2 / (4 * μ) * (Real.exp (-t) * ‖G (flow γ θ t s).1‖ ^ 2) by intro t; ring,
    show ∀ t : ℝ, Real.exp (-t) * (θ ^ 2 / μ * δ ^ 2 * ‖(flow γ θ t s).1 - w‖ ^ 2) =
      (θ ^ 2 / μ * δ ^ 2) * (Real.exp (-t) * ‖(flow γ θ t s).1 - w‖ ^ 2) by intro t; ring] at hh
  have hsum := integral_add (hAi.const_mul (γ * μ * θ / 2)) (hKi.const_mul (θ ^ 2 / (4 * μ)))
  simp only [Function.comp_apply] at hsum
  rw [hsum] at hh
  simp only [integral_const_mul] at hh
  have hzero : V (flow γ θ 0 s) = V s := by simp [flow, flowWeight]
  rw [hzero] at hh
  dsimp only [J] at hh
  convert hh using 1; ring

omit [CompleteSpace E] in
lemma sample_distance_bound {n : ℕ} [NeZero n] (g : Fin n × E → E) (G : E → E)
    {γ θ μ δ m : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hm : 0 < m)
    (hG : Continuous G) (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2) (w : E) (s : E × E) :
    let η := θ ^ 2 / μ
    let Id := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2
    let Ig := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖G (flow γ θ t s).1‖ ^ 2
    let Ih := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).1 - w‖ ^ 2
    Integrable (fun a => ‖(sampleUpdate γ θ μ g w s a).1 - w‖ ^ 2)
      (sampleLaw n : Measure (ℝ × Fin n)) ∧
    (∫ a, ‖(sampleUpdate γ θ μ g w s a).1 - w‖ ^ 2
      ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤
      ‖s.1 - w‖ ^ 2 + (2 / m + η ^ 2 * δ ^ 2) * Ih +
        m * θ ^ 2 * Id + (m + 1) * η ^ 2 * Ig := by
  classical
  dsimp only
  let η := θ ^ 2 / μ
  let B := fun v : E × E => ‖v.1 - w‖ ^ 2
  let H := fun (i : Fin n) (v : E × E) => B (jump θ μ v (FiniteSum.estimator g w v.1 i))
  let J := fun v => 𝔼 i, H i v
  let D := fun v : E × E => 2 * θ * ⟪v.1 - w, v.2 - v.1⟫
  let R := fun v : E × E => (2 / m + η ^ 2 * δ ^ 2) * B v +
    m * θ ^ 2 * ‖v.2 - v.1‖ ^ 2 + (m + 1) * η ^ 2 * ‖G v.1‖ ^ 2
  have hcomp := components_continuous g G hδ hG hsim
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hH (i : Fin n) : Continuous (H i) := by
    have he : Continuous (fun v : E × E => FiniteSum.estimator g w v.1 i) :=
      (((hcomp i).comp continuous_fst).sub continuous_const).add continuous_const
    exact hB.comp ((continuous_fst.sub (he.const_smul (θ ^ 2 / μ))).prodMk
      (continuous_snd.sub (he.const_smul (θ / μ))))
  have hJ : Continuous J := by
    dsimp [J]
    simp only [Fintype.expect_eq_sum_div_card]
    fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hR : Continuous R := by dsimp [R, B]; fun_prop
  have hgen (v : E × E) : D v + J v - B v ≤ R v := by
    have hu : (n : ℝ)⁻¹ • ∑ i, FiniteSum.estimator g w v.1 i = G v.1 := by
      rw [FiniteSum.estimator_unbiased, hfull]
    have hv : (𝔼 i, ‖FiniteSum.estimator g w v.1 i - G v.1‖ ^ 2) ≤
        δ ^ 2 * ‖v.1 - w‖ ^ 2 := by
      have hi (i : Fin n) : FiniteSum.estimator g w v.1 i - G v.1 =
          (g (i, v.1) - G v.1) - (g (i, w) - G w) := by
        dsimp [FiniteSum.estimator]
        rw [hfull]
        abel
      simp_rw [hi]
      exact hsim _ _
    exact distance_generator_bound (FiniteSum.estimator g w v.1) (G v.1) v.1 w
      (v.2 - v.1) θ η δ hm hu hv
  have hfc : Continuous (fun t => flow γ θ t s) :=
    (flow_continuous γ θ).comp (continuous_id.prodMk continuous_const)
  obtain ⟨CB, hCB⟩ := continuous_flow_bounded hγ hθ B hB s
  obtain ⟨CD, hCD⟩ := continuous_flow_bounded hγ hθ D hD s
  obtain ⟨CJ, hCJ⟩ := continuous_flow_bounded hγ hθ J hJ s
  obtain ⟨CR, hCR⟩ := continuous_flow_bounded hγ hθ R hR s
  have hder (t : ℝ) : HasDerivAt (fun t => B (flow γ θ t s)) (D (flow γ θ t s)) t := by
    have hh := (((flow_hasDerivAt (θ := θ) hγ s t).1).sub_const w).norm_sq
    convert hh using 1
    simp only [D, inner_smul_right]
    ring
  have hh := holding_generator_bound (hB.comp hfc) (hD.comp hfc)
    (hJ.comp hfc) (hR.comp hfc) hder hCB hCD hCJ hCR
    (fun t _ => hgen (flow γ θ t s))
  have hInt := sample_flow_integrable hγ hθ H hH s (sampleLaw n)
  refine ⟨hInt, ?_⟩
  have he := sample_flow_integral hγ hθ H hH s
  change (∫ a, H a.2 (flow γ θ (max 0 a.1) s) ∂(sampleLaw n : Measure (ℝ × Fin n))) ≤ _
  rw [he]
  have hAc : Continuous (fun v : E × E => ‖v.2 - v.1‖ ^ 2) := by fun_prop
  have hKc : Continuous (fun v : E × E => ‖G v.1‖ ^ 2) := by fun_prop
  obtain ⟨CA, hCA⟩ := continuous_flow_bounded hγ hθ _ hAc s
  obtain ⟨CK, hCK⟩ := continuous_flow_bounded hγ hθ _ hKc s
  have hAi := weighted_integrable (hAc.comp hfc) hCA
  have hKi := weighted_integrable (hKc.comp hfc) hCK
  have hBi := weighted_integrable (hB.comp hfc) hCB
  have hlin : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * R (flow γ θ t s)) =
      (2 / m + η ^ 2 * δ ^ 2) * (∫ t in Ioi (0 : ℝ), Real.exp (-t) * B (flow γ θ t s)) +
      m * θ ^ 2 * (∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2) +
      (m + 1) * η ^ 2 * (∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖G (flow γ θ t s).1‖ ^ 2) := by
    have heq (t : ℝ) : Real.exp (-t) * R (flow γ θ t s) =
        (2 / m + η ^ 2 * δ ^ 2) * (Real.exp (-t) * B (flow γ θ t s)) +
        m * θ ^ 2 * (Real.exp (-t) * ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2) +
        (m + 1) * η ^ 2 * (Real.exp (-t) * ‖G (flow γ θ t s).1‖ ^ 2) := by dsimp [R]; ring
    simp_rw [heq]
    have hsum := integral_add ((hBi.const_mul (2 / m + η ^ 2 * δ ^ 2)).add
      (hAi.const_mul (m * θ ^ 2))) (hKi.const_mul ((m + 1) * η ^ 2))
    simp only [Pi.add_apply, Function.comp_apply] at hsum
    have hsum2 := integral_add (hBi.const_mul (2 / m + η ^ 2 * δ ^ 2)) (hAi.const_mul (m * θ ^ 2))
    simp only [Function.comp_apply] at hsum2
    rw [hsum, hsum2]
    simp only [integral_const_mul]
  simp only [Function.comp_apply] at hh
  rw [hlin] at hh
  have hzero : B (flow γ θ 0 s) = ‖s.1 - w‖ ^ 2 := by simp [B, flow, flowWeight]
  rw [hzero] at hh
  dsimp only [J, B, η] at hh
  linarith

end OracleTemplate.ContinuizedSimilarQuasar.Movement
