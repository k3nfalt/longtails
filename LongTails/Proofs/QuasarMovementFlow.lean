import LongTails.Proofs.ContinuizedQuasarStep
import LongTails.Proofs.QuasarMovementRecursion

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

lemma holding_generator_bound {B D J R : ℝ → ℝ} {CB CD CJ CR : ℝ}
    (hB : Continuous B) (hD : Continuous D) (hJ : Continuous J) (hR : Continuous R)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ) (hr : ∀ t, 0 ≤ t → ‖R t‖ ≤ CR)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ R t) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * J t) ≤
      B 0 + ∫ t in Ioi (0 : ℝ), Real.exp (-t) * R t := by
  have hBi := weighted_integrable hB hb
  have hDi := weighted_integrable hD hd
  have hJi := weighted_integrable hJ hj
  have hRi := weighted_integrable hR hr
  have he := weighted_derivative_integral hB hD hderiv hb hd
  have hh := integral_mono_ae ((hDi.add hJi).sub hBi) hRi (show
      (fun t => Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t)
        ≤ᵐ[volume.restrict (Ioi 0)] (fun t => Real.exp (-t) * R t) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := mul_le_mul_of_nonneg_left (hgen t ht.le) (Real.exp_pos (-t)).le
    nlinarith)
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  have hs := integral_sub (hDi.add hJi) hBi
  simp only [Pi.add_apply] at hs
  rw [hs, integral_add hDi hJi] at hh
  linarith

lemma weighted_resolvent {B D J N T : ℝ → ℝ} {CB CD CJ CN CT c : ℝ}
    (hc : 0 ≤ c)
    (hB : Continuous B) (hD : Continuous D) (hJ : Continuous J)
    (hN : Continuous N) (hT : Continuous T)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ) (hn : ∀ t, 0 ≤ t → ‖N t‖ ≤ CN)
    (ht : ∀ t, 0 ≤ t → ‖T t‖ ≤ CT)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ -c * B t - T t + N t)
    (hjump : ∀ t, 0 ≤ t → J t ≤ 4 * B t + N t) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * J t) ≤
      4 / (4 + c) * B 0 -
        4 / (4 + c) * (∫ t in Ioi (0 : ℝ), Real.exp (-t) * T t) +
        ∫ t in Ioi (0 : ℝ), Real.exp (-t) * N t := by
  have hBi := weighted_integrable hB hb
  have hDi := weighted_integrable hD hd
  have hJi := weighted_integrable hJ hj
  have hNi := weighted_integrable hN hn
  have hTi := weighted_integrable hT ht
  have he := weighted_derivative_integral hB hD hderiv hb hd
  have hg := integral_mono_ae ((hDi.add hJi).sub hBi)
    (((hBi.const_mul (-c)).sub hTi).add hNi) (show
      (fun t => Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t)
        ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t => -c * (Real.exp (-t) * B t) - Real.exp (-t) * T t +
        Real.exp (-t) * N t) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := mul_le_mul_of_nonneg_left (hgen t ht.le) (Real.exp_pos (-t)).le
    nlinarith)
  simp only [Pi.sub_apply, Pi.add_apply] at hg
  have hs := integral_sub (hDi.add hJi) hBi
  have hs2 := integral_add ((hBi.const_mul (-c)).sub hTi) hNi
  simp only [Pi.add_apply] at hs
  simp only [Pi.sub_apply] at hs2
  rw [hs, integral_add hDi hJi, hs2,
    integral_sub (hBi.const_mul (-c)) hTi, integral_const_mul] at hg
  have hjj := integral_mono_ae hJi ((hBi.const_mul 4).add hNi) (show
      (fun t => Real.exp (-t) * J t) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t => 4 * (Real.exp (-t) * B t) + Real.exp (-t) * N t) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := mul_le_mul_of_nonneg_left (hjump t ht.le) (Real.exp_pos (-t)).le
    nlinarith)
  simp only [Pi.add_apply] at hjj
  rw [integral_add (hBi.const_mul 4) hNi, integral_const_mul] at hjj
  exact resolvent_slack hc (by linarith) hjj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma sample_flow_integral {n : ℕ} [NeZero n] {γ θ : ℝ}
    (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (H : Fin n → E × E → ℝ)
    (hH : ∀ i, Continuous (H i)) (s : E × E) :
    (∫ q, H q.2 (flow γ θ (max 0 q.1) s) ∂(sampleLaw n : Measure (ℝ × Fin n))) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (𝔼 i, H i (flow γ θ t s)) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hInt := sample_flow_integrable hγ hθ H hH s (sampleLaw n)
  change (∫ q, H q.2 (flow γ θ (max 0 q.1) s)
    ∂(expMeasure 1).prod (PMF.uniformOfFintype (Fin n)).toMeasure) = _
  rw [integral_prod _ hInt]
  simp_rw [FiniteSum.uniform_integral]
  rw [integral_expMeasure_one]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  simp only [max_eq_right ht.le]

omit [CompleteSpace E] in
lemma inner_movement_bound (h d : E) (θ : ℝ) :
    2 * θ * ⟪h, d⟫ ≤ ‖h‖ ^ 2 / 2 + 2 * θ ^ 2 * ‖d‖ ^ 2 := by
  have hh := sq_nonneg ‖h - (2 * θ) • d‖
  rw [norm_sub_sq_real] at hh
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
  nlinarith

omit [CompleteSpace E] in
lemma flow_anchor_moment {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (s : E × E) (w : E) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow γ θ t s).1 - w‖ ^ 2) ≤
      2 * ‖s.1 - w‖ ^ 2 + 4 * θ ^ 2 *
        (∫ t in Ioi (0 : ℝ), Real.exp (-t) *
          ‖(flow γ θ t s).2 - (flow γ θ t s).1‖ ^ 2) := by
  let H := fun v : E × E => ‖v.1 - w‖ ^ 2
  let D := fun v : E × E => ‖v.2 - v.1‖ ^ 2
  let H' := fun v : E × E => 2 * θ * ⟪v.1 - w, v.2 - v.1⟫
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hH' : Continuous H' := by dsimp [H']; fun_prop
  have hfc : Continuous (fun t => flow γ θ t s) :=
    (flow_continuous γ θ).comp (continuous_id.prodMk continuous_const)
  obtain ⟨CH, hbH⟩ := continuous_flow_bounded hγ hθ H hH s
  obtain ⟨CD, hbD⟩ := continuous_flow_bounded hγ hθ D hD s
  obtain ⟨CH', hbH'⟩ := continuous_flow_bounded hγ hθ H' hH' s
  have hiH := weighted_integrable (hH.comp hfc) hbH
  have hiD := weighted_integrable (hD.comp hfc) hbD
  have hiH' := weighted_integrable (hH'.comp hfc) hbH'
  have hder (t : ℝ) : HasDerivAt (fun t => H (flow γ θ t s))
      (H' (flow γ θ t s)) t := by
    have hh := (((flow_hasDerivAt (θ := θ) hγ s t).1).sub_const w).norm_sq
    convert hh using 1
    simp only [H', inner_smul_right]
    ring
  have he := weighted_derivative_integral (hH.comp hfc) (hH'.comp hfc)
    hder hbH hbH'
  have hi := integral_mono_ae hiH' ((hiH.const_mul (1 / 2 : ℝ)).add
    (hiD.const_mul (2 * θ ^ 2))) (show
      (fun t => Real.exp (-t) * H' (flow γ θ t s)) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t => (1 / 2 : ℝ) * (Real.exp (-t) * H (flow γ θ t s)) +
        (2 * θ ^ 2) * (Real.exp (-t) * D (flow γ θ t s))) from by
      apply Filter.Eventually.of_forall
      intro t
      have hh := mul_le_mul_of_nonneg_left
        (inner_movement_bound ((flow γ θ t s).1 - w)
          ((flow γ θ t s).2 - (flow γ θ t s).1) θ) (Real.exp_pos (-t)).le
      dsimp only [H, H', D]
      nlinarith)
  simp only [Pi.add_apply] at hi
  rw [integral_add (hiH.const_mul (1 / 2 : ℝ)) (hiD.const_mul (2 * θ ^ 2)),
    integral_const_mul, integral_const_mul] at hi
  have hzero : H (flow γ θ 0 s) = ‖s.1 - w‖ ^ 2 := by
    simp [H, flow, flowWeight]
  simp only [Function.comp_apply] at he hi
  rw [hzero] at he
  change (∫ t in Ioi (0 : ℝ), Real.exp (-t) * H (flow γ θ t s)) ≤
    2 * ‖s.1 - w‖ ^ 2 + 4 * θ ^ 2 *
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * D (flow γ θ t s))
  linarith

end OracleTemplate.ContinuizedSimilarQuasar.Movement
