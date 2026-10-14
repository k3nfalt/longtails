import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.RobustPilotConfidence

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def guardedError (B : ℝ) (u c v : E) : E := by
  classical
  exact if ‖u-c‖ ≤ B/2 then centeredClip B c v-u else 0

lemma guardedError_eq {B : ℝ} {u c v : E} (h : ‖u-c‖ ≤ B/2) :
    guardedError B u c v = centeredClip B c v-u := by simp [guardedError, h]

lemma guardedError_bound {B : ℝ} (hB : 0 ≤ B) (u c v : E) :
    ‖guardedError B u c v‖ ≤ 3*B/2 := by
  classical
  by_cases h : ‖u-c‖ ≤ B/2
  · rw [guardedError_eq h]
    exact centeredClip_error_bounded hB h v
  · simp only [guardedError, h, ↓reduceIte, norm_zero]
    positivity

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_centeredClip_joint :
    Measurable (fun w : ℝ × E × E => centeredClip w.1 w.2.1 w.2.2) := by
  unfold centeredClip clip
  apply measurable_snd.fst.add
  apply Measurable.ite
  · exact measurableSet_le (measurable_snd.snd.sub measurable_snd.fst).norm measurable_fst
  · exact measurable_snd.snd.sub measurable_snd.fst
  · exact (measurable_fst.div (measurable_snd.snd.sub measurable_snd.fst).norm).smul
      (measurable_snd.snd.sub measurable_snd.fst)

lemma measurable_guardedError :
    Measurable (fun w : ℝ × E × E × E => guardedError w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  unfold guardedError
  apply Measurable.ite
  · exact measurableSet_le (measurable_snd.fst.sub measurable_snd.snd.fst).norm
      (measurable_fst.div_const 2)
  · exact (measurable_centeredClip_joint.comp
      (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd))).sub
      measurable_snd.fst
  · exact measurable_const

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [CompleteSpace E]

lemma guardedError_moments {V : Ω → E} (hV : Measurable V) (hVi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B v : ℝ} (hB : 0 < B)
    (hmi : Integrable (fun ω => ‖V ω-u‖^2) P)
    (hm : (∫ ω, ‖V ω-u‖^2 ∂P) ≤ v) (c : E) :
    Integrable (fun ω => guardedError B u c (V ω)) P ∧
    Integrable (fun ω => ‖guardedError B u c (V ω)‖^2) P ∧
    (∫ ω, ‖guardedError B u c (V ω)‖^2 ∂P) ≤ v ∧
    ‖∫ ω, guardedError B u c (V ω) ∂P‖ ≤ 2*v/B := by
  classical
  by_cases hc : ‖u-c‖ ≤ B/2
  · simp only [guardedError, hc, ↓reduceIte]
    have h := centeredClip_moments hV hVi hmean hB hc hmi hm
    refine ⟨h.1.sub (integrable_const u), h.2.1, h.2.2.1, ?_⟩
    rw [integral_sub h.1 (integrable_const u)]
    simpa using h.2.2.2
  · have hv : 0 ≤ v := (integral_nonneg (fun _ => sq_nonneg _)).trans hm
    simp only [guardedError, hc, ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero, norm_zero]
    exact ⟨integrable_const 0, integrable_const 0, hv, by positivity⟩

lemma guardedError_mgf {V : Ω → E} (hV : Measurable V) (hVi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B v : ℝ} (hB : 0 < B)
    (hmi : Integrable (fun ω => ‖V ω-u‖^2) P)
    (hm : (∫ ω, ‖V ω-u‖^2 ∂P) ≤ v) (center z : E)
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hc : 0 ≤ c)
    (ht : 0 ≤ t) (hsmall : t*(a*(3*B/2)*‖z‖+c*a^2*(3*B/2)^2) ≤ 1) :
    Integrable (fun ω => Real.exp (t*(-b*⟪z, guardedError B u center (V ω)⟫+
      c*a^2*‖guardedError B u center (V ω)‖^2))) P ∧
    (∫ ω, Real.exp (t*(-b*⟪z, guardedError B u center (V ω)⟫+
      c*a^2*‖guardedError B u center (V ω)‖^2)) ∂P) ≤
      Real.exp (t*(a*‖z‖*(2*v/B)+c*a^2*v)+
        2*t^2*(a^2*‖z‖^2+c^2*a^4*(3*B/2)^2)*v) := by
  have h := guardedError_moments hV hVi hmean hB hmi hm center
  exact energy_increment_mgf
    (measurable_guardedError.comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk hV))))
    h.1 h.2.1 ha hb hba hc ht z
    (fun ω => guardedError_bound hB.le u center (V ω)) h.2.2.2 h.2.2.1 hsmall

lemma pilot_means_failure_probability {V : Ω → E} (hV : Measurable V)
    (hVi : Integrable V P) (u : E) (hmean : ∫ ω, V ω ∂P = u)
    (hV2i : Integrable (fun ω => ‖V ω-u‖^2) P) {σ B : ℝ}
    (hvar : (∫ ω, ‖V ω-u‖^2 ∂P) ≤ σ^2) (hB : 0 < B)
    (k r : ℕ) (hr : 0 < r) (hsize : (σ^2/(r : ℝ))/(B/6)^2 ≤ 1/16) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => P)
      {ξ | B/2 < ‖pilotCenter B (fun i => (1/(r : ℝ)) • ∑ j, V (ξ i j))-u‖} ≤
      ENNReal.ofReal ((1/2 : ℝ)^k) := by
  have h := finite_mean_variance hV hVi u hV2i hmean r hr
  apply pilotCenter_failure_probability (P := Measure.pi fun _ : Fin r => P)
    (V := fun ξ : Fin r → Ω => (1/(r : ℝ)) • ∑ j, V (ξ j)) (by fun_prop) u B ?_ k
  apply (norm_tail_le_second_moment h.1 (by positivity) ?_).trans hsize
  rw [h.2]
  exact div_le_div_of_nonneg_right hvar (by positivity)

lemma random_center_moments {Ξ : Type*} [MeasurableSpace Ξ] {Q : Measure Ξ}
    [IsProbabilityMeasure Q] {C : Ω → E} {V : Ξ → E}
    (hC : Measurable C) (hV : Measurable V) (hVi : Integrable V Q)
    {u : E} (hmean : ∫ ξ, V ξ ∂Q = u) {B v : ℝ} (hB : 0 < B)
    (hmi : Integrable (fun ξ => ‖V ξ-u‖^2) Q)
    (hm : (∫ ξ, ‖V ξ-u‖^2 ∂Q) ≤ v) :
    Integrable (fun w : Ω × Ξ => guardedError B u (C w.1) (V w.2)) (P.prod Q) ∧
    Integrable (fun w : Ω × Ξ => ‖guardedError B u (C w.1) (V w.2)‖^2) (P.prod Q) ∧
    (∫ w : Ω × Ξ, ‖guardedError B u (C w.1) (V w.2)‖^2 ∂P.prod Q) ≤ v ∧
    ‖∫ w : Ω × Ξ, guardedError B u (C w.1) (V w.2) ∂P.prod Q‖ ≤ 2*v/B := by
  let Y : Ω × Ξ → E := fun w => guardedError B u (C w.1) (V w.2)
  have hY : Measurable Y := measurable_guardedError.comp
    (measurable_const.prodMk (measurable_const.prodMk
      ((hC.comp measurable_fst).prodMk (hV.comp measurable_snd))))
  have hbound (w : Ω × Ξ) : ‖Y w‖ ≤ 3*B/2 := guardedError_bound hB.le u _ _
  have hYi : Integrable Y (P.prod Q) := Integrable.of_bound hY.aestronglyMeasurable
    (3*B/2) (Filter.Eventually.of_forall hbound)
  have hY2i : Integrable (fun w => ‖Y w‖^2) (P.prod Q) := by
    apply Integrable.of_bound (hY.norm.pow_const 2).aestronglyMeasurable ((3*B/2)^2)
    exact Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound w) 2)
  have hcond (ω : Ω) := guardedError_moments hV hVi hmean hB hmi hm (C ω)
  refine ⟨hYi, hY2i, ?_, ?_⟩
  · change (∫ w, ‖Y w‖^2 ∂P.prod Q) ≤ v
    rw [integral_prod _ hY2i]
    have h := integral_mono hY2i.integral_prod_left (integrable_const v)
      (fun ω => (hcond ω).2.2.1)
    simpa using h
  · change ‖∫ w, Y w ∂P.prod Q‖ ≤ 2*v/B
    rw [integral_prod _ hYi]
    have h := norm_integral_le_of_norm_le (integrable_const (2*v/B) :
      Integrable (fun _ : Ω => 2*v/B) P)
      (f := fun ω => ∫ ξ, Y (ω, ξ) ∂Q)
      (Filter.Eventually.of_forall (fun ω => (hcond ω).2.2.2))
    simpa using h

end OracleTemplate.RobustGradient
