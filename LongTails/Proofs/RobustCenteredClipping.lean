import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Proofs.HeavyTailedClipping

open MeasureTheory

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centeredClip_error {B : ℝ} (hB : 0 ≤ B) {c u : E}
    (hc : ‖u - c‖ ≤ B) (v : E) :
    ‖centeredClip B c v - u‖ ≤ ‖v - u‖ := by
  have h := norm_clip_sub_le hB hc (v - c)
  simpa only [centeredClip, show c + clip B (v - c) - u =
    clip B (v - c) - (u - c) by abel,
    show v - c - (u - c) = v - u by abel] using h

lemma centeredClip_error_bounded {B : ℝ} (hB : 0 ≤ B) {c u : E}
    (hc : ‖u - c‖ ≤ B / 2) (v : E) :
    ‖centeredClip B c v - u‖ ≤ 3 * B / 2 := by
  have he : centeredClip B c v - u = clip B (v - c) + (c - u) := by
    unfold centeredClip
    abel
  rw [he]
  have h := norm_clip_le hB (v - c)
  have hn := norm_add_le (clip B (v - c)) (c - u)
  rw [norm_sub_rev c u] at hn
  linarith

lemma centeredClip_residual {B : ℝ} (hB : 0 < B) {c u : E}
    (hc : ‖u - c‖ ≤ B / 2) (v : E) :
    ‖centeredClip B c v - v‖ ≤ 2 * ‖v - u‖ ^ 2 / B := by
  have h := clip_residual_le_moment hB (by norm_num : (1 : ℝ) ≤ 2) hc (v - c)
  have he : centeredClip B c v - v = -(v - c - clip B (v - c)) := by
    unfold centeredClip
    abel
  rw [he, norm_neg]
  have h' : ‖v - c - clip B (v - c)‖ ≤ ‖v-u‖^2 / (B/2) := by
    simpa only [show v - c - (u - c) = v - u by abel, Real.rpow_two,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using h
  exact h'.trans_eq (by ring)

variable {Ω : Type*} [MeasurableSpace Ω] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma measurable_centeredClip (B : ℝ) (c : E) : Measurable (centeredClip B c) :=
  measurable_const.add ((measurable_clip B).comp (measurable_id.sub_const c))

omit [CompleteSpace E] in
lemma centeredClip_moments {V : Ω → E} (hV : Measurable V) (hVi : Integrable V P)
    {u c : E} (hmean : ∫ ω, V ω ∂P = u) {B v : ℝ} (hB : 0 < B)
    (hc : ‖u - c‖ ≤ B / 2) (hmi : Integrable (fun ω => ‖V ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => centeredClip B c (V ω)) P ∧
    Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) P ∧
    (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂P) ≤ v ∧
    ‖(∫ ω, centeredClip B c (V ω) ∂P) - u‖ ≤ 2 * v / B := by
  have hY := (measurable_centeredClip B c).comp hV
  have hYi : Integrable (fun ω => centeredClip B c (V ω)) P :=
    (integrable_const c).add (integrable_clip (hV.sub_const c) hB.le)
  have hpoint (ω : Ω) : ‖centeredClip B c (V ω) - u‖ ^ 2 ≤ ‖V ω - u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (centeredClip_error hB.le (by linarith) _) 2
  have hYi2 : Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) P := by
    apply hmi.mono' ((hY.sub_const u).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω)
  refine ⟨hYi, hYi2, (integral_mono hYi2 hmi hpoint).trans hm, ?_⟩
  have hb := norm_integral_le_of_norm_le ((hmi.const_mul 2).div_const B)
    (f := fun ω => centeredClip B c (V ω) - V ω)
    (Filter.Eventually.of_forall (fun ω => centeredClip_residual hB hc (V ω)))
  rw [integral_sub hYi hVi, hmean, integral_div, integral_const_mul] at hb
  exact hb.trans (div_le_div_of_nonneg_right (by linarith) hB.le)

end OracleTemplate.RobustGradient
