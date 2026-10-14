import LongTails.Algorithms.TerminalClipping
import LongTails.Proofs.TerminalClippingEnergy
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

variable {E : Type*} [NormedAddCommGroup E]

lemma threshold_pos {B G : ℝ} (hB : 0 < B) (hG : 0 < G)
    {T : ℕ} (hT : 0 < T) (x U : E) : 0 < threshold B G T x U := by
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hm : 0 < Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) := by positivity
  unfold threshold
  dsimp only
  split_ifs with hU
  · positivity
  · have hu : 0 < ‖U‖ := norm_pos_iff.mpr hU
    apply lt_min <;> positivity

lemma threshold_size {B G : ℝ} {T : ℕ} (x U : E) :
    threshold B G T x U ≤ Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) * Real.sqrt T := by
  unfold threshold
  dsimp only
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma threshold_square {B G : ℝ} (hB : 0 < B) (hG : 0 < G)
    {T : ℕ} (hT : 0 < T) (x U : E) :
    (threshold B G T x U) ^ 2 ≤ (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) * T := by
  have h := pow_le_pow_left₀ (threshold_pos hB hG hT x U).le (threshold_size x U) 2
  simpa only [mul_pow, Real.sq_sqrt (show 0 ≤ B ^ 2 * ‖x‖ ^ 2 + G ^ 2 by positivity),
    Real.sq_sqrt (show 0 ≤ (T : ℝ) by positivity)] using h

lemma threshold_influence {B G : ℝ} (hB : 0 < B) {T : ℕ} (hT : 0 < T)
    (x U : E) :
    threshold B G T x U * ‖U‖ ≤ (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) / (B * Real.sqrt T) := by
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  unfold threshold
  dsimp only
  split_ifs with hU
  · simp only [hU, norm_zero, mul_zero]
    positivity
  · have hu : 0 < ‖U‖ := norm_pos_iff.mpr hU
    have hm : 0 ≤ B ^ 2 * ‖x‖ ^ 2 + G ^ 2 := by positivity
    rw [Real.sq_sqrt hm]
    calc
      _ ≤ ((B ^ 2 * ‖x‖ ^ 2 + G ^ 2) / (B * Real.sqrt T * ‖U‖)) * ‖U‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hu.le
      _ = _ := by field_simp

lemma threshold_bias_scale {B G : ℝ} (hB : 0 < B) (hG : 0 < G)
    {T : ℕ} (hT : 0 < T) (x U : E) :
    (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) / threshold B G T x U ≤
      Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) / Real.sqrt T +
        B * Real.sqrt T * ‖U‖ := by
  classical
  let M := Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2)
  have hm : 0 < M := by dsimp [M]; positivity
  have hm2 : M ^ 2 = B ^ 2 * ‖x‖ ^ 2 + G ^ 2 := Real.sq_sqrt (by positivity)
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have he : M ^ 2 / (M * Real.sqrt T) = M / Real.sqrt T := by field_simp
  unfold threshold
  dsimp only
  change _ / (if U = 0 then M * Real.sqrt T else
    min (M * Real.sqrt T) (M ^ 2 / (B * Real.sqrt T * ‖U‖))) ≤ _
  rw [← hm2, Real.sqrt_sq hm.le]
  split_ifs with hU
  · rw [he, hU, norm_zero, mul_zero, add_zero]
  · rw [min_def]
    split_ifs
    · rw [he]
      have hnon : 0 ≤ B * Real.sqrt T * ‖U‖ := by positivity
      linarith
    · have hu : 0 < ‖U‖ := norm_pos_iff.mpr hU
      have he' : M ^ 2 / (M ^ 2 / (B * Real.sqrt T * ‖U‖)) =
          B * Real.sqrt T * ‖U‖ := by field_simp
      rw [he']
      have hnon : 0 ≤ M / Real.sqrt T := by positivity
      linarith

lemma threshold_measurable [MeasurableSpace E] [BorelSpace E]
    (B G : ℝ) (T : ℕ) : Measurable (fun z : E × E => threshold B G T z.1 z.2) := by
  classical
  unfold threshold
  dsimp only
  apply Measurable.ite
  · exact (measurableSet_singleton (0 : E)).preimage measurable_snd
  · fun_prop
  · fun_prop

variable [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

lemma measurable_variable_clip {Ω : Type*} [MeasurableSpace Ω]
    {C : Ω → ℝ} {g : Ω → E} (hC : Measurable C) (hg : Measurable g) :
    Measurable (fun ω => clip (C ω) (g ω)) := by
  unfold clip
  exact Measurable.ite (measurableSet_le hg.norm hC) hg ((hC.div hg.norm).smul hg)

lemma threshold_oracle_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hgi : Integrable g P)
    (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {B G : ℝ} (hB : 0 < B) (hG : 0 < G) {T : ℕ} (hT : 0 < T)
    (x U : E) (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ B ^ 2 * ‖x‖ ^ 2 + G ^ 2) :
    ‖(∫ ω, g ω ∂P) - (∫ ω, clip (threshold B G T x U) (g ω) ∂P)‖ ≤
      Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) / Real.sqrt T +
        B * Real.sqrt T * ‖U‖ :=
  (full_moment_clip_bias hg hgi hmi (threshold_pos hB hG hT x U) hm).trans
    (threshold_bias_scale hB hG hT x U)

lemma clipped_mean_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {C : S → ℝ} {g : S → Ω → E}
    (hC : Measurable C) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun s => ∫ ω, clip (C s) (g s ω) ∂P) := by
  have hh : Measurable (Function.uncurry (fun s ω => clip (C s) (g s ω))) :=
    measurable_variable_clip (hC.comp measurable_fst) hg
  exact hh.stronglyMeasurable.integral_prod_right.measurable

end OracleTemplate.TerminalClipping
