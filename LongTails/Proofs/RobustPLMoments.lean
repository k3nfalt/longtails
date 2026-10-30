import LongTails.Proofs.RobustCenteredClipping
import LongTails.Proofs.StochasticEnvelopeSampling

open MeasureTheory

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centeredClip_residual_moment {B p : ℝ} (hB : 0 < B) (hp : 1 ≤ p)
    {c u : E} (hc : ‖u - c‖ ≤ B / 2) (v : E) :
    ‖centeredClip B c v - v‖ ≤ ‖v - u‖ ^ p / (B / 2) ^ (p - 1) := by
  have h := clip_residual_le_moment hB hp hc (v - c)
  have he : centeredClip B c v - v = -(v - c - clip B (v - c)) := by
    unfold centeredClip
    abel
  rw [he, norm_neg]
  simpa only [show v - c - (u - c) = v - u by abel] using h

lemma centeredClip_second_moment_pointwise {B p : ℝ} (hB : 0 ≤ B)
    (hp0 : 0 ≤ p) (hp : p ≤ 2) {c u : E} (hc : ‖u - c‖ ≤ B / 2) (v : E) :
    ‖centeredClip B c v - u‖ ^ 2 ≤ (3 * B / 2) ^ (2 - p) * ‖v - u‖ ^ p := by
  have hb := centeredClip_error_bounded hB hc v
  have he := centeredClip_error hB (by linarith : ‖u - c‖ ≤ B) v
  exact (sq_le_rpow_mul (norm_nonneg _) hb hp).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) he hp0)
      (Real.rpow_nonneg (by positivity) _))

lemma centeredClip_fourth_moment_pointwise {B p : ℝ} (hB : 0 ≤ B)
    (hp0 : 0 ≤ p) (hp : p ≤ 2) {c u : E} (hc : ‖u - c‖ ≤ B / 2) (v : E) :
    ‖centeredClip B c v - u‖ ^ 4 ≤
      (3 * B / 2) ^ 2 * ((3 * B / 2) ^ (2 - p) * ‖v - u‖ ^ p) := by
  have hs := centeredClip_second_moment_pointwise hB hp0 hp hc v
  have hb := pow_le_pow_left₀ (norm_nonneg _) (centeredClip_error_bounded hB hc v) 2
  have hh := mul_le_mul hb hs (sq_nonneg _) (sq_nonneg _)
  simpa only [← pow_add, show (2 : ℕ) + 2 = 4 by rfl] using hh

lemma centeredClip_bad_error {B : ℝ} (hB : 0 ≤ B) {c u : E}
    (hc : B / 2 ≤ ‖c - u‖) (v : E) :
    ‖centeredClip B c v - u‖ ≤ 3 * ‖c - u‖ := by
  have he : centeredClip B c v - u = clip B (v - c) + (c - u) := by
    unfold centeredClip
    abel
  rw [he]
  have hb := norm_clip_le hB (v - c)
  have ht := norm_add_le (clip B (v - c)) (c - u)
  linarith

lemma centeredClip_bad_moments {B : ℝ} (hB : 0 < B) {c u : E}
    (hc : B / 2 ≤ ‖c - u‖) (v : E) :
    ‖centeredClip B c v - u‖ ≤ 24 * ‖c - u‖ ^ 4 / B ^ 3 ∧
    ‖centeredClip B c v - u‖ ^ 2 ≤ 36 * ‖c - u‖ ^ 4 / B ^ 2 ∧
    ‖centeredClip B c v - u‖ ^ 4 ≤ 81 * ‖c - u‖ ^ 4 := by
  have he := centeredClip_bad_error hB.le hc v
  have hR : 0 ≤ ‖c - u‖ := norm_nonneg _
  have hB2 : B ≤ 2 * ‖c - u‖ := by linarith
  have h2 := pow_le_pow_left₀ hB.le hB2 2
  have h3 := pow_le_pow_left₀ hB.le hB2 3
  have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
  have he4 := pow_le_pow_left₀ (norm_nonneg _) he 4
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < B ^ 3)).mpr
    calc
      _ ≤ (3 * ‖c - u‖) * B ^ 3 := mul_le_mul_of_nonneg_right he (by positivity)
      _ ≤ (3 * ‖c - u‖) * (2 * ‖c - u‖) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  · apply (le_div_iff₀ (by positivity : 0 < B ^ 2)).mpr
    calc
      _ ≤ (3 * ‖c - u‖) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right he2 (sq_nonneg _)
      _ ≤ (3 * ‖c - u‖) ^ 2 * (2 * ‖c - u‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  · nlinarith only [he4]

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma centeredClip_heavy_moments {X : Ω → E} (hX : Measurable X)
    (hi : Integrable X P) {u c : E} (hm : ∫ ω, X ω ∂P = u)
    {B p M : ℝ} (hB : 0 < B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : ‖u - c‖ ≤ B / 2) (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpm : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ M) :
    Integrable (fun ω => centeredClip B c (X ω)) P ∧
    Integrable (fun ω => ‖centeredClip B c (X ω) - u‖ ^ 2) P ∧
    Integrable (fun ω => ‖centeredClip B c (X ω) - u‖ ^ 4) P ∧
    (∫ ω, ‖centeredClip B c (X ω) - u‖ ^ 2 ∂P) ≤ (3 * B / 2) ^ (2 - p) * M ∧
    (∫ ω, ‖centeredClip B c (X ω) - u‖ ^ 4 ∂P) ≤
      (3 * B / 2) ^ 2 * ((3 * B / 2) ^ (2 - p) * M) ∧
    ‖(∫ ω, centeredClip B c (X ω) ∂P) - u‖ ≤ M / (B / 2) ^ (p - 1) := by
  have hY := (measurable_centeredClip B c).comp hX
  have hYi : Integrable (fun ω => centeredClip B c (X ω)) P :=
    (integrable_const c).add (integrable_clip (hX.sub_const c) hB.le)
  have h2 (ω : Ω) := centeredClip_second_moment_pointwise hB.le
    (by linarith : 0 ≤ p) hp2 hc (X ω)
  have h4 (ω : Ω) := centeredClip_fourth_moment_pointwise hB.le
    (by linarith : 0 ≤ p) hp2 hc (X ω)
  have h2i : Integrable (fun ω => ‖centeredClip B c (X ω) - u‖ ^ 2) P := by
    apply (hpi.const_mul ((3 * B / 2) ^ (2 - p))).mono'
      ((hY.sub_const u).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2 ω
  have h4i : Integrable (fun ω => ‖centeredClip B c (X ω) - u‖ ^ 4) P := by
    apply ((hpi.const_mul ((3 * B / 2) ^ (2 - p))).const_mul ((3 * B / 2) ^ 2)).mono'
      ((hY.sub_const u).norm.pow_const 4).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h4 ω
  refine ⟨hYi, h2i, h4i, ?_, ?_, ?_⟩
  · have hh := integral_mono h2i (hpi.const_mul _) h2
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpm (by positivity))
  · have hh := integral_mono h4i ((hpi.const_mul _).const_mul _) h4
    rw [integral_const_mul, integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpm (by positivity)) (sq_nonneg _))
  · have hh := norm_integral_le_of_norm_le (hpi.div_const ((B / 2) ^ (p - 1)))
      (f := fun ω => centeredClip B c (X ω) - X ω)
      (Filter.Eventually.of_forall fun ω => centeredClip_residual_moment hB hp hc (X ω))
    rw [integral_sub hYi hi, hm, integral_div] at hh
    exact hh.trans (div_le_div_of_nonneg_right hpm (by positivity))

end OracleTemplate.RobustGradient
