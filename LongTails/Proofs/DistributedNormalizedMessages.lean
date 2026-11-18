import LongTails.Proofs.Clipping
import LongTails.Proofs.AdaptiveReplicaMoments
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedMessages

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clip_margin_residual {G a : ℝ} (hG : 0 ≤ G) (ha : 0 < a)
    {g : E} (hg : ‖g‖ ≤ G) (y : E) :
    ‖y - OracleTemplate.clip (G + a) y‖ ≤ ‖y - g‖ ^ 2 / (4 * a) := by
  rw [OracleTemplate.clip_residual_norm (by positivity)]
  apply max_le
  · positivity
  · apply (le_div_iff₀ (by positivity : 0 < 4 * a)).mpr
    have ht : ‖y‖ ≤ ‖y - g‖ + G := by
      have := norm_add_le (y - g) g
      rw [sub_add_cancel] at this
      linarith
    nlinarith [sq_nonneg (‖y - g‖ - 2 * a)]

lemma clipped_batch_bias [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G a : ℝ} (hG : 0 ≤ G) (ha : 0 < a) {g : E} (hg : ‖g‖ ≤ G)
    {Y : Ω → E} (hYm : AEStronglyMeasurable Y P) (hYi : Integrable Y P)
    (hY2 : Integrable (fun ω => ‖Y ω - g‖ ^ 2) P)
    (hmean : ∫ ω, Y ω ∂P = g) :
    ‖(∫ ω, OracleTemplate.clip (G + a) (Y ω) ∂P) - g‖ ≤
      (∫ ω, ‖Y ω - g‖ ^ 2 ∂P) / (4 * a) := by
  have hCm : AEStronglyMeasurable (fun ω => OracleTemplate.clip (G + a) (Y ω)) P :=
    ((OracleTemplate.measurable_clip (G + a)).comp_aemeasurable hYm.aemeasurable).aestronglyMeasurable
  have hCi : Integrable (fun ω => OracleTemplate.clip (G + a) (Y ω)) P := by
    apply (integrable_const (G + a) : Integrable (fun _ : Ω => G + a) P).mono' hCm
    exact Filter.Eventually.of_forall (fun ω => OracleTemplate.norm_clip_le (by positivity) (Y ω))
  have hDi : Integrable (fun ω => Y ω - OracleTemplate.clip (G + a) (Y ω)) P :=
    hYi.sub hCi
  have hres := integral_mono hDi.norm (hY2.div_const (4 * a))
    (fun ω => clip_margin_residual hG ha hg (Y ω))
  rw [integral_div] at hres
  have hn := norm_integral_le_integral_norm (μ := P) (fun ω => Y ω - OracleTemplate.clip (G + a) (Y ω))
  rw [integral_sub hYi hCi, hmean, norm_sub_rev] at hn
  exact hn.trans hres

lemma clipped_batch_second_moment [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ} (hB : 0 ≤ B) {g : E} (hg : ‖g‖ ≤ B) {Y : Ω → E}
    (hYm : AEStronglyMeasurable Y P)
    (hY2 : Integrable (fun ω => ‖Y ω - g‖ ^ 2) P) :
    Integrable (fun ω => ‖OracleTemplate.clip B (Y ω) - g‖ ^ 2) P ∧
      (∫ ω, ‖OracleTemplate.clip B (Y ω) - g‖ ^ 2 ∂P) ≤
        ∫ ω, ‖Y ω - g‖ ^ 2 ∂P := by
  have hCm : AEStronglyMeasurable (fun ω => OracleTemplate.clip B (Y ω)) P :=
    ((OracleTemplate.measurable_clip B).comp_aemeasurable hYm.aemeasurable).aestronglyMeasurable
  have hb (ω : Ω) : ‖OracleTemplate.clip B (Y ω) - g‖ ^ 2 ≤ ‖Y ω - g‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (OracleTemplate.norm_clip_sub_le hB hg (Y ω))
  have hi : Integrable (fun ω => ‖OracleTemplate.clip B (Y ω) - g‖ ^ 2) P := by
    apply hY2.mono' ((hCm.sub aestronglyMeasurable_const).norm.pow 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb ω
  exact ⟨hi, integral_mono hi hY2 hb⟩

lemma clipped_batch_norm_second_moment [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ} (hB : 0 ≤ B) {g : E} {Y : Ω → E}
    (hYm : AEStronglyMeasurable Y P) (hYi : Integrable Y P)
    (hY2 : Integrable (fun ω => ‖Y ω - g‖ ^ 2) P) (hmean : (∫ ω, Y ω ∂P) = g) :
    Integrable (fun ω => ‖OracleTemplate.clip B (Y ω)‖ ^ 2) P ∧
      (∫ ω, ‖OracleTemplate.clip B (Y ω)‖ ^ 2 ∂P) ≤
        ‖g‖ ^ 2 + ∫ ω, ‖Y ω - g‖ ^ 2 ∂P := by
  have hzi : Integrable (fun ω => Y ω - g) P := hYi.sub (integrable_const g)
  have hzm : (∫ ω, Y ω - g ∂P) = 0 := by
    rw [integral_sub hYi (integrable_const g), hmean]
    simp
  have hi := AdaptiveReplicaMoments.shifted_second_moment_integrable g hzi hY2
  have hm := AdaptiveReplicaMoments.shifted_second_moment g hzi hY2 hzm
  have he (ω : Ω) : g + (Y ω - g) = Y ω := by abel
  simp_rw [he] at hi hm
  have hCm : AEStronglyMeasurable (fun ω => OracleTemplate.clip B (Y ω)) P :=
    ((OracleTemplate.measurable_clip B).comp_aemeasurable hYm.aemeasurable).aestronglyMeasurable
  have hb (ω : Ω) : ‖OracleTemplate.clip B (Y ω)‖ ^ 2 ≤ ‖Y ω‖ ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    simpa using OracleTemplate.norm_clip_sub_le hB (u := (0 : E)) (by simpa using hB) (Y ω)
  have hCi : Integrable (fun ω => ‖OracleTemplate.clip B (Y ω)‖ ^ 2) P := by
    apply hi.mono' (hCm.norm.pow 2)
    filter_upwards [] with ω
    change ‖‖OracleTemplate.clip B (Y ω)‖ ^ 2‖ ≤ ‖Y ω‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb ω
  exact ⟨hCi, (integral_mono hCi hi hb).trans_eq hm⟩

lemma unbiased_compression_shift [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (c g : E) {C : Ω → E} {v : ℝ}
    (hCi : Integrable C P) (hC2 : Integrable (fun ω => ‖C ω - c‖ ^ 2) P)
    (hmean : (∫ ω, C ω ∂P) = c) (hvar : (∫ ω, ‖C ω - c‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖C ω - g‖ ^ 2) P ∧
      (∫ ω, ‖C ω - g‖ ^ 2 ∂P) ≤ ‖c - g‖ ^ 2 + v := by
  have hzi : Integrable (fun ω => C ω - c) P := hCi.sub (integrable_const c)
  have hzm : (∫ ω, C ω - c ∂P) = 0 := by
    rw [integral_sub hCi (integrable_const c), hmean]
    simp
  have hi := AdaptiveReplicaMoments.shifted_second_moment_integrable (c - g) hzi hC2
  have hm := AdaptiveReplicaMoments.shifted_second_moment (c - g) hzi hC2 hzm
  have he (ω : Ω) : (c - g) + (C ω - c) = C ω - g := by abel
  simp_rw [he] at hi hm
  exact ⟨hi, hm.trans_le (add_le_add le_rfl hvar)⟩

end LongTails.Proofs.DistributedNormalizedMessages
