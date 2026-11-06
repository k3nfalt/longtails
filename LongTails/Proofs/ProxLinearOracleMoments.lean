import LongTails.Proofs.NormalizedStormOrthogonality
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.ProxLinearEnvelope

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ProxLinearOracleMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma centered_second_moment {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) μ) (a : E)
    (hmean : ∫ ω, X ω ∂μ = a) :
    Integrable (fun ω => ‖X ω - a‖ ^ 2) μ ∧
      (∫ ω, ‖X ω - a‖ ^ 2 ∂μ) = (∫ ω, ‖X ω‖ ^ 2 ∂μ) - ‖a‖ ^ 2 := by
  have hinner : Integrable (fun ω => ⟪X ω, a⟫) μ := hX.inner_const a
  have hexp (ω : Ω) : ‖X ω - a‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪X ω, a⟫ + ‖a‖ ^ 2 :=
    norm_sub_sq_real _ _
  have hi : Integrable (fun ω => ‖X ω - a‖ ^ 2) μ := by
    simp_rw [hexp]
    exact (hX2.sub (hinner.const_mul 2)).add (integrable_const _)
  refine ⟨hi, ?_⟩
  simp_rw [hexp]
  rw [integral_add (f := fun ω => ‖X ω‖ ^ 2 - 2 * ⟪X ω, a⟫)
    (g := fun _ => ‖a‖ ^ 2) (hX2.sub (hinner.const_mul 2)) (integrable_const _),
    integral_sub (f := fun ω => ‖X ω‖ ^ 2) (g := fun ω => 2 * ⟪X ω, a⟫)
      hX2 (hinner.const_mul 2), integral_const_mul]
  have hin : (∫ ω, ⟪X ω, a⟫ ∂μ) = ‖a‖ ^ 2 := by
    calc
      _ = ∫ ω, ⟪a, X ω⟫ ∂μ := integral_congr_ae
        (Filter.Eventually.of_forall fun ω => (real_inner_comm (X ω) a).symm)
      _ = _ := by rw [integral_inner hX, hmean, real_inner_self_eq_norm_sq]
  rw [hin, integral_const]
  simp only [probReal_univ, one_smul]
  ring

lemma centered_second_moment_le {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) μ) (a : E)
    (hmean : ∫ ω, X ω ∂μ = a) :
    (∫ ω, ‖X ω - a‖ ^ 2 ∂μ) ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  rw [(centered_second_moment hX hX2 a hmean).2]
  exact sub_le_self _ (sq_nonneg _)

lemma recursive_noise_moment {X Y : Ω → E} (hX : Integrable X μ) (hY : Integrable Y μ)
    (a b : E) (hXa : ∫ ω, X ω ∂μ = a) (hYb : ∫ ω, Y ω ∂μ = b)
    (hA2 : Integrable (fun ω => ‖X ω - a‖ ^ 2) μ)
    (hD2 : Integrable (fun ω => ‖X ω - Y ω‖ ^ 2) μ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Integrable (fun ω => X ω - a - (1 - β) • (Y ω - b)) μ ∧
    (∫ ω, X ω - a - (1 - β) • (Y ω - b) ∂μ) = 0 ∧
    Integrable (fun ω => ‖X ω - a - (1 - β) • (Y ω - b)‖ ^ 2) μ ∧
    (∫ ω, ‖X ω - a - (1 - β) • (Y ω - b)‖ ^ 2 ∂μ) ≤
      2 * β ^ 2 * (∫ ω, ‖X ω - a‖ ^ 2 ∂μ) +
      2 * (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ) := by
  let A : Ω → E := fun ω => X ω - a
  let B : Ω → E := fun ω => X ω - Y ω - (a - b)
  let W : Ω → E := fun ω => X ω - a - (1 - β) • (Y ω - b)
  have hA : Integrable A μ := hX.sub (integrable_const _)
  have hW : Integrable W μ := hA.sub ((hY.sub (integrable_const _)).smul _)
  have hDm : (∫ ω, X ω - Y ω ∂μ) = a - b := by rw [integral_sub hX hY, hXa, hYb]
  have hcenter := centered_second_moment (hX.sub hY) hD2 (a - b) hDm
  have hB2 : Integrable (fun ω => ‖B ω‖ ^ 2) μ := hcenter.1
  have hid (ω : Ω) : W ω = β • A ω + (1 - β) • B ω := by dsimp [W, A, B]; module
  have hn (ω : Ω) : ‖W ω‖ ^ 2 ≤
      2 * β ^ 2 * ‖A ω‖ ^ 2 + 2 * (1 - β) ^ 2 * ‖B ω‖ ^ 2 := by
    rw [hid]
    have h := ProxLinearEnvelope.norm_add_sq_two (β • A ω) ((1 - β) • B ω)
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using h
  have hR : Integrable (fun ω => 2 * β ^ 2 * ‖A ω‖ ^ 2 +
      2 * (1 - β) ^ 2 * ‖B ω‖ ^ 2) μ := (hA2.const_mul _).add (hB2.const_mul _)
  have hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) μ :=
    hR.mono' (hW.aestronglyMeasurable.norm.pow 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hn ω)
  have hbound := integral_mono hW2 hR hn
  rw [integral_add (hA2.const_mul _) (hB2.const_mul _), integral_const_mul,
    integral_const_mul] at hbound
  have hBnon : 0 ≤ ∫ ω, ‖B ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hBmax : (∫ ω, ‖B ω‖ ^ 2 ∂μ) ≤ ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ := by
    rw [show (∫ ω, ‖B ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ) - ‖a - b‖ ^ 2 from hcenter.2]
    exact sub_le_self _ (sq_nonneg _)
  refine ⟨hW, ?_, hW2, ?_⟩
  · rw [integral_sub (f := fun ω => X ω - a)
      (g := fun ω => (1 - β) • (Y ω - b)) hA
      ((hY.sub (integrable_const b)).smul (1 - β)), integral_smul,
      integral_sub hX (integrable_const a), integral_sub hY (integrable_const b), hXa, hYb]
    simp
  · have hβsq : (1 - β) ^ 2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hβsq hBnon
    change (∫ ω, ‖W ω‖ ^ 2 ∂μ) ≤ _
    change _ ≤ 2 * β ^ 2 * (∫ ω, ‖A ω‖ ^ 2 ∂μ) + _
    nlinarith

end LongTails.Proofs.ProxLinearOracleMoments
