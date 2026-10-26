import LongTails.Proofs.GeneralNormClipping
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OracleTemplate.FairClippingTransfer

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residual_sq {B : ℝ} (hB : 0 < B) {u : E} (hu : ‖u‖ ≤ B / 2) (v : E) :
    ‖v - clip B v‖ ≤ 2 / B * ‖v - u‖ ^ 2 := by
  have h := clip_residual_le_moment (p := 2) hB (by norm_num) hu v
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two] at h
  convert h using 1
  ring

lemma discrepancy {Ω : Type*} {X Y : Ω → E} {S : Set Ω} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ ω ∉ S, X ω = Y ω) (ω : Ω) :
    ‖clip B (X ω) - clip B (Y ω)‖ ≤ S.indicator (fun _ => 2 * B) ω := by
  classical
  by_cases hw : ω ∈ S
  · rw [Set.indicator_of_mem hw]
    exact (norm_sub_le _ _).trans (by linarith [norm_clip_le hB (X ω), norm_clip_le hB (Y ω)])
  · rw [Set.indicator_of_notMem hw, h ω hw, sub_self, norm_zero]

lemma error_sq {Ω : Type*} {X Y : Ω → E} {S : Set Ω} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ ω ∉ S, X ω = Y ω) {u : E} (hu : ‖u‖ ≤ B) (ω : Ω) :
    ‖clip B (X ω) - u‖ ^ 2 ≤ ‖Y ω - u‖ ^ 2 + S.indicator (fun _ => 4 * B ^ 2) ω := by
  classical
  by_cases hw : ω ∈ S
  · rw [Set.indicator_of_mem hw]
    have hn : ‖clip B (X ω) - u‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [norm_clip_le hB (X ω)])
    nlinarith [sq_nonneg ‖Y ω - u‖,
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn]
  · rw [Set.indicator_of_notMem hw, add_zero, h ω hw]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_clip_sub_le hB hu (Y ω)) 2

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma integral_discrepancy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    {S : Set Ω} (hS : MeasurableSet S) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ω ∉ S, X ω = Y ω) :
    ‖(∫ ω, clip B (X ω) ∂P) - ∫ ω, clip B (Y ω) ∂P‖ ≤ 2 * B * P.real S := by
  have he := norm_integral_le_of_norm_le (μ := P)
    ((integrable_const (2 * B)).indicator hS)
    (Filter.Eventually.of_forall (discrepancy hB h))
  rw [integral_sub (GeneralNormClipping.integrable_clip hX hB)
    (GeneralNormClipping.integrable_clip hY hB), integral_indicator_const _ hS,
    smul_eq_mul, mul_comm] at he
  exact he

lemma integral_clipping_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → E} (hY : Measurable Y) (hYi : Integrable Y P)
    {u : E} (hmean : ∫ ω, Y ω ∂P = u)
    (hYi2 : Integrable (fun ω => ‖Y ω - u‖ ^ 2) P)
    {B : ℝ} (hB : 0 < B) (hu : ‖u‖ ≤ B / 2) :
    ‖(∫ ω, clip B (Y ω) ∂P) - u‖ ≤ 2 / B * ∫ ω, ‖Y ω - u‖ ^ 2 ∂P := by
  have he := norm_integral_le_of_norm_le (hYi2.const_mul (2 / B))
    (Filter.Eventually.of_forall (fun ω => residual_sq hB hu (Y ω)))
  rw [integral_sub hYi (GeneralNormClipping.integrable_clip hY hB.le),
    hmean, norm_sub_rev, integral_const_mul] at he
  exact he

lemma integral_bias_transfer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hYi : Integrable Y P) {u : E} (hmean : ∫ ω, Y ω ∂P = u)
    (hYi2 : Integrable (fun ω => ‖Y ω - u‖ ^ 2) P)
    {S : Set Ω} (hS : MeasurableSet S) {B : ℝ} (hB : 0 < B) (hu : ‖u‖ ≤ B / 2)
    (h : ∀ ω ∉ S, X ω = Y ω) :
    ‖(∫ ω, clip B (X ω) ∂P) - u‖ ≤
      2 / B * (∫ ω, ‖Y ω - u‖ ^ 2 ∂P) + 2 * B * P.real S := by
  have h₁ := integral_discrepancy (P := P) hX hY hS hB.le h
  have h₂ := integral_clipping_bias hY hYi hmean hYi2 hB hu
  have h₃ := norm_sub_le_norm_sub_add_norm_sub
    (∫ ω, clip B (X ω) ∂P) (∫ ω, clip B (Y ω) ∂P) u
  linarith

lemma integrable_clipped_error_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → E} (hX : Measurable X) {B : ℝ} (hB : 0 ≤ B) (u : E) :
    Integrable (fun ω => ‖clip B (X ω) - u‖ ^ 2) P := by
  apply Integrable.of_bound
    ((((measurable_clip B).comp hX).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    ((B + ‖u‖) ^ 2)
  filter_upwards [] with ω
  change |‖clip B (X ω) - u‖ ^ 2| ≤ _
  rw [abs_sq]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact (norm_sub_le _ _).trans (by linarith [norm_clip_le hB (X ω)])

lemma integral_error_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → E} (hX : Measurable X)
    {u : E} (hYi2 : Integrable (fun ω => ‖Y ω - u‖ ^ 2) P)
    {S : Set Ω} (hS : MeasurableSet S) {B : ℝ} (hB : 0 ≤ B) (hu : ‖u‖ ≤ B)
    (h : ∀ ω ∉ S, X ω = Y ω) :
    (∫ ω, ‖clip B (X ω) - u‖ ^ 2 ∂P) ≤
      (∫ ω, ‖Y ω - u‖ ^ 2 ∂P) + 4 * B ^ 2 * P.real S := by
  have hXi := integrable_clipped_error_sq (P := P) hX hB u
  have hI := (integrable_const (μ := P) (4 * B ^ 2)).indicator hS
  have he := integral_mono hXi (hYi2.add hI) (error_sq hB h hu)
  simp only [Pi.add_apply] at he
  rw [integral_add hYi2 hI, integral_indicator_const _ hS, smul_eq_mul,
    mul_comm (P.real S)] at he
  exact he

end OracleTemplate.FairClippingTransfer
