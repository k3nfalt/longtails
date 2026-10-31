import LongTails.Algorithms.GapNoiseSamples
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.MultiplicativeRobustConfidence

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.GapNoisePilot

open LongTails.Algorithms.GapNoisePastExtragradient

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma pilot_confidence {g : Ω → E} {u : E} {H0 V : ℝ} {batch : ℕ}
    (hg : Measurable g) (hi : Integrable g P) (hmean : (∫ ω, g ω ∂P) = u)
    (hvi : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hv : (∫ ω, ‖g ω - u‖ ^ 2 ∂P) ≤ V) (hH : 0 < H0) (hbatch : 0 < batch)
    (hsize : 2 ^ 20 * V ≤ (batch : ℝ) * (‖u‖ + H0) ^ 2) (groups : ℕ) :
    (Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin batch => P)
      {ξ | (‖u‖ + H0) / 8 < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun i => (1 / (batch : ℝ)) • ∑ j, g (ξ i j)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  let average : (Fin batch → Ω) → E := fun ξ => (1 / (batch : ℝ)) • ∑ j, g (ξ j)
  have hm : Measurable average := by dsimp [average]; fun_prop
  obtain ⟨hmi, hmoment⟩ := OracleTemplate.RobustGradient.finite_mean_variance
    hg hi u hvi hmean batch hbatch
  have hn : 0 < (batch : ℝ) := Nat.cast_pos.mpr hbatch
  have hr : 0 < (‖u‖ + H0) / 48 := by positivity
  have hbound : (∫ ξ, ‖average ξ - u‖ ^ 2 ∂Measure.pi (fun _ : Fin batch => P)) ≤ V / batch := by
    dsimp [average]
    rw [hmoment]
    exact div_le_div_of_nonneg_right hv hn.le
  have ht := OracleTemplate.RobustGradient.norm_tail_le_second_moment hmi hr hbound
  have ht' : (Measure.pi fun _ : Fin batch => P).real
      {ξ | (‖u‖ + H0) / 48 < ‖average ξ - u‖} ≤ 1 / 256 := by
    apply ht.trans
    rw [div_le_iff₀ (sq_pos_of_pos hr), div_le_iff₀ hn]
    nlinarith [mul_nonneg hn.le (sq_nonneg (‖u‖ + H0))]
  have h := OracleTemplate.MultiplicativeRobustEstimator.medoid_failure_probability hm u hr.le ht' groups
  simpa only [show 6 * ((‖u‖ + H0) / 48) = (‖u‖ + H0) / 8 by ring] using h

lemma shifted_pilot_confidence {g : Ω → E} {u a : E} {H0 V : ℝ} {batch : ℕ}
    (hg : Measurable g) (hi : Integrable g P) (hmean : (∫ ω, g ω ∂P) = u)
    (hvi : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hv : (∫ ω, ‖g ω - u‖ ^ 2 ∂P) ≤ V) (hH : 0 < H0) (hbatch : 0 < batch)
    (hsize : 2 ^ 20 * V ≤ (batch : ℝ) * (‖u + a‖ + H0) ^ 2) (groups : ℕ) :
    (Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin batch => P)
      {ξ | (‖u + a‖ + H0) / 8 < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun i => (1 / (batch : ℝ)) • ∑ j, g (ξ i j) + a) - (u + a)‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  have hm : (∫ ω, g ω + a ∂P) = u + a := by
    rw [integral_add hi (integrable_const _), hmean]
    simp
  have hvi' : Integrable (fun ω => ‖(g ω + a) - (u + a)‖ ^ 2) P := by
    simpa only [add_sub_add_right_eq_sub] using hvi
  have hv' : (∫ ω, ‖(g ω + a) - (u + a)‖ ^ 2 ∂P) ≤ V := by
    simpa only [add_sub_add_right_eq_sub] using hv
  have hh := pilot_confidence (hg.add measurable_const) (hi.add (integrable_const _))
    hm hvi' hv' hH hbatch hsize groups
  have he (ξ : Fin batch → Ω) : (1 / (batch : ℝ)) • ∑ j, (g (ξ j) + a) =
      (1 / (batch : ℝ)) • ∑ j, g (ξ j) + a := by
    rw [Finset.sum_add_distrib, smul_add]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hbatch)), one_smul]
  simpa only [Pi.add_apply, he] using hh

lemma sampled_pilot_confidence
    (c : StageConfig (E := E))
    {g : E → Ω → E} {F : E → E} (x : E) {V : ℝ} {batch : ℕ}
    (hg : Measurable (g x)) (hi : Integrable (g x) P) (hmean : (∫ ω, g x ω ∂P) = F x)
    (hvi : Integrable (fun ω => ‖g x ω - F x‖ ^ 2) P)
    (hv : (∫ ω, ‖g x ω - F x‖ ^ 2 ∂P) ≤ V)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hbatch : 0 < batch)
    (hsize : 2 ^ 20 * V ≤ (batch : ℝ) *
      (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) ^ 2)
    (groups : ℕ) :
    (Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin batch => P)
      {ξ | (‖regularizedReply c x (F x)‖ +
          c.scale / c.curvature) / 8 <
        ‖pilotFromSamples c g x batch groups ξ -
          regularizedReply c x (F x)‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  exact shifted_pilot_confidence hg hi hmean hvi hv (div_pos hS hb) hbatch hsize groups

lemma relative_variance_batch {σ v R h H0 batch : ℝ}
    (hv : 0 ≤ v) (hR : 0 ≤ R) (hh : 0 ≤ h) (hH : 0 < H0)
    (hbatch : 2 ^ 20 * (σ ^ 2 / H0 ^ 2 + v * R / H0) ≤ batch) :
    2 ^ 20 * (σ ^ 2 + v * R * (h + H0)) ≤ batch * (h + H0) ^ 2 := by
  have hs : H0 ^ 2 ≤ (h + H0) ^ 2 := by nlinarith
  have hl : H0 * (h + H0) ≤ (h + H0) ^ 2 := by nlinarith
  have hσ : σ ^ 2 ≤ (σ ^ 2 / H0 ^ 2) * (h + H0) ^ 2 := by
    calc
      σ ^ 2 = (σ ^ 2 / H0 ^ 2) * H0 ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hn : v * R * (h + H0) ≤ (v * R / H0) * (h + H0) ^ 2 := by
    calc
      v * R * (h + H0) = (v * R / H0) * (H0 * (h + H0)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have hb : σ ^ 2 + v * R * (h + H0) ≤
      (σ ^ 2 / H0 ^ 2 + v * R / H0) * (h + H0) ^ 2 := by nlinarith
  calc
    _ ≤ 2 ^ 20 * ((σ ^ 2 / H0 ^ 2 + v * R / H0) * (h + H0) ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 ^ 20 * (σ ^ 2 / H0 ^ 2 + v * R / H0)) * (h + H0) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbatch (sq_nonneg _)

end LongTails.Proofs.GapNoisePilot
