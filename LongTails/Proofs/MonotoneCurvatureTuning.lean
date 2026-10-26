import LongTails.Algorithms.MonotoneCurvatureStage
import LongTails.Proofs.LazyQuarticDecay

namespace LongTails.Proofs.MonotoneCurvatureTuning

open LongTails.Algorithms.MonotoneCurvatureStage
open LongTails.Algorithms.QuarticMetricStage

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def distanceScale (H γ : ℝ) : ℝ := γ / (2 ^ 30 * H)

noncomputable def metricRadius (H γ t : ℝ) : ℝ := 32 * t * Real.sqrt γ * distanceScale H γ

lemma distanceScale_pos {H γ : ℝ} (hH : 0 < H) (hγ : 0 < γ) : 0 < distanceScale H γ := by
  unfold distanceScale
  positivity

lemma metricRadius_pos {H γ t : ℝ} (hH : 0 < H) (hγ : 0 < γ) (ht : 0 < t) :
    0 < metricRadius H γ t := by
  have hd := distanceScale_pos hH hγ
  unfold metricRadius
  positivity

lemma acceleration (S : E ≃L[ℝ] E) (c : Point E) (H γ t : ℝ) :
    (parameters S c H γ t).a ^ 2 * (parameters S c H γ t).L =
      (parameters S c H γ t).μ := by
  dsimp [parameters]
  ring

lemma radius_identity (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hγ : 0 ≤ γ) (ht : t ≠ 0) :
    (metricRadius H γ t) ^ 2 = 2 * (parameters S c H γ t).q / (parameters S c H γ t).μ := by
  dsimp [metricRadius, distanceScale, parameters]
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hγ]
  field_simp
  ring

lemma radius_clipping (S : E ≃L[ℝ] E) (c : Point E) (H γ t : ℝ) :
    metricRadius H γ t = (parameters S c H γ t).r / 8 := by
  dsimp [metricRadius, distanceScale, parameters]
  ring

lemma scales (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) :
    0 ≤ (parameters S c H γ t).a ∧ (parameters S c H γ t).a ≤ 1 ∧
    0 < (parameters S c H γ t).μ ∧ (parameters S c H γ t).μ ≤ (parameters S c H γ t).L ∧
    0 < (parameters S c H γ t).r ∧ 0 < (parameters S c H γ t).q := by
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  dsimp [parameters]
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, by positivity⟩
  · apply (div_le_one (by positivity)).mpr
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith

lemma progress_clipping (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) :
    (parameters S c H γ t).q ≤ (parameters S c H γ t).L * (parameters S c H γ t).r ^ 2 / 16 := by
  have ht0 : t ≠ 0 := by linarith
  have hr := radius_identity S c (H := H) hγ.le ht0
  have hc := radius_clipping S c H γ t
  have hμ := (scales S c hH hγ ht).2.2.1
  have hμL := (scales S c hH hγ ht).2.2.2.1
  have he : (parameters S c H γ t).μ * (metricRadius H γ t) ^ 2 = 2 * (parameters S c H γ t).q := by
    have hh := (eq_div_iff hμ.ne').mp hr
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hμL (sq_nonneg (metricRadius H γ t))
  have hq := (scales S c hH hγ ht).2.2.2.2.2
  rw [hc] at he hm
  nlinarith

lemma query_radius (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) :
    (metricRadius H γ t + (parameters S c H γ t).r / 2) / (t * Real.sqrt γ) =
      160 * distanceScale H γ := by
  have hs : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.mpr hγ).ne'
  dsimp [metricRadius, distanceScale, parameters]
  field_simp
  ring

lemma small_query_radius {H γ t : ℝ} (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) :
    H * (160 * distanceScale H γ) ≤ t ^ 2 * γ / 16 := by
  have he : H * distanceScale H γ = γ / 2 ^ 30 := by
    unfold distanceScale
    field_simp
  have ht₂ : 1 ≤ t ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ht₂ hγ.le
  nlinarith

lemma horizon_decay (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (ht : 1 ≤ t) :
    (1 - (parameters S c H γ t).a) ^ horizon t ≤ 1 / (80 * t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have ha : (parameters S c H γ t).a ≤ 1 := by
    change 1 / (64 * t) ≤ 1
    apply (div_le_one (by positivity)).mpr
    linarith
  have hn := Nat.le_ceil (2 ^ 13 * t * Real.log (2 + t))
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 / (64 * t) by positivity)
  have he : 1 / (64 * t) * (2 ^ 13 * t * Real.log (2 + t)) =
      128 * Real.log (2 + t) := by field_simp; ring
  rw [he] at hn'
  have hdec := LazyQuarticDecay.geometric_decay ha (show 0 < 2 + t by linarith) hn'
  have hp : 80 * t ^ 2 ≤ (2 + t) ^ (128 : ℕ) := by
    have h₁ : (80 : ℝ) ≤ (2 + t) ^ (126 : ℕ) := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (show 3 ≤ 2 + t by linarith) 126
      norm_num at hh ⊢
      linarith
    have h₂ : t ^ 2 ≤ (2 + t) ^ 2 := by nlinarith
    have hh := mul_le_mul h₁ h₂ (sq_nonneg _) (by positivity)
    have heq : (2 + t) ^ (128 : ℕ) = (2 + t) ^ (126 : ℕ) * (2 + t) ^ 2 := by rw [← pow_add]
    rw [heq]
    exact hh
  exact hdec.trans (one_div_le_one_div_of_le (by positivity) hp)

end LongTails.Proofs.MonotoneCurvatureTuning
