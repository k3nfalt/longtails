import LongTails.Proofs.AdaptiveEntropicGeometry
import LongTails.Proofs.GeneralNormClipping
import LongTails.Proofs.QuantileClipping
import Mathlib.Analysis.MeanInequalitiesPow
import LongTails.Proofs.AdaptiveEntropicStateMeasurable

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma clippedReply_coordinates {d : ℕ} (B : ℝ) (c g : Vector d) :
    (fun i => (clippedReply B c g - c) i) = clip B (fun i => (g - c) i) := by
  unfold clippedReply clip dualNorm
  split_ifs <;> funext i <;> simp

lemma clippedReply_residual {d : ℕ} {B : ℝ} (hB : 0 ≤ B) (c g : Vector d) :
    dualNorm (g - clippedReply B c g) = max 0 (dualNorm (g - c) - B) := by
  have he : (fun i => (g - clippedReply B c g) i) =
      (fun i => (g - c) i) - clip B (fun i => (g - c) i) := by
    rw [← clippedReply_coordinates B c g]
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  unfold dualNorm
  rw [he, GeneralNormClipping.residual_norm hB]

lemma clippedReply_difference {d : ℕ} {B : ℝ} (hB : 0 ≤ B) (c g h : Vector d) :
    dualNorm (clippedReply B c g - clippedReply B c h) ≤ 2 * dualNorm (g - h) := by
  have he : (fun i => (clippedReply B c g - clippedReply B c h) i) =
      clip B (fun i => (g - c) i) - clip B (fun i => (h - c) i) := by
    rw [← clippedReply_coordinates B c g, ← clippedReply_coordinates B c h]
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  have hd : (fun i => (g - c) i) - (fun i => (h - c) i) = fun i => (g - h) i := by
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  unfold dualNorm
  rw [he]
  simpa only [hd] using GeneralNormClipping.difference hB
    (fun i => (g - c) i) (fun i => (h - c) i)

lemma clippedReply_weighted_residual {d : ℕ} {t Q r : ℝ}
    (ht : 0 < t) (hQ : 0 ≤ Q) (hr : 0 ≤ r) (c g : Vector d) :
    t * dualNorm (g - clippedReply (r + Q / t) c g) =
      max 0 (t * max 0 (dualNorm (g - c) - r) - Q) := by
  rw [clippedReply_residual (add_nonneg hr (div_nonneg hQ ht.le))]
  exact QuantileClipping.weighted_excess ht hQ _ _

lemma innovation_bound {d : ℕ} (g c μ : Vector d) {r σ : ℝ} (hσ : 0 ≤ σ)
    (hc : dualNorm (μ - c) ≤ 8 * σ + r) :
    max 0 (dualNorm (g - c) - r) ≤ dualNorm (g - μ) + 8 * σ := by
  have he : (fun i => (g - c) i) = (fun i => (g - μ) i) + (fun i => (μ - c) i) := by
    funext i
    simp only [Pi.add_apply, PiLp.sub_apply]
    ring
  have ht : dualNorm (g - c) ≤ dualNorm (g - μ) + dualNorm (μ - c) := by
    unfold dualNorm
    rw [he]
    exact norm_add_le _ _
  apply max_le
  · exact add_nonneg (norm_nonneg _) (by positivity)
  · linarith

lemma shifted_moment_pointwise {a σ p : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    (a + 8 * σ) ^ p ≤ 2 * a ^ p + 128 * σ ^ p := by
  have hbase : (a + 8 * σ) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + (8 * σ) ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨a, ha⟩ : NNReal) (⟨8 * σ, by positivity⟩ : NNReal) hp
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show p - 1 ≤ 1 by linarith)
  have height : (8 : ℝ) ^ p ≤ 64 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hp2 using 1; norm_num
  have hsum : 0 ≤ a ^ p + (8 * σ) ^ p := by positivity
  have hh := hbase.trans (mul_le_mul_of_nonneg_right htwo hsum)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hσ] at hh
  have hs := mul_le_mul_of_nonneg_right height (Real.rpow_nonneg hσ p)
  linarith

lemma innovation_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → Vector d}
    (hG : Measurable G) (c μ : Vector d) {r σ p : ℝ}
    (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : dualNorm (μ - c) ≤ 8 * σ + r)
    (hi : Integrable (fun ω => dualNorm (G ω - μ) ^ p) P)
    (hm : (∫ ω, dualNorm (G ω - μ) ^ p ∂P) ≤ σ ^ p) :
    Integrable (fun ω => max 0 (dualNorm (G ω - c) - r) ^ p) P ∧
      (∫ ω, max 0 (dualNorm (G ω - c) - r) ^ p ∂P) ≤ 130 * σ ^ p := by
  have hb (ω : Ω) : max 0 (dualNorm (G ω - c) - r) ^ p ≤
      2 * dualNorm (G ω - μ) ^ p + 128 * σ ^ p := by
    exact (Real.rpow_le_rpow (le_max_left _ _) (innovation_bound (G ω) c μ hσ hc)
      (by linarith : 0 ≤ p)).trans (shifted_moment_pointwise (norm_nonneg _) hσ hp hp2)
  have hdom : Integrable (fun ω => 2 * dualNorm (G ω - μ) ^ p + 128 * σ ^ p) P :=
    (hi.const_mul 2).add (integrable_const _)
  have hmeas : Measurable (fun ω => max 0 (dualNorm (G ω - c) - r) ^ p) := by
    exact (measurable_const.max (((measurable_dualNorm d).comp
      (hG.sub_const c)).sub_const r)).pow_const p
  have hx : Integrable (fun ω => max 0 (dualNorm (G ω - c) - r) ^ p) P := by
    apply hdom.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_left _ _) p)]
    exact hb ω
  refine ⟨hx, ?_⟩
  have hh := integral_mono hx hdom hb
  rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  linarith

lemma clippedReply_difference_sq_moment {d : ℕ} {B p : ℝ}
    (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2) (c g h : Vector d) :
    dualNorm (clippedReply B c g - clippedReply B c h) ^ 2 ≤
      4 * B ^ (2 - p) * dualNorm (g - h) ^ p := by
  have he : (fun i => (clippedReply B c g - clippedReply B c h) i) =
      clip B (fun i => (g - c) i) - clip B (fun i => (h - c) i) := by
    rw [← clippedReply_coordinates B c g, ← clippedReply_coordinates B c h]
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  have hd : (fun i => (g - c) i) - (fun i => (h - c) i) = fun i => (g - h) i := by
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  unfold dualNorm
  rw [he]
  simpa only [hd] using GeneralNormClipping.difference_sq_moment hB hp hp2
    (fun i => (g - c) i) (fun i => (h - c) i)

lemma dualNorm_difference_moment {d : ℕ} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (g h μ : Vector d) :
    dualNorm (g - h) ^ p ≤ 2 * (dualNorm (g - μ) ^ p + dualNorm (h - μ) ^ p) := by
  have he : (fun i => (g - h) i) = (fun i => (g - μ) i) - (fun i => (h - μ) i) := by
    funext i
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  have ht : dualNorm (g - h) ≤ dualNorm (g - μ) + dualNorm (h - μ) := by
    unfold dualNorm
    rw [he]
    exact norm_sub_le _ _
  have hbase : (dualNorm (g - μ) + dualNorm (h - μ)) ^ p ≤
      (2 : ℝ) ^ (p - 1) * (dualNorm (g - μ) ^ p + dualNorm (h - μ) ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨dualNorm (g - μ), norm_nonneg _⟩ : NNReal)
      (⟨dualNorm (h - μ), norm_nonneg _⟩ : NNReal) hp
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show p - 1 ≤ 1 by linarith)
  exact (Real.rpow_le_rpow (norm_nonneg _) ht (by linarith)).trans
    (hbase.trans (mul_le_mul_of_nonneg_right htwo
      (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _))))

lemma clippedReply_pair_moment {d : ℕ} {B p : ℝ}
    (hB : 0 < B) (hp : 1 ≤ p) (hp2 : p ≤ 2) (c g h μ : Vector d) :
    dualNorm (clippedReply B c g - clippedReply B c h) ^ 2 ≤
      8 * B ^ (2 - p) * (dualNorm (g - μ) ^ p + dualNorm (h - μ) ^ p) := by
  have hh := mul_le_mul_of_nonneg_left (dualNorm_difference_moment hp hp2 g h μ)
    (show 0 ≤ 4 * B ^ (2 - p) by positivity)
  exact (clippedReply_difference_sq_moment hB (by linarith) hp2 c g h).trans
    (by nlinarith)

lemma positive_part_tail_moment {v A p : ℝ} (hv : 0 ≤ v) (hA : 0 < A) (hp : 1 ≤ p) :
    max 0 (v - A) ≤ v ^ p / A ^ (p - 1) := by
  by_cases h : v ≤ A
  · rw [max_eq_left (sub_nonpos.mpr h)]
    positivity
  · have hav : A ≤ v := (lt_of_not_ge h).le
    have hvp : 0 < v := hA.trans_le hav
    have hpow := Real.rpow_le_rpow hA.le hav (show 0 ≤ p - 1 by linarith)
    have hm := mul_le_mul_of_nonneg_left hpow hv
    have he : v * v ^ (p - 1) = v ^ p := by
      rw [Real.rpow_sub hvp, Real.rpow_one]
      field_simp
    rw [he] at hm
    have hden : 0 < A ^ (p - 1) := Real.rpow_pos_of_pos hA _
    apply (max_le hv (by linarith : v - A ≤ v)).trans
    exact (le_div_iff₀ hden).mpr hm

lemma tail_indicator_moment {v A p : ℝ} (hv : 0 ≤ v) (hA : 0 < A) (hp : 0 ≤ p) :
    (if A < v then (1 : ℝ) else 0) ≤ v ^ p / A ^ p := by
  split_ifs with h
  · apply (one_le_div (Real.rpow_pos_of_pos hA p)).mpr
    exact Real.rpow_le_rpow hA.le h.le hp
  · positivity

end OracleTemplate.AdaptiveHeavyTailSimplex
