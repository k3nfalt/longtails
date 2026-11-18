import LongTails.Proofs.DistributedNormalizedPath
import LongTails.Proofs.DistributedNormalizedMeasurability
import LongTails.Proofs.ZerothOrderGridEstimator

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedConvergence

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

lemma root_gradient_integrable {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    {D : Z → Draws p} {S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams}
    (hD : Measurable D) (hS : Measurable S)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hgm : ∀ i, Measurable (Function.uncurry (g i))) (f : Point p → ℝ)
    (hL : 0 ≤ p.L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) (k : ℕ) :
    Integrable (fun z => ‖gradient f (trajectory p cfg (D z) g (S z) k).root‖) P := by
  have hgc : LipschitzWith ⟨p.L, hL⟩ (gradient f) := lipschitzWith_iff_norm_sub_le.mpr hlip
  have hm := hgc.continuous.measurable.comp
    (DistributedNormalizedMeasurability.measurable_trajectory p cfg g hgm hD hS k).1
  apply Integrable.of_bound hm.norm.aestronglyMeasurable (‖gradient f p.x0‖ + p.L * (k * cfg.stepSize))
  filter_upwards [] with z
  rw [norm_norm]
  dsimp only [Function.comp_def]
  have hp := DistributedNormalizedPath.root_path p cfg hη (D z) g (S z) k
  have hb := (hlip (trajectory p cfg (D z) g (S z) k).root p.x0).trans
    (mul_le_mul_of_nonneg_left hp hL)
  have ht := norm_add_le (gradient f (trajectory p cfg (D z) g (S z) k).root - gradient f p.x0)
    (gradient f p.x0)
  rw [sub_add_cancel] at ht
  linarith

lemma integrated_descent {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    (D : Z → Draws p) (S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 ≤ p.L) (K : ℕ) (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hi : ∀ k < K, Integrable (fun z => ‖gradient f (trajectory p cfg (D z) g (S z) k).root‖) P)
    (he : ∀ k < K, Integrable (fun z =>
      ‖estimator p cfg (D z) g (S z) k (trajectory p cfg (D z) g (S z) k) -
        gradient f (trajectory p cfg (D z) g (S z) k).root‖) P) :
    cfg.stepSize * ∑ k ∈ Finset.range K,
      (∫ z, ‖gradient f (trajectory p cfg (D z) g (S z) k).root‖ ∂P) ≤
      p.Δ + 2 * cfg.stepSize * ∑ k ∈ Finset.range K,
        (∫ z, ‖estimator p cfg (D z) g (S z) k (trajectory p cfg (D z) g (S z) k) -
          gradient f (trajectory p cfg (D z) g (S z) k).root‖ ∂P) +
      K * (p.L / 2 * cfg.stepSize ^ 2) := by
  have hgi := integrable_finsetSum (Finset.range K) (fun k hk => hi k (Finset.mem_range.mp hk))
  have hei := integrable_finsetSum (Finset.range K) (fun k hk => he k (Finset.mem_range.mp hk))
  have hpart : Integrable (fun z => p.Δ + 2 * cfg.stepSize * ∑ k ∈ Finset.range K,
      ‖estimator p cfg (D z) g (S z) k (trajectory p cfg (D z) g (S z) k) -
        gradient f (trajectory p cfg (D z) g (S z) k).root‖) P :=
    (integrable_const p.Δ).add (hei.const_mul (2 * cfg.stepSize))
  have h := integral_mono (hgi.const_mul cfg.stepSize)
    (((integrable_const p.Δ).add (hei.const_mul (2 * cfg.stepSize))).add
      (integrable_const ((K : ℝ) * (p.L / 2 * cfg.stepSize ^ 2)))) (fun z => by
        have hd := DistributedNormalizedPath.descent_sum p cfg hη (D z) g (S z) f hg hlip hL K
        exact hd.trans (add_le_add (add_le_add (hgap _) le_rfl) le_rfl))
  simp only [Pi.add_apply] at h
  rw [integral_add hpart
    (integrable_const ((K : ℝ) * (p.L / 2 * cfg.stepSize ^ 2))),
    integral_add (integrable_const p.Δ) (hei.const_mul (2 * cfg.stepSize))] at h
  simpa only [integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_finsetSum _ (fun k hk => hi k (Finset.mem_range.mp hk)),
    integral_finsetSum _ (fun k hk => he k (Finset.mem_range.mp hk))] using h

lemma normalized_sum_absorption {η ε Δ L N G E : ℝ}
    (hη : 0 < η) (hN : 0 < N)
    (hdescent : η * G ≤ Δ + 2 * η * E + N * (L / 2 * η ^ 2))
    (herror : E ≤ G / 8 + N * ε / 32)
    (hgap : Δ ≤ N * η * ε / 8) (hstep : L * η ≤ ε / 128) :
    G / N ≤ 49 * ε / 192 := by
  have herr := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2 * η by positivity)
  have hs := mul_le_mul_of_nonneg_left hstep (show 0 ≤ N * η / 2 by positivity)
  have hG : η * G ≤ η * (N * (49 * ε / 192)) := by nlinarith
  have hGN := (mul_le_mul_iff_right₀ hη).mp hG
  exact (div_le_iff₀ hN).mpr (by nlinarith)

lemma uniform_output_integral {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (K : ℕ+) (V : Fin K → Z → ℝ)
    (hm : ∀ i, Measurable (V i)) (hi : ∀ i, Integrable (V i) P) :
    Integrable (fun z : Fin K × Z => V z.1 z.2)
      ((PMF.uniformOfFintype (Fin K)).toMeasure.prod P) ∧
      (∫ z : Fin K × Z, V z.1 z.2 ∂(PMF.uniformOfFintype (Fin K)).toMeasure.prod P) =
        (K : ℝ)⁻¹ * ∑ i, ∫ z, V i z ∂P := by
  have hmeas : Measurable (fun z : Fin K × Z => V z.1 z.2) :=
    measurable_from_prod_countable_right hm
  have hint := OracleTemplate.ZerothOrder.finite_prod_integrable
    (μ := (PMF.uniformOfFintype (Fin K)).toMeasure) (ν := P) hmeas.aestronglyMeasurable hi
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint, OracleTemplate.ZerothOrder.uniform_integral_explicit]
  simp only [Fintype.card_fin, smul_eq_mul]

end LongTails.Proofs.DistributedNormalizedConvergence
