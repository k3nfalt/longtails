import LongTails.Proofs.BFGSRate
import LongTails.Proofs.LinearDecaySgdStep
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BFGSComposite

open LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSRate

variable {d m : ℕ}

lemma hasGradientAt_comp (A : Space d →L[ℝ] Space m) {h : Space m → ℝ} {gh : Space m}
    {x : Space d} (hh : HasGradientAt h gh (A x)) :
    HasGradientAt (fun x => h (A x)) (ContinuousLinearMap.adjoint A gh) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hh ⊢
  have hc := hh.comp x A.hasFDerivAt
  have heq : InnerProductSpace.toDual ℝ (Space d) (ContinuousLinearMap.adjoint A gh) =
      (InnerProductSpace.toDual ℝ (Space m) gh).comp A := by
    ext v
    rw [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [heq]
  exact hc

lemma coco_inner {h : Space m → ℝ} {gradH : Space m → Space m} {Lh : ℝ} (hLh : 0 < Lh)
    (hc : ConvexOn ℝ univ h) (hg : ∀ z, HasGradientAt h (gradH z) z)
    (hlip : ∀ z w, ‖gradH z - gradH w‖ ≤ Lh * ‖z - w‖) (a b : Space m) :
    ‖gradH a - gradH b‖ ^ 2 ≤ Lh * ⟪gradH a - gradH b, a - b⟫ := by
  have h1 := OracleTemplate.SampledConvex.cocoercive hLh hc hg hlip a b
  have h2 := OracleTemplate.SampledConvex.cocoercive hLh hc hg hlip b a
  have e : ‖gradH b - gradH a‖ = ‖gradH a - gradH b‖ := norm_sub_rev _ _
  rw [e] at h2
  have e2 : ⟪gradH a - gradH b, a - b⟫ = ⟪gradH a, a - b⟫ + ⟪gradH b, b - a⟫ := by
    rw [inner_sub_left, show b - a = -(a - b) by abel, inner_neg_right]
    ring
  have hx : ⟪gradH b, a - b⟫ = -⟪gradH b, b - a⟫ := by rw [← inner_neg_right, neg_sub]
  have hy : ⟪gradH a, b - a⟫ = -⟪gradH a, a - b⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hx] at h1
  rw [hy] at h2
  rw [e2]
  have hs : 2 * Lh * (h a - h b - -⟪gradH b, b - a⟫) + 2 * Lh * (h b - h a - -⟪gradH a, a - b⟫) =
      2 * (Lh * (⟪gradH a, a - b⟫ + ⟪gradH b, b - a⟫)) := by ring
  linarith

lemma adjoint_norm_le (A : Space d →L[ℝ] Space m) (v : Space m) :
    ‖ContinuousLinearMap.adjoint A v‖ ≤ ‖A‖ * ‖v‖ := by
  have := (ContinuousLinearMap.adjoint A).le_opNorm v
  rwa [LinearIsometryEquiv.norm_map] at this

theorem prob_of_composite {A : Space d →L[ℝ] Space m} {h : Space m → ℝ}
    {gradH : Space m → Space m} {Lh μ L : ℝ} {xs x0 : Space d}
    (hc : ConvexOn ℝ univ h) (hg : ∀ z, HasGradientAt h (gradH z) z)
    (hlip : ∀ z w, ‖gradH z - gradH w‖ ≤ Lh * ‖z - w‖) (hμ : 0 < μ) (hLh : 0 < Lh)
    (hAL : Lh * ‖A‖ ^ 2 ≤ L) (hmin : IsMinOn (fun x => h (A x)) univ xs)
    (hqg : ∀ x, h (A x) ≤ h (A x0) → μ / 2 * ‖A x - A xs‖ ^ 2 ≤ h (A x) - h (A xs)) :
    Prob (fun x => h (A x)) xs x0 L (Lh / μ) := by
  set gf : Space d → Space d := fun x => ContinuousLinearMap.adjoint A (gradH (A x))
  have hgf : ∀ x, HasGradientAt (fun x => h (A x)) (gf x) x :=
    fun x => hasGradientAt_comp A (hg (A x))
  have huniq : ∀ x gx, HasGradientAt (fun x => h (A x)) gx x → gx = gf x :=
    fun x gx hx => hx.unique (hgf x)
  have hdiff : ∀ x z, gf z - gf x = ContinuousLinearMap.adjoint A (gradH (A z) - gradH (A x)) :=
    fun x z => (map_sub _ _ _).symm
  have hinner : ∀ x z w, ⟪gf z - gf x, w⟫ = ⟪gradH (A z) - gradH (A x), A w⟫ := by
    intro x z w
    rw [hdiff, ContinuousLinearMap.adjoint_inner_left]
  have hconv : ConvexOn ℝ univ (fun x => h (A x)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := hc.2 (mem_univ (A x)) (mem_univ (A y)) ha hb hab
    simpa only [map_add, map_smul] using this
  refine ⟨fun x => hmin (mem_univ x), ?_, ?_, ?_⟩
  · intro x gx hx
    rw [huniq x gx hx]
    have := OracleTemplate.Gradient.convex_support hconv hgf x xs
    have e : ⟪gf x, x - xs⟫ = -⟪gf x, xs - x⟫ := by
      rw [show x - xs = -(xs - x) by abel, inner_neg_right]
    linarith
  · intro x gx z gz hx hz
    rw [huniq x gx hx, huniq z gz hz]
    have hco := coco_inner hLh hc hg hlip (A z) (A x)
    have hn := adjoint_norm_le A (gradH (A z) - gradH (A x))
    rw [← hdiff] at hn
    have hAzx : A z - A x = A (z - x) := (map_sub _ _ _).symm
    rw [hAzx, ← hinner] at hco
    have hsq : ‖gf z - gf x‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖gradH (A z) - gradH (A x)‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hip : 0 ≤ ⟪gf z - gf x, z - x⟫ := by
      nlinarith [sq_nonneg ‖gradH (A z) - gradH (A x)‖]
    calc ‖gf z - gf x‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖gradH (A z) - gradH (A x)‖ ^ 2 := hsq
      _ ≤ ‖A‖ ^ 2 * (Lh * ⟪gf z - gf x, z - x⟫) :=
          mul_le_mul_of_nonneg_left hco (sq_nonneg _)
      _ = (Lh * ‖A‖ ^ 2) * ⟪gf z - gf x, z - x⟫ := by ring
      _ ≤ L * ⟪gf z - gf x, z - x⟫ := mul_le_mul_of_nonneg_right hAL hip
  · intro x gx z gz hx hz hlev
    rw [huniq x gx hx, huniq z gz hz]
    have hco := coco_inner hLh hc hg hlip (A z) (A x)
    have hAzx : A z - A x = A (z - x) := (map_sub _ _ _).symm
    rw [hAzx, ← hinner] at hco
    have hq := hqg z hlev
    rw [hinner x z (z - xs), map_sub]
    have hcs := abs_real_inner_le_norm (gradH (A z) - gradH (A x)) (A z - A xs)
    have hsq : ⟪gradH (A z) - gradH (A x), A z - A xs⟫ ^ 2 ≤
        ‖gradH (A z) - gradH (A x)‖ ^ 2 * ‖A z - A xs‖ ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
    have hA2 : ‖A z - A xs‖ ^ 2 ≤ 2 / μ * (h (A z) - h (A xs)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
      linarith
    have hip : 0 ≤ ⟪gf z - gf x, z - x⟫ := by
      nlinarith [sq_nonneg ‖gradH (A z) - gradH (A x)‖]
    calc ⟪gradH (A z) - gradH (A x), A z - A xs⟫ ^ 2
        ≤ ‖gradH (A z) - gradH (A x)‖ ^ 2 * ‖A z - A xs‖ ^ 2 := hsq
      _ ≤ (Lh * ⟪gf z - gf x, z - x⟫) * (2 / μ * (h (A z) - h (A xs))) :=
          mul_le_mul hco hA2 (sq_nonneg _) (by positivity)
      _ = 2 * (Lh / μ) * ⟪gf z - gf x, z - x⟫ * (h (A z) - h (A xs)) := by
          field_simp

theorem initial_gap {A : Space d →L[ℝ] Space m} {h : Space m → ℝ}
    {gradH : Space m → Space m} {Lh L : ℝ} {xs x0 : Space d}
    (hg : ∀ z, HasGradientAt h (gradH z) z) (hlip : ∀ z w, ‖gradH z - gradH w‖ ≤ Lh * ‖z - w‖)
    (hLh : 0 ≤ Lh) (hAL : Lh * ‖A‖ ^ 2 ≤ L) (hmin : IsMinOn (fun x => h (A x)) univ xs) :
    h (A x0) - h (A xs) ≤ L / 2 * ‖x0 - xs‖ ^ 2 := by
  set gf : Space d → Space d := fun x => ContinuousLinearMap.adjoint A (gradH (A x))
  have hgf : ∀ x, HasGradientAt (fun x => h (A x)) (gf x) x :=
    fun x => hasGradientAt_comp A (hg (A x))
  have hlipf : ∀ x y, ‖gf x - gf y‖ ≤ (Lh * ‖A‖ ^ 2) * ‖x - y‖ := by
    intro x y
    have h1 := adjoint_norm_le A (gradH (A x) - gradH (A y))
    rw [map_sub] at h1
    have h2 := hlip (A x) (A y)
    have h3 : ‖A x - A y‖ ≤ ‖A‖ * ‖x - y‖ := by
      rw [← map_sub]
      exact A.le_opNorm _
    calc ‖gf x - gf y‖ ≤ ‖A‖ * ‖gradH (A x) - gradH (A y)‖ := h1
      _ ≤ ‖A‖ * (Lh * (‖A‖ * ‖x - y‖)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hLh)
      _ = (Lh * ‖A‖ ^ 2) * ‖x - y‖ := by ring
  have hz : gf xs = 0 := by
    have hloc : IsLocalMin (fun x => h (A x)) xs :=
      Filter.Eventually.of_forall fun w => hmin (mem_univ w)
    have h0 := hloc.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.mp (hgf xs))
    simpa using h0
  have hup := OracleTemplate.Gradient.smooth_upper_bound hgf hlipf xs x0
  rw [hz, inner_zero_left, add_zero] at hup
  have : (Lh * ‖A‖ ^ 2) / 2 * ‖x0 - xs‖ ^ 2 ≤ L / 2 * ‖x0 - xs‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  linarith

end LongTails.Proofs.BFGSComposite
