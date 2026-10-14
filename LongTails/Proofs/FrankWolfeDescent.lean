import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace OracleTemplate.FrankWolfe

open Set InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma convex_support_on {C : Set E} {f : E → ℝ} {g x y : E}
    (hc : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C) (hg : HasGradientAt f g x) :
    ⟪g, y - x⟫ ≤ f y - f x := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt f ((toDual ℝ E) g) ((AffineMap.lineMap x y) (0 : ℝ)) := by
    simpa using hg.hasFDerivAt
  have hline : HasDerivAt (f ∘ AffineMap.lineMap x y) ⟪g, y - x⟫ (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have h := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hline
  simpa [slope_def_field] using h

lemma smooth_upper_bound_on {C : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : Convex ℝ C) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => ⟪g (x + t • d), d⟫
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ C := by
    intro t ht
    convert hc hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring) using 1
    dsimp [d]
    module
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t := by
    intro t ht
    have h := (hg _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul, toDual_apply_apply] at h
    exact h
  let B := fun t : ℝ => f x + t * ⟪g x, d⟫ + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪g x, d⟫ + L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪g x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ ⟪g x, d⟫ + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := (real_inner_le_norm (g (x + t • d) - g x) d).trans
      (mul_le_mul_of_nonneg_right (hlip _ (hmem t ⟨ht.1, ht.2.le⟩) _ hx) (norm_nonneg d))
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_sub_left] at h
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hF t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

lemma short_step_range {gap curvature : ℝ} (hg : 0 ≤ gap) (hc : 0 < curvature) :
    0 ≤ min 1 (gap / curvature) ∧ min 1 (gap / curvature) ≤ 1 := by
  exact ⟨le_min (by norm_num) (div_nonneg hg hc.le), min_le_left _ _⟩

lemma short_step_model_decrease {gap curvature : ℝ}
    (hc : 0 < curvature) :
    let γ := min 1 (gap / curvature)
    min (gap / 2) (gap ^ 2 / (2 * curvature)) ≤
      γ * gap - curvature / 2 * γ ^ 2 := by
  dsimp only
  by_cases h : curvature ≤ gap
  · rw [min_eq_left ((le_div_iff₀ hc).mpr (by simpa using h))]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right ((div_le_one hc).mpr (le_of_not_ge h))]
    calc
      min (gap / 2) (gap ^ 2 / (2 * curvature)) ≤
          gap ^ 2 / (2 * curvature) := min_le_right _ _
      _ = gap / curvature * gap - curvature / 2 * (gap / curvature) ^ 2 := by
        field_simp
        ring

lemma short_step_descent {before after gap curvature : ℝ}
    (hc : 0 < curvature)
    (hmodel : after ≤ before - min 1 (gap / curvature) * gap +
      curvature / 2 * (min 1 (gap / curvature)) ^ 2) :
    after ≤ before - min (gap / 2) (gap ^ 2 / (2 * curvature)) := by
  have h := short_step_model_decrease (gap := gap) hc
  dsimp only at h
  linarith

lemma short_step_model_optimal {gap curvature t : ℝ} (hc : 0 < curvature)
    (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * gap - curvature / 2 * t ^ 2 ≤
      min 1 (gap / curvature) * gap - curvature / 2 * (min 1 (gap / curvature)) ^ 2 := by
  by_cases h : curvature ≤ gap
  · rw [min_eq_left ((le_div_iff₀ hc).mpr (by simpa using h))]
    nlinarith [sq_nonneg (1 - t), mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht1)]
  · rw [min_eq_right ((div_le_one hc).mpr (le_of_not_ge h))]
    have hs := mul_nonneg (by positivity : 0 ≤ curvature / 2) (sq_nonneg (t - gap / curvature))
    have heq : gap / curvature * gap - curvature / 2 * (gap / curvature) ^ 2 -
        (t * gap - curvature / 2 * t ^ 2) = curvature / 2 * (t - gap / curvature) ^ 2 := by
      field_simp
      ring
    linarith

lemma short_step_initial_bound {before after gap curvature : ℝ} (hc : 0 < curvature)
    (hgap : before ≤ gap)
    (hmodel : after ≤ before - min 1 (gap / curvature) * gap +
      curvature / 2 * (min 1 (gap / curvature)) ^ 2) : after ≤ curvature / 2 := by
  have h := short_step_model_optimal (gap := gap) hc (t := 1) (by norm_num) le_rfl
  norm_num at h
  linarith

end OracleTemplate.FrankWolfe
