import LongTails.Proofs.BlumGladyshevValley
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace ContDiff

namespace LongTails.Proofs.BlumGladyshevValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ridge (a b : ℝ) (e x₀ x : E) : ℝ :=
  a * valley (⟪e, x - x₀⟫ - b)

noncomputable def ridgeGradient (a b : ℝ) (e x₀ x : E) : E :=
  (a * slope (⟪e, x - x₀⟫ - b)) • e

lemma valley_smooth : ContDiff ℝ ∞ valley := by
  unfold valley
  exact ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun x : ℝ => by positivity)).sub contDiff_const

lemma ridge_smooth (a b : ℝ) (e x₀ : E) : ContDiff ℝ ∞ (ridge a b e x₀) := by
  unfold ridge
  apply contDiff_const.mul
  apply valley_smooth.comp
  exact (((innerSL ℝ e).contDiff).comp (contDiff_id.sub contDiff_const)).sub contDiff_const

lemma ridge_gradient [CompleteSpace E] (a b : ℝ) (e x₀ x : E) :
    HasGradientAt (ridge a b e x₀) (ridgeGradient a b e x₀ x) x := by
  let A := InnerProductSpace.toDual ℝ E e
  have h := ((valley_derivative (⟪e, x - x₀⟫ - b)).hasFDerivAt.comp x
    ((A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)).sub_const b)).const_mul a
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext v
    simp [ridgeGradient, A, InnerProductSpace.toDual_apply_apply]
    ring

lemma ridge_support {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (e x₀ x y : E) :
    ridge a b e x₀ x + ⟪ridgeGradient a b e x₀ x, y - x⟫ ≤ ridge a b e x₀ y := by
  have h := mul_le_mul_of_nonneg_left
    (valley_support (⟪e, x - x₀⟫ - b) (⟪e, y - x₀⟫ - b)) ha
  simp only [ridge, ridgeGradient, real_inner_smul_left, inner_sub_right] at *
  linarith only [h]

lemma ridge_convex {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (e x₀ : E) :
    ConvexOn ℝ Set.univ (ridge a b e x₀) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  let z := u • x + v • y
  have h := add_le_add (mul_le_mul_of_nonneg_left (ridge_support ha b e x₀ z x) hu)
    (mul_le_mul_of_nonneg_left (ridge_support ha b e x₀ z y) hv)
  have hi : u * ⟪ridgeGradient a b e x₀ z, x - z⟫ +
      v * ⟪ridgeGradient a b e x₀ z, y - z⟫ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have he : u • (x - z) + v • (y - z) = 0 := by
      rw [smul_sub, smul_sub]
      rw [show u • x - u • z + (v • y - v • z) =
        z - (u • z + v • z) by dsimp [z]; abel, ← add_smul, huv, one_smul, sub_self]
    rw [he, inner_zero_right]
  change ridge a b e x₀ z ≤ u * ridge a b e x₀ x + v * ridge a b e x₀ y
  nlinarith only [h, hi, congrArg (fun w : ℝ => w * ridge a b e x₀ z) huv]

end LongTails.Proofs.BlumGladyshevValley
