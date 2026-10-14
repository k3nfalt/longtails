import LongTails.Proofs.GdConvex
import LongTails.Proofs.Clipping

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.GapStrongGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma raw_clip_residual {M : ℝ} (hM : 0 < M) (v : E) :
    ‖v - clip M v‖ ≤ ‖v‖ ^ 2 / M := by
  by_cases hv : ‖v‖ ≤ M
  · rw [clip_eq_self hv, sub_self, norm_zero]
    positivity
  · rw [clip_residual_norm hM.le, max_eq_right (by linarith : 0 ≤ ‖v‖ - M)]
    apply (le_div_iff₀ hM).mpr
    have hn := mul_le_mul_of_nonneg_left (le_of_not_ge hv) (norm_nonneg v)
    nlinarith [sq_nonneg M]

variable [CompleteSpace E]

lemma coupling_support {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (x z u : E) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    (A + a) * (f y - f u) ≤ A * (f x - f u) + a * ⟪g y, z - u⟫ := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  have hAa : 0 < A + a := by positivity
  have hx := mul_le_mul_of_nonneg_left (Gradient.convex_support hc hg y x) hA
  have hu := mul_le_mul_of_nonneg_left (Gradient.convex_support hc hg y u) ha.le
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hAa.ne'] <;> ring
  have hi := congrArg (fun v => ⟪g y, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hn : ⟪g y, u - z⟫ = -⟪g y, z - u⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [hn] at hi
  change (A + a) * (f y - f u) ≤ _
  nlinarith only [hx, hu, hi]

lemma coupled_step {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {A a η H : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (x z u h : E)
    (hs : let y := (A / (A + a)) • x + (a / (A + a)) • z
      f (y - η • h) ≤ f y - η * ⟪g y, h⟫ + H * η ^ 2 * ‖h‖ ^ 2) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    (A + a) * (f (y - η • h) - f u) + ‖z - a • h - u‖ ^ 2 / 2 ≤
      A * (f x - f u) + ‖z - u‖ ^ 2 / 2 -
        (A + a) * η * ⟪g y, h⟫ +
        ((A + a) * H * η ^ 2 + a ^ 2 / 2) * ‖h‖ ^ 2 +
        a * ⟪g y - h, z - u⟫ := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  have hb := coupling_support hc hg hA ha x z u
  change (A + a) * (f y - f u) ≤ _ at hb
  change f (y - η • h) ≤ f y - η * ⟪g y, h⟫ + H * η ^ 2 * ‖h‖ ^ 2 at hs
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ A + a by positivity)
  have he : z - a • h - u = (z - u) - a • h := by module
  change (A + a) * (f (y - η • h) - f u) + ‖z - a • h - u‖ ^ 2 / 2 ≤ _
  rw [he, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left]
  rw [real_inner_comm (z - u) h]
  simp only [inner_sub_left, inner_sub_right] at *
  nlinarith only [hb, hs']

end OracleTemplate.GapStrongGrowth
