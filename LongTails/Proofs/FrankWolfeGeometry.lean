import LongTails.Setups.UniformlyConvexHolder
import LongTails.Proofs.FrankWolfeDescent

open Set InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace LongTails.Setups.UniformlyConvexHolder.UniformlyConvexSet

omit [CompleteSpace E] in
lemma convex {C : Set E} {a q : ℝ}
    (hC : UniformlyConvexSet C a q) : Convex ℝ C := by
  intro x hx y hy t s ht hs hts
  have h := hC x hx y hy t ⟨ht, by linarith⟩ 0 (by simp)
  have heq : 1 - t = s := by linarith
  simpa [heq] using h

end LongTails.Setups.UniformlyConvexHolder.UniformlyConvexSet

namespace OracleTemplate.FrankWolfe

open LongTails.Setups.UniformlyConvexHolder

omit [CompleteSpace E] in
lemma uniformly_convex_gap {C : Set E} {a q : ℝ} (hC : UniformlyConvexSet C a q)
    {x atom g : E} (hx : x ∈ C) (ha : atom ∈ C)
    (hlmo : ∀ y ∈ C, ⟪g, atom⟫ ≤ ⟪g, y⟫) :
    a / 2 * ‖g‖ * ‖x - atom‖ ^ q ≤ ⟪g, x - atom⟫ := by
  by_cases hg : g = 0
  · simp [hg]
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let z := -(‖g‖⁻¹ • g)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']
  have hi : ⟪g, z⟫ = -‖g‖ := by
    dsimp [z]
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hc := hC x hx atom ha (1 / 2) (by constructor <;> norm_num) z hz
  have h := hlmo _ hc
  simp only [inner_add_right, inner_smul_right, hi, inner_sub_right] at h ⊢
  nlinarith

lemma gradient_growth {C : Set E} {f : E → ℝ} {g x y : E} {c r h : ℝ}
    (hc : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C) (hg : HasGradientAt f g x)
    (hgap : f x - f y = h) (hdist : ‖x - y‖ ≤ c * h ^ (1 / r)) :
    h ≤ ‖g‖ * c * h ^ (1 / r) := by
  have hs := convex_support_on hc hx hy hg
  have hn := real_inner_le_norm g (x - y)
  have hmult := mul_le_mul_of_nonneg_left hdist (norm_nonneg g)
  have hi : ⟪g, y - x⟫ = -⟪g, x - y⟫ := by
    rw [show y - x = -(x - y) by module, inner_neg_right]
  rw [hi] at hs
  nlinarith

omit [CompleteSpace E] in
lemma short_step_mem {C : Set E} (hC : Convex ℝ C) {x atom g : E} {L : ℝ}
    (hL : 0 < L) (hx : x ∈ C) (ha : atom ∈ C)
    (hlmo : ⟪g, atom⟫ ≤ ⟪g, x⟫) : shortStep L x g atom ∈ C := by
  by_cases h : atom = x
  · simp [shortStep, h, hx]
  have hd : 0 < L * ‖atom - x‖ ^ 2 := by
    exact mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)))
  have hgap : 0 ≤ ⟪g, x - atom⟫ := by rw [inner_sub_right]; linarith
  have hs := short_step_range hgap hd
  have hc := hC hx ha (sub_nonneg.mpr hs.2) hs.1 (by ring)
  convert hc using 1
  unfold shortStep
  module

lemma short_step_smooth_model {C : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : Convex ℝ C) (hL : 0 < L)
    (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x atom : E} (hx : x ∈ C) (ha : atom ∈ C)
    (hlmo : ⟪g x, atom⟫ ≤ ⟪g x, x⟫) :
    let gap := ⟪g x, x - atom⟫
    let curvature := L * ‖atom - x‖ ^ 2
    let γ := min 1 (gap / curvature)
    f (shortStep L x (g x) atom) ≤ f x - γ * gap + curvature / 2 * γ ^ 2 := by
  dsimp only
  have hmem := short_step_mem hc hL hx ha hlmo
  have hs := smooth_upper_bound_on hc hg hlip hx hmem
  simp only [shortStep, add_sub_cancel_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hi : ⟪g x, atom - x⟫ = -⟪g x, x - atom⟫ := by
    rw [show atom - x = -(x - atom) by module, inner_neg_right]
  rw [hi] at hs
  unfold shortStep
  convert hs using 1; ring

lemma short_step_objective_descent {C : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : Convex ℝ C) (hL : 0 < L)
    (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x atom : E} (hx : x ∈ C) (ha : atom ∈ C)
    (hlmo : ⟪g x, atom⟫ ≤ ⟪g x, x⟫) :
    f (shortStep L x (g x) atom) ≤ f x -
      min (⟪g x, x - atom⟫ / 2) (⟪g x, x - atom⟫ ^ 2 / (2 * (L * ‖atom - x‖ ^ 2))) := by
  by_cases h : atom = x
  · simp [h, shortStep]
  have hd : 0 < L * ‖atom - x‖ ^ 2 :=
    mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)))
  exact short_step_descent hd (short_step_smooth_model hc hL hg hlip hx ha hlmo)

end OracleTemplate.FrankWolfe
