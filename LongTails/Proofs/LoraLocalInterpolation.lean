import LongTails.Proofs.LinearDecaySgdStep
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LoraLocalInterpolation

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma remainder_inner_bound {v r : F} {M d : ℝ}
    (hM : 0 ≤ M) (hv : ‖v‖ ≤ M) (hr : ‖r‖ ≤ d ^ 2 / 2) :
    ⟪v, r⟫ ≤ M * d ^ 2 / 2 := by
  calc
    ⟪v, r⟫ ≤ ‖v‖ * ‖r‖ := real_inner_le_norm _ _
    _ ≤ M * (d ^ 2 / 2) := mul_le_mul hv hr (norm_nonneg _) hM
    _ = M * d ^ 2 / 2 := by ring

lemma pullback_cocoercive [CompleteSpace F] {f : F → ℝ} {G : F → F} {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hc : ConvexOn ℝ univ f)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖)
    (p : E → F) (u v : E) (D : E →L[ℝ] F) (g : E)
    (hpair : ⟪g, u - v⟫ = ⟪G (p v), D (u - v)⟫)
    (hbound : ‖G (p v)‖ ≤ M)
    (hrem : ‖p u - p v - D (u - v)‖ ≤ ‖u - v‖ ^ 2 / 2) :
    ‖G (p u) - G (p v)‖ ^ 2 ≤
      2 * ρ * (f (p u) - f (p v) - ⟪g, u - v⟫ + M * ‖u - v‖ ^ 2 / 2) := by
  have hco := OracleTemplate.SampledConvex.cocoercive hρ hc hG hlip (p u) (p v)
  have hneg : ‖-G (p v)‖ ≤ M := by simpa only [norm_neg] using hbound
  have hi := remainder_inner_bound hM hneg hrem
  rw [inner_neg_left, inner_sub_right, ← hpair] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (le_of_lt hρ)
  nlinarith

lemma squared_gradient_bound {a b d R M : ℝ}
    (hb : 0 ≤ b) (h : b ≤ R * a + M * d) :
    b ^ 2 ≤ 2 * R ^ 2 * a ^ 2 + 2 * M ^ 2 * d ^ 2 := by
  have hs : b ^ 2 ≤ (R * a + M * d) ^ 2 :=
    pow_le_pow_left₀ hb h 2
  nlinarith [sq_nonneg (R * a - M * d)]

lemma interpolation_defect {a b d R M ρ e : ℝ}
    (hb : 0 ≤ b)
    (hco : a ^ 2 ≤ 2 * ρ * (e + M * d ^ 2 / 2))
    (hgrad : b ≤ R * a + M * d) :
    b ^ 2 ≤ 4 * ρ * R ^ 2 * e + (2 * ρ * R ^ 2 * M + 2 * M ^ 2) * d ^ 2 := by
  have hbnd := squared_gradient_bound hb hgrad
  have hscaled := mul_le_mul_of_nonneg_left hco (show 0 ≤ 2 * R ^ 2 by positivity)
  nlinarith

lemma adjoint_gradient_difference [CompleteSpace E] [CompleteSpace F]
    (D₁ D₂ : E →L[ℝ] F) (G₁ G₂ : F) {R M d : ℝ}
    (hR : ‖D₁‖ ≤ R) (hD : ‖D₁ - D₂‖ ≤ d)
    (hM : ‖G₂‖ ≤ M) (hd : 0 ≤ d) :
    ‖D₁.adjoint G₁ - D₂.adjoint G₂‖ ≤ R * ‖G₁ - G₂‖ + M * d := by
  have he : D₁.adjoint G₁ - D₂.adjoint G₂ =
      D₁.adjoint (G₁ - G₂) + (D₁ - D₂).adjoint G₂ := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  calc
    ‖D₁.adjoint (G₁ - G₂) + (D₁ - D₂).adjoint G₂‖ ≤
        ‖D₁.adjoint (G₁ - G₂)‖ + ‖(D₁ - D₂).adjoint G₂‖ := norm_add_le _ _
    _ ≤ ‖D₁.adjoint‖ * ‖G₁ - G₂‖ + ‖(D₁ - D₂).adjoint‖ * ‖G₂‖ :=
      add_le_add (D₁.adjoint.le_opNorm _) ((D₁ - D₂).adjoint.le_opNorm _)
    _ = ‖D₁‖ * ‖G₁ - G₂‖ + ‖D₁ - D₂‖ * ‖G₂‖ := by
      simp only [LinearIsometryEquiv.norm_map]
    _ ≤ R * ‖G₁ - G₂‖ + d * M :=
      add_le_add (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
        (mul_le_mul hD hM (norm_nonneg _) hd)
    _ = R * ‖G₁ - G₂‖ + M * d := by ring

lemma pullback_interpolation [CompleteSpace E] [CompleteSpace F]
    {f : F → ℝ} {G : F → F} {ρ R M : ℝ}
    (hρ : 0 < ρ) (hc : ConvexOn ℝ univ f)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖)
    (p : E → F) (u v : E) (D₁ D₂ : E →L[ℝ] F)
    (hR : ‖D₁‖ ≤ R) (hD : ‖D₁ - D₂‖ ≤ ‖u - v‖)
    (hM : ‖G (p v)‖ ≤ M)
    (hrem : ‖p u - p v - D₂ (u - v)‖ ≤ ‖u - v‖ ^ 2 / 2) :
    ‖D₁.adjoint (G (p u)) - D₂.adjoint (G (p v))‖ ^ 2 ≤
      4 * ρ * R ^ 2 * (f (p u) - f (p v) - ⟪D₂.adjoint (G (p v)), u - v⟫) +
        (2 * ρ * R ^ 2 * M + 2 * M ^ 2) * ‖u - v‖ ^ 2 := by
  have hco := pullback_cocoercive hρ ((norm_nonneg _).trans hM) hc hG hlip p u v
    D₂ (D₂.adjoint (G (p v))) (D₂.adjoint_inner_left _ _) hM hrem
  have hd := adjoint_gradient_difference D₁ D₂ (G (p u)) (G (p v))
    hR hD hM (norm_nonneg _)
  exact interpolation_defect (norm_nonneg _) hco hd

end LongTails.Proofs.LoraLocalInterpolation
