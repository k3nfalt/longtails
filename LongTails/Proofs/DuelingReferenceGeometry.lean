import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.DuelingReferenceGeometry

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma chord_curvature {f : E → ℝ} {z e g : E} {s μ : ℝ} (he : ‖e‖ = 1)
    (hp : f z + ⟪g, (s • e)⟫ + μ / 2 * ‖s • e‖ ^ 2 ≤ f (z + s • e))
    (hm : f z + ⟪g, -(s • e)⟫ + μ / 2 * ‖-(s • e)‖ ^ 2 ≤ f (z - s • e)) :
    μ * s ^ 2 ≤ f (z + s • e) + f (z - s • e) - 2 * f z := by
  simp only [inner_neg_right, norm_neg, norm_smul, Real.norm_eq_abs, he, mul_one,
    sq_abs] at hp hm
  linarith

lemma reference_separation {a b c t u : ℝ} (h : 4 * u ≤ a + b - 2 * c) :
    u ≤ |t - a| ∨ u ≤ |t - b| ∨ u ≤ |t - c| := by
  by_contra! hn
  obtain ⟨ha, _⟩ := abs_lt.mp hn.1
  obtain ⟨hb, _⟩ := abs_lt.mp hn.2.1
  obtain ⟨_, hc⟩ := abs_lt.mp hn.2.2
  linarith

lemma reference_slope {a b c t u m : ℝ} {k : ℕ} {w : ℝ → ℝ}
    (h : 4 * u ≤ a + b - 2 * c) (hu : 0 ≤ u) (hm : 0 ≤ m)
    (ha : m * |t - a| ^ k ≤ w (t - a)) (hb : m * |t - b| ^ k ≤ w (t - b))
    (hc : m * |t - c| ^ k ≤ w (t - c)) :
    m * u ^ k / 3 ≤ (w (t - a) + w (t - b) + w (t - c)) / 3 := by
  have hnon (v : ℝ) : 0 ≤ m * |t - v| ^ k := by positivity
  have hbound (v : ℝ) (hv : u ≤ |t - v|) : m * u ^ k ≤ m * |t - v| ^ k := by gcongr
  rcases reference_separation (t := t) h with h₁ | h₂ | h₃
  · linarith [hbound a h₁, hnon b, hnon c]
  · linarith [hbound b h₂, hnon a, hnon c]
  · linarith [hbound c h₃, hnon a, hnon b]

end LongTails.Proofs.DuelingReferenceGeometry
