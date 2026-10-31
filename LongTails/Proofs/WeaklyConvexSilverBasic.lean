import LongTails.Proofs.SilverTrace
import LongTails.Proofs.LinearDecaySgdStep

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeaklyConvexSilverBasic

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma shifted_gradient [CompleteSpace E] {f : E → ℝ} {g : E → E} {ρ : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x) (x : E) :
    HasGradientAt (fun z => f z + ρ / 2 * ‖z‖ ^ 2) (g x + ρ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hg x).hasFDerivAt.add ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (ρ / 2))
    using 1
  ext v
  simp
  ring

lemma shifted_defect {A X : E} {F ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ‖A + ρ • X‖ ^ 2 ≤ 2 * (1 + ρ) * (F + ρ / 2 * ‖X‖ ^ 2)) :
    -ρ * ‖X - A‖ ^ 2 ≤ 2 * F - ‖A‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_of_nonneg hρ, inner_smul_right] at h
  rw [norm_sub_sq_real]
  have hx : 0 ≤ ‖X‖ ^ 2 - 2 * ⟪X, A⟫ + ‖A‖ ^ 2 := by
    have := sq_nonneg ‖X - A‖
    rw [norm_sub_sq_real] at this
    linarith
  have hc : ⟪A, X⟫ = ⟪X, A⟫ := real_inner_comm _ _
  rw [hc] at h
  nlinarith [mul_nonneg (mul_nonneg hρ hρ) hx, hρ]

lemma weak_defect [CompleteSpace E] {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hc : ConvexOn ℝ univ (fun z => f z + ρ / 2 * ‖z‖ ^ 2))
    (hg : ∀ x, HasGradientAt f (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖) (u v : E) :
    -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v) := by
  have hl : ∀ x y, ‖(g x + ρ • x) - (g y + ρ • y)‖ ≤ (1 + ρ) * ‖x - y‖ := by
    intro x y
    have he : (g x + ρ • x) - (g y + ρ • y) = (g x - g y) + ρ • (x - y) := by module
    rw [he]
    calc ‖(g x - g y) + ρ • (x - y)‖ ≤ ‖g x - g y‖ + ‖ρ • (x - y)‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ + ρ * ‖x - y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hρ]
        linarith [hlip x y]
      _ = (1 + ρ) * ‖x - y‖ := by ring
  have hco := OracleTemplate.SampledConvex.cocoercive (by linarith : (0 : ℝ) < 1 + ρ)
    hc (shifted_gradient hg) hl u v
  have e1 : (g u + ρ • u) - (g v + ρ • v) = (g u - g v) + ρ • (u - v) := by module
  have e2 : f u + ρ / 2 * ‖u‖ ^ 2 - (f v + ρ / 2 * ‖v‖ ^ 2) - ⟪g v + ρ • v, u - v⟫ =
      (f u - f v - ⟪g v, u - v⟫) + ρ / 2 * ‖u - v‖ ^ 2 := by
    have h1 : ⟪v, u - v⟫ = ⟪u, v⟫ - ‖v‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
    rw [inner_add_left, real_inner_smul_left, h1, norm_sub_sq_real]
    ring
  have e3 : (u - g u) - (v - g v) = (u - v) - (g u - g v) := by module
  rw [e1] at hco
  change ‖(g u - g v) + ρ • (u - v)‖ ^ 2 ≤ 2 * (1 + ρ) *
    (f u + ρ / 2 * ‖u‖ ^ 2 - (f v + ρ / 2 * ‖v‖ ^ 2) - ⟪g v + ρ • v, u - v⟫) at hco
  rw [e2] at hco
  rw [e3]
  have := shifted_defect hρ hco
  simp only [defect]
  linarith

lemma reference_identity (f : E → ℝ) (g : E → E) (hs : List ℝ) (x z : E) :
    primitive f g hs x + defectSum f g z hs x =
      ‖x - (z - g z)‖ ^ 2 - ‖run g hs x - (z - g z)‖ ^ 2 -
        hs.sum * (hs.sum + 1) * ‖g (run g hs x)‖ ^ 2 -
        2 * hs.sum * (f (run g hs x) - f z) - hs.sum * ‖g z‖ ^ 2 := by
  rw [defectSum_formula f g z x]
  simp only [primitive, history, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_comm z x, real_inner_comm (run g hs x) x, real_inner_comm (run g hs x) z,
    real_inner_comm (g z) x, real_inner_comm (g z) z, real_inner_comm (g z) (run g hs x)]
  ring

lemma defectSum_weak {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v))
    (z : E) (hs : List ℝ) (x : E) (hw : ∀ h ∈ hs, 0 ≤ h) (M : ℝ)
    (hM : ∀ w ∈ nodes g hs x, ‖(z - g z) - (w - g w)‖ ^ 2 ≤ M) :
    -hs.sum * (ρ * M) ≤ defectSum f g z hs x :=
  defectSum_lower f g z hs x (ρ * M) hw fun w hm => by
    have := hD z w
    nlinarith [mul_le_mul_of_nonneg_left (hM w hm) hρ]


end LongTails.Proofs.WeaklyConvexSilverBasic
