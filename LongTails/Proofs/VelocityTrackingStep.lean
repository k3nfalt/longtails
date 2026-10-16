import LongTails.Proofs.GdConvex
import LongTails.Proofs.LinearDecaySgdStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.VelocityTracking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lyap (p w : E) : ℝ := ‖p‖ ^ 2 - 3 * ⟪p, w⟫ + 6 * ‖w‖ ^ 2

lemma lyap_contract {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (p w G : E)
    (h1 : s * ‖p‖ ^ 2 ≤ ⟪G, p⟫) (h2 : 2 * ‖G‖ ^ 2 ≤ ⟪G, p⟫) :
    lyap (p + s • w - (1 + s / 4) • G) (w - (1 / 4 : ℝ) • G) ≤ (1 - s / 8) * lyap p w := by
  have q1 : 0 ≤ ‖p - w‖ ^ 2 := sq_nonneg _
  have q2 : 0 ≤ ‖w + (4 / 23 : ℝ) • G‖ ^ 2 := sq_nonneg _
  have q3 : 0 ≤ ‖p - (13 / 15 : ℝ) • w‖ ^ 2 := sq_nonneg _
  have q4 : 0 ≤ ‖w + (90 / 251 : ℝ) • G‖ ^ 2 := sq_nonneg _
  have q5 : 0 ≤ ‖G‖ ^ 2 := sq_nonneg _
  simp only [lyap, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at *
  have e1 : ⟪w, p⟫ = ⟪p, w⟫ := real_inner_comm _ _
  have e2 : ⟪G, w⟫ = ⟪w, G⟫ := real_inner_comm _ _
  have e3 : ⟪p, G⟫ = ⟪G, p⟫ := real_inner_comm _ _
  have hq0 : 0 ≤ 13 / 16 * ⟪p, p⟫ - 13 / 8 * ⟪p, w⟫ + 9 / 4 * ⟪w, w⟫ + 1 / 2 * ⟪w, G⟫ +
      3 / 16 * ⟪G, G⟫ := by nlinarith
  have hqh : 0 ≤ 15 / 16 * ⟪p, p⟫ - 13 / 8 * ⟪p, w⟫ + 7 / 4 * ⟪w, w⟫ + 3 / 4 * ⟪w, G⟫ +
      5 / 32 * ⟪G, G⟫ := by nlinarith
  have hl1 : 0 ≤ 15 / 16 + s / 4 := by positivity
  have hl2 : 0 ≤ 5 / 16 + s / 4 := by positivity
  have hm : 0 ≤ s * (1 - 2 * s) := mul_nonneg hs.le (by linarith)
  nlinarith [mul_nonneg hl1 (sub_nonneg.mpr h1), mul_nonneg hl2 (sub_nonneg.mpr h2),
    mul_nonneg hm hq0, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * s ^ 2) hqh]

lemma lyap_eq (p w : E) : lyap p w = ‖p - (3 / 2 : ℝ) • w‖ ^ 2 + 15 / 4 * ‖w‖ ^ 2 := by
  simp only [lyap, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm p w]
  ring

lemma lyap_nonneg (p w : E) : 0 ≤ lyap p w := by
  rw [lyap_eq]
  positivity

lemma norm_sq_le_lyap (p w : E) : ‖p‖ ^ 2 ≤ 2 * lyap p w := by
  have h : 0 ≤ ‖p - (3 : ℝ) • w‖ ^ 2 := sq_nonneg _
  have h' : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  simp only [lyap, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm p w] at *
  nlinarith

lemma lyap_le (p w : E) : lyap p w ≤ 5 / 2 * ‖p‖ ^ 2 + 15 / 2 * ‖w‖ ^ 2 := by
  have h : 0 ≤ ‖p + w‖ ^ 2 := sq_nonneg _
  simp only [lyap, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_comm p w] at *
  nlinarith

lemma lyap_add_smul (a b n : E) (c d : ℝ) :
    lyap (a + c • n) (b + d • n) = lyap a b +
      ⟪(2 * c - 3 * d) • a + (12 * d - 3 * c) • b, n⟫ +
        (c ^ 2 - 3 * c * d + 6 * d ^ 2) * ‖n‖ ^ 2 := by
  simp only [lyap, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_comm a n, real_inner_comm b n]
  ring

lemma lyap_young {η : ℝ} (hη : 0 < η) (a b c d : E) :
    lyap (a + c) (b + d) ≤ (1 + η) * lyap a b + (1 + η⁻¹) * lyap c d := by
  have h := lyap_nonneg (η • a - c) (η • b - d)
  have hexp : lyap (η • a - c) (η • b - d) =
      η ^ 2 * lyap a b - η * (lyap (a + c) (b + d) - lyap a b - lyap c d) + lyap c d := by
    simp only [lyap, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      real_inner_comm a c, real_inner_comm b c, real_inner_comm b d]
    ring
  rw [hexp] at h
  have hc := lyap_nonneg c d
  have key : η * lyap (a + c) (b + d) ≤ η * ((1 + η) * lyap a b + (1 + η⁻¹) * lyap c d) := by
    have : η * ((1 + η) * lyap a b + (1 + η⁻¹) * lyap c d) =
        η * lyap a b + η ^ 2 * lyap a b + η * lyap c d + lyap c d := by
      field_simp
      ring
    rw [this]
    linarith
  exact le_of_mul_le_mul_left key hη

variable [CompleteSpace E]

lemma sector {f : E → ℝ} {μ L γ : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hγ : 0 < γ)
    (hγL : γ * L ≤ 1 / 2) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) {u : E} (hm : IsMinOn f univ u)
    (y : E) :
    γ * μ * ‖y - u‖ ^ 2 ≤ ⟪γ • gradient f y, y - u⟫ ∧
      2 * ‖γ • gradient f y‖ ^ 2 ≤ ⟪γ • gradient f y, y - u⟫ := by
  have hzero : gradient f u = 0 := by
    have hd := Gradient.descent hL hg hlip u
    have hh := hm (show u - (1 / L) • gradient f u ∈ univ from trivial)
    change f u ≤ f (u - (1 / L) • gradient f u) at hh
    have hsq : ‖gradient f u‖ ^ 2 / (2 * L) ≤ 0 := by linarith
    have hz := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hsq
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient f u)])
  have hconv : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩
    have h1 := hsc (a • x + b • z) x
    have h2 := hsc (a • x + b • z) z
    have hq1 : 0 ≤ μ / 2 * ‖x - (a • x + b • z)‖ ^ 2 := by positivity
    have hq2 : 0 ≤ μ / 2 * ‖z - (a • x + b • z)‖ ^ 2 := by positivity
    have hlin : a * ⟪gradient f (a • x + b • z), x - (a • x + b • z)⟫ +
        b * ⟪gradient f (a • x + b • z), z - (a • x + b • z)⟫ = 0 := by
      rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
      have : a • (x - (a • x + b • z)) + b • (z - (a • x + b • z)) = (0 : E) := by
        rw [show b = 1 - a by linarith]
        module
      rw [this, inner_zero_right]
    have k1 := mul_le_mul_of_nonneg_left h1 ha
    have k2 := mul_le_mul_of_nonneg_left h2 hb
    have k3 := mul_nonneg ha hq1
    have k4 := mul_nonneg hb hq2
    have hfm : a * f (a • x + b • z) + b * f (a • x + b • z) = f (a • x + b • z) := by
      rw [← add_mul, hab, one_mul]
    simp only [smul_eq_mul]
    nlinarith
  have hi : ⟪gradient f y, u - y⟫ = -⟪gradient f y, y - u⟫ := by
    rw [← inner_neg_right, neg_sub]
  have hnorm : ‖u - y‖ = ‖y - u‖ := norm_sub_rev _ _
  have hs1 := hsc y u
  have hs2 := hsc u y
  simp only [hzero, inner_zero_left, hi, hnorm] at hs1 hs2
  have hc1 := SampledConvex.cocoercive hL hconv hg hlip y u
  have hc2 := SampledConvex.cocoercive hL hconv hg hlip u y
  simp only [hzero, sub_zero, inner_zero_left, zero_sub, norm_neg, hi] at hc1 hc2
  have hco : ‖gradient f y‖ ^ 2 ≤ L * ⟪gradient f y, y - u⟫ := by nlinarith
  have hpos : 0 ≤ ⟪gradient f y, y - u⟫ := by nlinarith [sq_nonneg (‖y - u‖)]
  rw [inner_smul_left, norm_smul, RCLike.conj_to_real, Real.norm_eq_abs, abs_of_pos hγ]
  constructor
  · nlinarith
  · have hγ2 : 2 * γ ^ 2 * ‖gradient f y‖ ^ 2 ≤ 2 * γ ^ 2 * (L * ⟪gradient f y, y - u⟫) :=
      mul_le_mul_of_nonneg_left hco (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hγL (mul_nonneg hγ.le hpos)]

end OracleTemplate.VelocityTracking
