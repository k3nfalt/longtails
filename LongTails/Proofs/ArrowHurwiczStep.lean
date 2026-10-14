import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ArrowHurwicz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsProx (X : Set E) (g : E → ℝ) (τ : ℝ) (u p : E) : Prop :=
  p ∈ X ∧ ∀ w ∈ X, τ * g p + ‖p - u‖ ^ 2 / 2 ≤ τ * g w + ‖w - u‖ ^ 2 / 2

lemma prox_vi {X : Set E} {g : E → ℝ} {τ : ℝ} {u p : E} (hX : Convex ℝ X)
    (hg : ConvexOn ℝ X g) (hp : IsProx X g τ u p) (hτ : 0 ≤ τ) {w : E} (hw : w ∈ X) :
    ⟪u - p, w - p⟫ ≤ τ * (g w - g p) := by
  obtain ⟨hpX, hmin⟩ := hp
  by_contra hcon
  rw [not_le] at hcon
  set δ := ⟪u - p, w - p⟫ - τ * (g w - g p) with hδ
  have hδpos : 0 < δ := by linarith
  set N := ‖w - p‖ ^ 2 with hN
  have hN0 : 0 ≤ N := sq_nonneg _
  set s := min 1 (δ / (N + 1)) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos hδpos (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsN : s * N < δ := by
    have h1 : s ≤ δ / (N + 1) := min_le_right _ _
    have h2 : s * (N + 1) ≤ δ := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ N + 1)
      rwa [div_mul_cancel₀ _ (by linarith : (N + 1) ≠ 0)] at this
    nlinarith
  have hws : (1 - s) • p + s • w ∈ X :=
    hX hpX hw (by linarith) hs0.le (by ring)
  have hm := hmin _ hws
  have hcv := hg.2 hpX hw (by linarith : (0 : ℝ) ≤ 1 - s) hs0.le (by ring)
  simp only [smul_eq_mul] at hcv
  have hvec : (1 - s) • p + s • w - u = (p - u) + s • (w - p) := by module
  have hnorm : ‖(1 - s) • p + s • w - u‖ ^ 2 =
      ‖p - u‖ ^ 2 + 2 * s * ⟪p - u, w - p⟫ + s ^ 2 * N := by
    rw [hvec, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, mul_pow]
    ring
  have hinner : ⟪p - u, w - p⟫ = -⟪u - p, w - p⟫ := by
    rw [← inner_neg_left, neg_sub]
  rw [hnorm, hinner] at hm
  have key : 0 ≤ τ * s * (g w - g p) - s * ⟪u - p, w - p⟫ + s ^ 2 * N / 2 := by
    have := mul_le_mul_of_nonneg_left hcv hτ
    nlinarith
  have key2 : 0 ≤ s * (τ * (g w - g p) - ⟪u - p, w - p⟫ + s * N / 2) := by
    nlinarith
  have key3 : 0 ≤ τ * (g w - g p) - ⟪u - p, w - p⟫ + s * N / 2 :=
    nonneg_of_mul_nonneg_right (by linarith) hs0
  nlinarith

lemma prox_step_bound {X : Set E} {g : E → ℝ} {τ M : ℝ} {x v p : E} (hX : Convex ℝ X)
    (hg : ConvexOn ℝ X g) (hgL : ∀ a ∈ X, ∀ b ∈ X, g a - g b ≤ M * ‖a - b‖)
    (hM : 0 ≤ M) (hτ : 0 ≤ τ) (hx : x ∈ X) (hp : IsProx X g τ (x - τ • v) p) :
    ‖p - x‖ ≤ τ * (‖v‖ + M) := by
  have hvi := prox_vi hX hg hp hτ hx
  have hpX := hp.1
  have hL := hgL x hx p hpX
  have hrw : ⟪x - τ • v - p, x - p⟫ = ‖x - p‖ ^ 2 - τ * ⟪v, x - p⟫ := by
    rw [show x - τ • v - p = (x - p) - τ • v by abel, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_smul_left]
  rw [hrw] at hvi
  have hcs : ⟪v, x - p⟫ ≤ ‖v‖ * ‖x - p‖ := real_inner_le_norm _ _
  have h1 : ‖x - p‖ ^ 2 ≤ τ * (‖v‖ + M) * ‖x - p‖ := by
    have := mul_le_mul_of_nonneg_left hcs hτ
    have := mul_le_mul_of_nonneg_left hL hτ
    nlinarith
  rw [norm_sub_rev]
  by_cases h0 : ‖x - p‖ = 0
  · rw [h0]; have : 0 ≤ ‖v‖ + M := by positivity
    positivity
  · have hpos : 0 < ‖x - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have := (mul_le_mul_iff_left₀ hpos).mp (by nlinarith : ‖x - p‖ * ‖x - p‖ ≤ (τ * (‖v‖ + M)) * ‖x - p‖)
    linarith


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma one_step_identity (K : E →L[ℝ] F) (adj : F → E) (hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫)
    (η : ℝ) (x0 x1 xh : E) (y0 y1 yh : F) :
    η * (⟪yh, K x1⟫ - ⟪y1, K xh⟫) + ⟪x0 - η • adj y0 - x1, x1 - xh⟫ +
        ⟪y0 + η • K x1 - y1, y1 - yh⟫ =
      (‖x0 - xh‖ ^ 2 / 2 + ‖y0 - yh‖ ^ 2 / 2 - η / 2 * ⟪y0, K x0⟫ + η * ⟪y0, K xh⟫) -
        (‖x1 - xh‖ ^ 2 / 2 + ‖y1 - yh‖ ^ 2 / 2 - η / 2 * ⟪y1, K x1⟫ + η * ⟪y1, K xh⟫) +
        (⟪x0 - η • adj y0 - x1, x1 - x0⟫ + ⟪y0 + η • K x1 - y1, y1 - y0⟫) / 2 := by
  have e1 : ⟪adj y0, x1⟫ = ⟪y0, K x1⟫ := hadj _ _
  have e2 : ⟪adj y0, xh⟫ = ⟪y0, K xh⟫ := hadj _ _
  have e3 : ⟪adj y0, x0⟫ = ⟪y0, K x0⟫ := hadj _ _
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, e1, e2, e3]
  rw [real_inner_comm x0 x1, real_inner_comm xh x1, real_inner_comm xh x0,
    real_inner_comm y0 y1, real_inner_comm yh y1, real_inner_comm yh y0,
    real_inner_comm (K x1) y1, real_inner_comm (K x1) yh, real_inner_comm (K x1) y0]
  ring

lemma friction_identity (K : E →L[ℝ] F) (adj : F → E) (hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫)
    (η : ℝ) (xm x0 x1 : E) (ym y0 y1 : F) :
    ⟪(x0 - η • adj y0 - x1) - (xm - η • adj ym - x0), x1 - x0⟫ +
        ⟪(y0 + η • K x1 - y1) - (ym + η • K x0 - y0), y1 - y0⟫ =
      (‖x0 - xm‖ ^ 2 + ‖y0 - ym‖ ^ 2) / 2 - (‖x1 - x0‖ ^ 2 + ‖y1 - y0‖ ^ 2) / 2 -
        ‖(x1 - x0) - (x0 - xm)‖ ^ 2 / 2 - ‖(y1 - y0) - (y0 - ym)‖ ^ 2 / 2 +
        η * ⟪K (x1 - x0), (y1 - y0) - (y0 - ym)⟫ := by
  have a1 : ⟪adj y0, x1⟫ = ⟪y0, K x1⟫ := hadj _ _
  have a2 : ⟪adj y0, x0⟫ = ⟪y0, K x0⟫ := hadj _ _
  have a3 : ⟪adj ym, x1⟫ = ⟪ym, K x1⟫ := hadj _ _
  have a4 : ⟪adj ym, x0⟫ = ⟪ym, K x0⟫ := hadj _ _
  simp only [map_sub, norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, a1, a2, a3, a4]
  rw [real_inner_comm y1 (K x1), real_inner_comm y1 (K x0), real_inner_comm y0 (K x1),
    real_inner_comm y0 (K x0), real_inner_comm ym (K x1), real_inner_comm ym (K x0)]
  linarith [real_inner_comm x0 x1, real_inner_comm xm x1, real_inner_comm xm x0,
    real_inner_comm y0 y1, real_inner_comm ym y1, real_inner_comm ym y0]


lemma adj_norm_le (K : E →L[ℝ] F) (adj : F → E) (hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫)
    {L : ℝ} (hK : ‖K‖ ≤ L) (y : F) : ‖adj y‖ ≤ L * ‖y‖ := by
  have hL : 0 ≤ L := le_trans (norm_nonneg _) hK
  have h1 : ‖adj y‖ ^ 2 ≤ L * ‖y‖ * ‖adj y‖ := by
    rw [← real_inner_self_eq_norm_sq, hadj]
    calc ⟪y, K (adj y)⟫ ≤ ‖y‖ * ‖K (adj y)‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (L * ‖adj y‖) := by
          gcongr
          exact le_trans (K.le_opNorm _) (by gcongr)
      _ = L * ‖y‖ * ‖adj y‖ := by ring
  by_cases h0 : ‖adj y‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖adj y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma inner_sub_self_le (a d : E) : ⟪a - d, d⟫ ≤ ‖a‖ ^ 2 / 4 := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have := real_inner_le_norm a d
  nlinarith [sq_nonneg (‖a‖ - 2 * ‖d‖)]

lemma young_cross (K : E →L[ℝ] F) (η : ℝ) (a : E) (b : F) :
    η * ⟪K a, b⟫ ≤ ‖b‖ ^ 2 / 2 + η ^ 2 / 2 * ‖K a‖ ^ 2 := by
  have h := sq_nonneg ‖b - η • K a‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_comm] at h
  linarith

lemma friction_bound (K : E →L[ℝ] F) (adj : F → E) (hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫)
    (g : E → ℝ) (h : F → ℝ) (η : ℝ) (xm x0 x1 : E) (ym y0 y1 : F)
    (hvx : ⟪xm - η • adj ym - x0, x1 - x0⟫ ≤ η * (g x1 - g x0))
    (hvy : ⟪ym + η • K x0 - y0, y1 - y0⟫ ≤ η * (h y1 - h y0)) :
    ⟪x0 - η • adj y0 - x1, x1 - x0⟫ + ⟪y0 + η • K x1 - y1, y1 - y0⟫ ≤
      (‖x0 - xm‖ ^ 2 + ‖y0 - ym‖ ^ 2) / 2 - (‖x1 - x0‖ ^ 2 + ‖y1 - y0‖ ^ 2) / 2 +
        η ^ 2 / 2 * ‖K (x1 - x0)‖ ^ 2 + η * (g x1 - g x0 + h y1 - h y0) := by
  have hid := friction_identity K adj hadj η xm x0 x1 ym y0 y1
  rw [inner_sub_left (x0 - η • adj y0 - x1) (xm - η • adj ym - x0),
    inner_sub_left (y0 + η • K x1 - y1) (ym + η • K x0 - y0)] at hid
  have hy := young_cross K η (x1 - x0) ((y1 - y0) - (y0 - ym))
  have hx := sq_nonneg ‖(x1 - x0) - (x0 - xm)‖
  linarith

lemma one_step_bound (K : E →L[ℝ] F) (adj : F → E) (hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫)
    (g : E → ℝ) (h : F → ℝ) (η : ℝ) (x0 x1 xh : E) (y0 y1 yh : F)
    (hvx : ⟪x0 - η • adj y0 - x1, xh - x1⟫ ≤ η * (g xh - g x1))
    (hvy : ⟪y0 + η • K x1 - y1, yh - y1⟫ ≤ η * (h yh - h y1)) :
    η * ((g x1 + ⟪yh, K x1⟫ - h yh) - (g xh + ⟪y1, K xh⟫ - h y1)) ≤
      (‖x0 - xh‖ ^ 2 / 2 + ‖y0 - yh‖ ^ 2 / 2 - η / 2 * ⟪y0, K x0⟫ + η * ⟪y0, K xh⟫) -
        (‖x1 - xh‖ ^ 2 / 2 + ‖y1 - yh‖ ^ 2 / 2 - η / 2 * ⟪y1, K x1⟫ + η * ⟪y1, K xh⟫) +
        (⟪x0 - η • adj y0 - x1, x1 - x0⟫ + ⟪y0 + η • K x1 - y1, y1 - y0⟫) / 2 := by
  have hid := one_step_identity K adj hadj η x0 x1 xh y0 y1 yh
  have e1 : ⟪x0 - η • adj y0 - x1, x1 - xh⟫ = -⟪x0 - η • adj y0 - x1, xh - x1⟫ := by
    rw [← inner_neg_right, neg_sub]
  have e2 : ⟪y0 + η • K x1 - y1, y1 - yh⟫ = -⟪y0 + η • K x1 - y1, yh - y1⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [e1, e2] at hid
  linarith

end OracleTemplate.ArrowHurwicz
