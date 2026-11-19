import LongTails.Proofs.HiddenConvexGeometry
import Mathlib.Tactic

open scoped RealInnerProductSpace
open Metric

namespace LongTails.Proofs.FullRangeClip

open OracleTemplate.LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ballProj_variational (x0 w v : E) {r : ℝ} (hr : 0 ≤ r) (hv : ‖v - x0‖ ≤ r) :
    0 ≤ ⟪w - ballProj x0 r w, ballProj x0 r w - v⟫ := by
  unfold ballProj
  split_ifs with h
  · simp
  · push Not at h
    set d := w - x0 with hd
    have hdpos : 0 < ‖d‖ := lt_of_le_of_lt hr h
    have hne : ‖d‖ ≠ 0 := hdpos.ne'
    set s := r / ‖d‖ with hs
    have e1 : w - (x0 + s • d) = (1 - s) • d := by
      rw [hd, sub_smul, one_smul]
      abel
    have e2 : x0 + s • d - v = s • d - (v - x0) := by abel
    rw [e1, e2, inner_smul_left, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hsd : s * ‖d‖ = r := by rw [hs]; field_simp
    have hs1 : s ≤ 1 := by rw [hs]; exact (div_le_one hdpos).mpr h.le
    have hcs : ⟪d, v - x0⟫ ≤ ‖d‖ * ‖v - x0‖ := real_inner_le_norm _ _
    simp only [conj_trivial]
    have : 0 ≤ s * ‖d‖ ^ 2 - ⟪d, v - x0⟫ := by
      have h1 : s * ‖d‖ ^ 2 = r * ‖d‖ := by rw [← hsd]; ring
      rw [h1]
      nlinarith [mul_le_mul_of_nonneg_left hv hdpos.le]
    exact mul_nonneg (by linarith) this

lemma ballProj_nonexpansive (x0 w v : E) {r : ℝ} (hr : 0 ≤ r) :
    ‖ballProj x0 r w - ballProj x0 r v‖ ≤ ‖w - v‖ := by
  set a := ballProj x0 r w
  set b := ballProj x0 r v
  have ha : ‖a - x0‖ ≤ r := by
    have := ballProj_mem x0 w hr
    rwa [mem_closedBall, dist_eq_norm] at this
  have hb : ‖b - x0‖ ≤ r := by
    have := ballProj_mem x0 v hr
    rwa [mem_closedBall, dist_eq_norm] at this
  have h1 := ballProj_variational x0 w b hr hb
  have h2 := ballProj_variational x0 v a hr ha
  have hid : ‖a - b‖ ^ 2 ≤ ⟪w - v, a - b⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have e1 : ⟪w - a, a - b⟫ = ⟪w, a - b⟫ - ⟪a, a - b⟫ := inner_sub_left _ _ _
    have e2 : ⟪v - b, b - a⟫ = -(⟪v, a - b⟫ - ⟪b, a - b⟫) := by
      rw [inner_sub_left, ← neg_sub a b, inner_neg_right, inner_neg_right]
      ring
    have e3 : ⟪w - v, a - b⟫ = ⟪w, a - b⟫ - ⟪v, a - b⟫ := inner_sub_left _ _ _
    have e4 : ⟪a - b, a - b⟫ = ⟪a, a - b⟫ - ⟪b, a - b⟫ := inner_sub_left _ _ _
    linarith
  have hcs := real_inner_le_norm (w - v) (a - b)
  by_cases h0 : ‖a - b‖ = 0
  · rw [h0]
    exact norm_nonneg _
  · have hp : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma clip_nonexpansive {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (x0 : E) {r : ℝ}
    (hr : 0 ≤ r) (x y : E) :
    ‖T (ballProj x0 r x) - T (ballProj x0 r y)‖ ≤ ‖x - y‖ :=
  (hT _ _).trans (ballProj_nonexpansive x0 x y hr)

lemma ballProj_of_mem (x0 w : E) {r : ℝ} (h : ‖w - x0‖ ≤ r) : ballProj x0 r w = w := by
  simp [ballProj, h]

lemma clip_fixed {T : E → E} {x0 u : E} {r : ℝ} (hu : ‖u - x0‖ ≤ r) (hfix : T u = u) :
    T (ballProj x0 r u) = u := by
  rw [ballProj_of_mem x0 u hu, hfix]

lemma clip_terminal {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (x0 u z : E) {r : ℝ}
    (hr : 0 < r) (hu : ‖u - x0‖ ≤ r / 2) (hfix : T u = u) :
    ‖T (ballProj x0 r z) - ballProj x0 r z‖ ≤ 4 * ‖T (ballProj x0 r z) - z‖ := by
  set y := ballProj x0 r z
  set p := z - y
  set w := T y - z
  have hmargin : r / 2 * ‖p‖ ≤ ⟪p, y - u⟫ := ballProj_margin x0 z u hr.le hu
  have hyb : ‖y - x0‖ ≤ r := by
    have := ballProj_mem x0 z hr.le
    rwa [mem_closedBall, dist_eq_norm] at this
  have hyu : ‖y - u‖ ≤ 3 * r / 2 := by
    have := norm_sub_le_norm_sub_add_norm_sub y x0 u
    rw [norm_sub_rev x0 u] at this
    linarith
  have hex : T y - y = p + w := by simp only [p, w]; abel
  have hn : ‖(y - u) + (p + w)‖ ≤ ‖y - u‖ := by
    have e : (y - u) + (p + w) = T y - T u := by rw [hfix, ← hex]; abel
    rw [e]
    exact hT _ _
  have hsq : ‖(y - u) + (p + w)‖ ^ 2 ≤ ‖y - u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  rw [norm_add_sq_real] at hsq
  have hin : ⟪y - u, p + w⟫ = ⟪p, y - u⟫ + ⟪y - u, w⟫ := by
    rw [inner_add_right, real_inner_comm]
  have hcs : -(‖y - u‖ * ‖w‖) ≤ ⟪y - u, w⟫ := by
    have := real_inner_le_norm (y - u) (-w)
    rw [inner_neg_right, norm_neg] at this
    linarith
  have hsn := sq_nonneg ‖p + w‖
  have hp : r / 2 * ‖p‖ ≤ 3 * r / 2 * ‖w‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hyu (norm_nonneg w)]
  have hp2 : ‖p‖ ≤ 3 * ‖w‖ := by
    have : r / 2 * ‖p‖ ≤ r / 2 * (3 * ‖w‖) := by nlinarith
    exact (mul_le_mul_iff_right₀ (by positivity)).mp this
  rw [hex]
  have := norm_add_le p w
  linarith

end LongTails.Proofs.FullRangeClip
