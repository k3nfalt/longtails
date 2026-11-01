import LongTails.Proofs.RadiusFreeSherpaBasic

set_option linter.unusedSectionVars false

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma accepted_potential {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) {A : ℝ} (hA : 0 ≤ A) {x v y : E} (hy : 0 < ‖g y‖) (hfy : f y ≤ f x)
    (hB : ⟪g y, y - v⟫ ≤ ‖g y‖ ^ 2 / (16 * localCurvature L0 L1 ‖g y‖)) :
    (A + weight L0 L1 A ‖g y‖) *
        (f (y - (1 / (4 * localCurvature L0 L1 ‖g y‖)) • g y) - f u) +
      weight L0 L1 A ‖g y‖ ^ 2 * ‖g y‖ ^ 2 / 2 +
      ‖v - weight L0 L1 A ‖g y‖ • g y - u‖ ^ 2 / 2 ≤
    A * (f x - f u) + ‖v - u‖ ^ 2 / 2 := by
  have hL0 := H.L0_pos
  set L := localCurvature L0 L1 ‖g y‖ with hLdef
  set a := weight L0 L1 A ‖g y‖ with ha
  set φ := phiRatio L0 L1 ‖g y‖ with hφ
  have hL : 0 < L := localCurvature_pos hL0 hL1.le hy.le
  have hapos : 0 < a := weight_pos A hL0 hL1 hy
  have haeq : a ^ 2 = (A + a) / (7 * L) + a * φ := weight_eq hL0 hL1 hA hy
  have hφ0 : 0 ≤ φ := phiRatio_nonneg hL0 hL1 hy
  have hdesc : f (y - (1 / (4 * L)) • g y) ≤ f y - 5 * ‖g y‖ ^ 2 / (24 * L) :=
    descent_step H hL1 y
  have hphi : f y + ⟪g y, u - y⟫ + φ * ‖g y‖ ^ 2 ≤ f u := phi_inequality H hL1 y hy
  have hmin : f u ≤ f y := H.min (mem_univ y)
  have hdist : ‖v - a • g y - u‖ ^ 2 =
      ‖v - u‖ ^ 2 - 2 * a * ⟪g y, v - u⟫ + a ^ 2 * ‖g y‖ ^ 2 := by
    have e : v - a • g y - u = (v - u) - a • g y := by abel
    rw [e, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hapos,
      real_inner_smul_right, real_inner_comm]
    ring
  have hsplit : ⟪g y, v - u⟫ = ⟪g y, v - y⟫ + ⟪g y, y - u⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have hvy : ⟪g y, v - y⟫ = -⟪g y, y - v⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  have hyu : ⟪g y, y - u⟫ = -⟪g y, u - y⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  have hsupp : f y - f u + φ * ‖g y‖ ^ 2 ≤ ⟪g y, y - u⟫ := by rw [hyu]; linarith
  have hAa0 : 0 ≤ A + a := by linarith
  have hG2L : 0 ≤ ‖g y‖ ^ 2 / L := by positivity
  have h1 : (A + a) * (f (y - (1 / (4 * L)) • g y) - f u) ≤
      (A + a) * (f y - f u) - (A + a) * (‖g y‖ ^ 2 / L) * (5 / 24) := by
    have := mul_le_mul_of_nonneg_left hdesc hAa0
    have e : (A + a) * (5 * ‖g y‖ ^ 2 / (24 * L)) = (A + a) * (‖g y‖ ^ 2 / L) * (5 / 24) := by
      ring
    linarith
  have h2 : (A + a) * (f y - f u) ≤ A * (f x - f u) + a * (f y - f u) := by
    have := mul_le_mul_of_nonneg_left hfy hA
    linarith
  have h3 : ‖v - a • g y - u‖ ^ 2 / 2 ≤
      ‖v - u‖ ^ 2 / 2 + a * (‖g y‖ ^ 2 / L) * (1 / 16) - a * (f y - f u) - a * φ * ‖g y‖ ^ 2 +
        a ^ 2 * ‖g y‖ ^ 2 / 2 := by
    rw [hdist, hsplit, hvy]
    have hb := mul_le_mul_of_nonneg_left hB hapos.le
    have hs := mul_le_mul_of_nonneg_left hsupp hapos.le
    have e : a * (‖g y‖ ^ 2 / (16 * L)) = a * (‖g y‖ ^ 2 / L) * (1 / 16) := by ring
    linarith
  have h4 : a ^ 2 * ‖g y‖ ^ 2 = (A + a) * (‖g y‖ ^ 2 / L) * (1 / 7) + a * φ * ‖g y‖ ^ 2 := by
    rw [haeq]; ring
  have key : (A + a) * (‖g y‖ ^ 2 / L) * (1 / 16) + (A + a) * (‖g y‖ ^ 2 / L) * (1 / 7) ≤
      (A + a) * (‖g y‖ ^ 2 / L) * (5 / 24) := by
    have hc : (1 : ℝ) / 16 + 1 / 7 ≤ 5 / 24 := by norm_num
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hAa0 hG2L)
    linarith
  have haG : a * (‖g y‖ ^ 2 / L) * (1 / 16) ≤ (A + a) * (‖g y‖ ^ 2 / L) * (1 / 16) := by
    have : a ≤ A + a := by linarith
    have := mul_le_mul_of_nonneg_right this hG2L
    linarith
  linarith

structure Inv (f : E → ℝ) (u : E) (R : ℝ) (c : Core E) (S : ℝ) : Prop where
  A_nonneg : 0 ≤ c.A
  S_nonneg : 0 ≤ S
  potential : c.A * (f c.x - f u) + S / 2 + ‖c.v - u‖ ^ 2 / 2 ≤ R ^ 2 / 2
  x_dist : ‖c.x - u‖ ≤ R

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma Inv.v_dist {f : E → ℝ} {u : E} {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn f univ u) (h : Inv f u R c S) : ‖c.v - u‖ ≤ R := by
  have hgap : 0 ≤ f c.x - f u := sub_nonneg.mpr (hmin (mem_univ _))
  have hp := h.potential
  have hA := mul_nonneg h.A_nonneg hgap
  have hS := h.S_nonneg
  have hsq : ‖c.v - u‖ ^ 2 ≤ R ^ 2 := by linarith
  by_contra hcon
  push Not at hcon
  have : R ^ 2 < ‖c.v - u‖ ^ 2 := by nlinarith [norm_nonneg (c.v - u)]
  linarith

omit [CompleteSpace E] in
lemma Inv.segment_dist {f : E → ℝ} {u : E} {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn f univ u) (h : Inv f u R c S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖c.v + t • (c.x - c.v) - u‖ ≤ R := by
  have hv := h.v_dist hR hmin
  have hx := h.x_dist
  have he : c.v + t • (c.x - c.v) - u = (1 - t) • (c.v - u) + t • (c.x - u) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [he]
  calc ‖(1 - t) • (c.v - u) + t • (c.x - u)‖ ≤ ‖(1 - t) • (c.v - u)‖ + ‖t • (c.x - u)‖ :=
        norm_add_le _ _
    _ = (1 - t) * ‖c.v - u‖ + t * ‖c.x - u‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    _ ≤ (1 - t) * R + t * R := by
        gcongr
    _ = R := by ring

lemma accept_inv {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) {R : ℝ} {c : Core E} {S : ℝ} (hI : Inv f u R c S)
    {y : E} (hy : 0 < ‖g y‖) (hyd : ‖y - u‖ ≤ R) (hfy : f y ≤ f c.x)
    (hB : ⟪g y, y - c.v⟫ ≤ ‖g y‖ ^ 2 / (16 * localCurvature L0 L1 ‖g y‖)) :
    Inv f u R ⟨c.A + weight L0 L1 c.A ‖g y‖,
      y - (1 / (4 * localCurvature L0 L1 ‖g y‖)) • g y,
      c.v - weight L0 L1 c.A ‖g y‖ • g y⟩ (S + weight L0 L1 c.A ‖g y‖ ^ 2 * ‖g y‖ ^ 2) := by
  have hA := hI.A_nonneg
  have hpot := accepted_potential H hL1 hA (x := c.x) (v := c.v) hy hfy hB
  have hw := weight_pos c.A H.L0_pos hL1 hy
  refine ⟨add_nonneg hA hw.le, add_nonneg hI.S_nonneg (by positivity), ?_, ?_⟩
  · have := hI.potential
    simp only
    linarith
  · simp only
    exact (descent_dist H hL1 y).trans hyd

omit [CompleteSpace E] in
lemma accept_eq {L0 L1 : ℝ} (c : Core E) (y gy : E) :
    accept L0 L1 c y gy = .queryX ⟨c.A + weight L0 L1 c.A ‖gy‖,
      y - (1 / (4 * localCurvature L0 L1 ‖gy‖)) • gy, c.v - weight L0 L1 c.A ‖gy‖ • gy⟩ := rfl

end OracleTemplate.RadiusFreeSherpa
