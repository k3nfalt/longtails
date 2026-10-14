import LongTails.Proofs.TwoSidedPLStep

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.TwoSidedPL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma pl_scalar {L τ μx μy A B k n1 a1 a2 a3 R : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hμx : 0 < μx) (hμxL : μx ≤ L) (hμy : 0 < μy) (hμyL : μy ≤ L) (hR : 0 ≤ R) (ha1 : 0 ≤ a1)
    (h1 : 2 * L * a1 ≤ A ^ 2) (h2 : 2 * μy * a2 ≤ B ^ 2)
    (h3 : μx * a3 ≤ μx * a2 + (L * μx + 2 * L ^ 2) * R ^ 2)
    (h4 : L * R ≤ 4 / 3 * A + L * τ * n1 + L * k) :
    μx * μy * τ * (a1 + a2 + a3) ≤
      2 ^ 18 * L * (τ / 3 * A ^ 2 + τ / 64 * B ^ 2 + L * τ * μy / 24576 * k ^ 2) +
        9 * L ^ 2 * τ ^ 3 * μy * n1 ^ 2 := by
  have q1 : μx * μy * τ * a1 ≤ L * τ / 2 * A ^ 2 := by
    have e1 : μx * μy * τ * a1 ≤ L * μy * τ * a1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hμxL hμy.le) hτ.le) ha1
    have e2 : L * μy * τ * a1 = μy * τ / 2 * (2 * L * a1) := by ring
    have e3 : μy * τ / 2 * (2 * L * a1) ≤ μy * τ / 2 * A ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e4 : μy * τ / 2 * A ^ 2 ≤ L * τ / 2 * A ^ 2 :=
      mul_le_mul_of_nonneg_right (by have := mul_le_mul_of_nonneg_right hμyL hτ.le; linarith)
        (sq_nonneg A)
    linarith
  have q2 : μx * μy * τ * a2 ≤ L * τ / 2 * B ^ 2 := by
    have e2 : μx * μy * τ * a2 = μx * τ / 2 * (2 * μy * a2) := by ring
    have e3 : μx * τ / 2 * (2 * μy * a2) ≤ μx * τ / 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e4 : μx * τ / 2 * B ^ 2 ≤ L * τ / 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_right (by have := mul_le_mul_of_nonneg_right hμxL hτ.le; linarith)
        (sq_nonneg B)
    linarith
  have hR2 : L ^ 2 * R ^ 2 ≤ 3 * (16 / 9 * A ^ 2 + L ^ 2 * τ ^ 2 * n1 ^ 2 + L ^ 2 * k ^ 2) := by
    have hLR : 0 ≤ L * R := by positivity
    have := pow_le_pow_left₀ hLR h4 2
    linarith [sq_nonneg (4 / 3 * A - L * τ * n1), sq_nonneg (4 / 3 * A - L * k),
      sq_nonneg (L * τ * n1 - L * k)]
  have q3 : μx * μy * τ * a3 ≤ L * τ / 2 * B ^ 2 + 3 * μy * τ * (L ^ 2 * R ^ 2) := by
    have e1 : μx * μy * τ * a3 = μy * τ * (μx * a3) := by ring
    have e2 : μy * τ * (μx * a3) ≤ μy * τ * (μx * a2 + (L * μx + 2 * L ^ 2) * R ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e3 : (L * μx + 2 * L ^ 2) * R ^ 2 ≤ 3 * (L ^ 2 * R ^ 2) := by
      have h0 : L * μx ≤ L * L := mul_le_mul_of_nonneg_left hμxL hL.le
      have := mul_le_mul_of_nonneg_right h0 (sq_nonneg R)
      linarith
    have e4 : μy * τ * ((L * μx + 2 * L ^ 2) * R ^ 2) ≤ μy * τ * (3 * (L ^ 2 * R ^ 2)) :=
      mul_le_mul_of_nonneg_left e3 (by positivity)
    have e5 : μy * τ * (μx * a2) = μx * μy * τ * a2 := by ring
    linarith
  have q4 : 3 * μy * τ * (L ^ 2 * R ^ 2) ≤
      3 * μy * τ * (3 * (16 / 9 * A ^ 2 + L ^ 2 * τ ^ 2 * n1 ^ 2 + L ^ 2 * k ^ 2)) :=
    mul_le_mul_of_nonneg_left hR2 (by positivity)
  have r1 : μy * τ * A ^ 2 ≤ L * τ * A ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμyL hτ.le) (sq_nonneg A)
  have r2 : 0 ≤ L * τ * A ^ 2 := by positivity
  have r3 : 0 ≤ L * τ * B ^ 2 := by positivity
  have r4 : 0 ≤ L ^ 2 * τ * μy * k ^ 2 := by positivity
  linarith

lemma ab_scalar {L τ μx μy A B k n1 b c Gy Gx : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hμx : 0 < μx) (hμxL : μx ≤ L) (hμy : 0 < μy) (hμyL : μy ≤ L) (hGy : 0 ≤ Gy) (hGx : 0 ≤ Gx)
    (h1 : 2 * μy * b ≤ Gy ^ 2) (h2 : 2 * μx * c ≤ Gx ^ 2) (h3 : Gy ≤ B + A)
    (h4 : Gx ≤ 5 / 3 * A + 2 * L * τ * n1 + 2 * L * k) :
    μx * μy * τ * (2 * b + c) ≤
      2 ^ 19 * L * (τ / 3 * A ^ 2 + τ / 64 * B ^ 2 + L * τ * μy / 24576 * k ^ 2) +
        12 * L ^ 2 * τ ^ 3 * μy * n1 ^ 2 := by
  have hGy2 : Gy ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    have := pow_le_pow_left₀ hGy h3 2
    linarith [sq_nonneg (A - B)]
  have hGx2 : Gx ^ 2 ≤ 3 * (25 / 9 * A ^ 2 + 4 * L ^ 2 * τ ^ 2 * n1 ^ 2 + 4 * L ^ 2 * k ^ 2) := by
    have := pow_le_pow_left₀ hGx h4 2
    linarith [sq_nonneg (5 / 3 * A - 2 * L * τ * n1), sq_nonneg (5 / 3 * A - 2 * L * k),
      sq_nonneg (2 * L * τ * n1 - 2 * L * k)]
  have q1 : μx * μy * τ * (2 * b) ≤ L * τ * (2 * A ^ 2 + 2 * B ^ 2) := by
    have e : μx * μy * τ * (2 * b) = μx * τ * (2 * μy * b) := by ring
    have e2 : μx * τ * (2 * μy * b) ≤ μx * τ * (2 * A ^ 2 + 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left (h1.trans hGy2) (by positivity)
    have e3 : μx * τ * (2 * A ^ 2 + 2 * B ^ 2) ≤ L * τ * (2 * A ^ 2 + 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμxL hτ.le) (by positivity)
    linarith
  have q2 : μx * μy * τ * c ≤ μy * τ / 2 *
      (3 * (25 / 9 * A ^ 2 + 4 * L ^ 2 * τ ^ 2 * n1 ^ 2 + 4 * L ^ 2 * k ^ 2)) := by
    have e : μx * μy * τ * c = μy * τ / 2 * (2 * μx * c) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (h2.trans hGx2) (by positivity)
  have r1 : μy * τ * A ^ 2 ≤ L * τ * A ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμyL hτ.le) (sq_nonneg A)
  have r2 : 0 ≤ L * τ * A ^ 2 := by positivity
  have r3 : 0 ≤ L * τ * B ^ 2 := by positivity
  have r4 : 0 ≤ L ^ 2 * τ * μy * k ^ 2 := by positivity
  have r5 : 0 ≤ L ^ 2 * τ ^ 3 * μy * n1 ^ 2 := by positivity
  linarith

lemma Hyp.potential_gap [ProperSpace E] {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F}
    {L μx μy : ℝ} (H : Hyp f gx gy L μx μy) {τ : ℝ} (hτ : 0 < τ) (hs : 3 * L * τ ≤ 1)
    (x z e1 x' : E) (y : F) (hx' : x' = x - τ • (xgrad gx L z x y + e1)) :
    μx * μy * τ * (potential f L z x y - minimaxValue f) ≤
      2 ^ 18 * L * (τ / 3 * ‖xgrad gx L z x y‖ ^ 2 + τ / 64 * ‖gy (xhat f L y z) y‖ ^ 2 +
        L * τ * μy / 24576 * ‖x' - z‖ ^ 2) + 9 * L ^ 2 * τ ^ 3 * μy * ‖e1‖ ^ 2 := by
  have hL := H.hL
  have e : potential f L z x y - minimaxValue f = (fhat f L z x y - psi f L y z) +
      (envelope f L z - psi f L y z) + (envelope f L z - minimaxValue f) := by
    simp only [potential]; ring
  rw [e]
  have h1 := H.fhat_sub_psi z x y
  rw [le_div_iff₀ (by positivity)] at h1
  have ha1 : 0 ≤ fhat f L z x y - psi f L y z := sub_nonneg.2 (H.xhat_min y z x)
  have ha2 : 0 ≤ envelope f L z - psi f L y z := sub_nonneg.2 (H.psi_le_envelope y z)
  have h2 := H.envelope_sub_psi y z
  have h3 := H.envelope_gap y z
  have h3' : μx * (envelope f L z - minimaxValue f) ≤ μx * (envelope f L z - psi f L y z) +
      (L * μx + 2 * L ^ 2) * ‖xhat f L y z - z‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 H.hμx.le
    have e2 : μx * ((envelope f L z - psi f L y z) + (L + 2 * L ^ 2 / μx) * ‖xhat f L y z - z‖ ^ 2) =
        μx * (envelope f L z - psi f L y z) + (L * μx + 2 * L ^ 2) * ‖xhat f L y z - z‖ ^ 2 := by
      have hc : μx * (L + 2 * L ^ 2 / μx) = L * μx + 2 * L ^ 2 := by
        rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ H.hμx.ne']; ring
      rw [mul_add, ← mul_assoc, hc]
    linarith
  have hdn := H.dist_next hτ hs x z e1 x' y hx'
  have hR : ‖xhat f L y z - z‖ ≤ ‖xhat f L y z - x'‖ + ‖x' - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : L * ‖xhat f L y z - z‖ ≤ 4 / 3 * ‖xgrad gx L z x y‖ + L * τ * ‖e1‖ + L * ‖x' - z‖ := by
    linarith [mul_le_mul_of_nonneg_left hR hL.le]
  exact pl_scalar hL hτ H.hμx H.hμxL H.hμy H.hμyL (norm_nonneg _) ha1
    (by rw [mul_comm]; exact h1) h2 h3' h4

lemma Hyp.criterion_gap [ProperSpace E] {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F}
    {L μx μy : ℝ} (H : Hyp f gx gy L μx μy) {τ : ℝ} (hτ : 0 < τ) (hs : 3 * L * τ ≤ 1)
    (x z e1 x' : E) (y : F) (hx' : x' = x - τ • (xgrad gx L z x y + e1)) :
    μx * μy * τ * ((maxValue f x - minimaxValue f) + (maxValue f x - f x y)) ≤
      2 ^ 19 * L * (τ / 3 * ‖xgrad gx L z x y‖ ^ 2 + τ / 64 * ‖gy (xhat f L y z) y‖ ^ 2 +
        L * τ * μy / 24576 * ‖x' - z‖ ^ 2) + 12 * L ^ 2 * τ ^ 3 * μy * ‖e1‖ ^ 2 := by
  have hL := H.hL
  have e : (maxValue f x - minimaxValue f) + (maxValue f x - f x y) =
      2 * (maxValue f x - f x y) + (f x y - minimaxValue f) := by ring
  rw [e]
  have h1 := H.maxValue_sub_le x y
  rw [le_div_iff₀ (by linarith [H.hμy])] at h1
  have h2 := H.sub_minimax_le x y
  rw [le_div_iff₀ (by linarith [H.hμx])] at h2
  have hd := H.dist_xhat z x y
  have h3 : ‖gy x y‖ ≤ ‖gy (xhat f L y z) y‖ + ‖xgrad gx L z x y‖ := by
    have hl := H.lipy x (xhat f L y z) y y
    simp only [sub_self, norm_zero, add_zero] at hl
    have := norm_le_insert' (gy x y) (gy (xhat f L y z) y)
    simp only [xgrad] at hd ⊢
    linarith
  have hxz : x - z = τ • (xgrad gx L z x y + e1) + (x' - z) := by rw [hx']; abel
  have hnxz : ‖x - z‖ ≤ τ * ‖xgrad gx L z x y‖ + τ * ‖e1‖ + ‖x' - z‖ := by
    rw [hxz]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    linarith [mul_le_mul_of_nonneg_left (norm_add_le (xgrad gx L z x y) e1) hτ.le]
  have h4 : ‖gx x y‖ ≤ 5 / 3 * ‖xgrad gx L z x y‖ + 2 * L * τ * ‖e1‖ + 2 * L * ‖x' - z‖ := by
    have eg : gx x y = xgrad gx L z x y - (2 * L) • (x - z) := by simp [xgrad]
    rw [eg]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hA : L * τ * ‖xgrad gx L z x y‖ ≤ 1 / 3 * ‖xgrad gx L z x y‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hnxz (by linarith : (0 : ℝ) ≤ 2 * L)]
  exact ab_scalar hL hτ H.hμx H.hμxL H.hμy H.hμyL (norm_nonneg _) (norm_nonneg _)
    (by rw [mul_comm]; exact h1)
    (by rw [mul_comm]; exact h2) h3 h4

end OracleTemplate.TwoSidedPL
