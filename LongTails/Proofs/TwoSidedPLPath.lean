import LongTails.Proofs.TwoSidedPLGap
import LongTails.Proofs.TwoSidedPLSum

open Finset
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.TwoSidedPL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def nextState (gx : E → F → E) (gy : E → F → F) (L μy τ : ℝ) (s : E × F × E)
    (e1 : E) (e2 : F) : E × F × E :=
  (s.1 - τ • (xgrad gx L s.2.2 s.1 s.2.1 + e1),
    s.2.1 + (τ / 32) • (gy (s.1 - τ • (xgrad gx L s.2.2 s.1 s.2.1 + e1)) s.2.1 + e2),
    s.2.2 + (τ * μy / 6144) • (s.1 - τ • (xgrad gx L s.2.2 s.1 s.2.1 + e1) - s.2.2))

noncomputable def decrease (f : E → F → ℝ) (gx : E → F → E) (gy : E → F → F) (L μy τ : ℝ)
    (s s' : E × F × E) : ℝ :=
  τ / 3 * ‖xgrad gx L s.2.2 s.1 s.2.1‖ ^ 2 + τ / 64 * ‖gy (xhat f L s.2.1 s.2.2) s.2.1‖ ^ 2 +
    L * τ * μy / 24576 * ‖s'.1 - s.2.2‖ ^ 2

noncomputable def martingale (f : E → F → ℝ) (gx : E → F → E) (gy : E → F → F) (L τ : ℝ)
    (s : E × F × E) (x' : E) (e1 : E) (e2 : F) : ℝ :=
  (τ - 3 * L * τ ^ 2) * ⟪xgrad gx L s.2.2 s.1 s.2.1, e1⟫ +
    ⟪(τ / 16) • gy (xhat f L s.2.1 s.2.2) s.2.1 - (τ / 32 + 5 * L * τ ^ 2 / 1024) • gy x' s.2.1, e2⟫

noncomputable def gapValue (f : E → F → ℝ) (s : E × F × E) : ℝ :=
  (maxValue f s.1 - minimaxValue f) + (maxValue f s.1 - f s.1 s.2.1)

noncomputable def statePotential (f : E → F → ℝ) (L : ℝ) (s : E × F × E) : ℝ :=
  potential f L s.2.2 s.1 s.2.1

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy : ℝ}

lemma Hyp.minimax_le_potential [ProperSpace E] (H : Hyp f gx gy L μx μy) (z x : E) (y : F) :
    minimaxValue f ≤ potential f L z x y := by
  have h1 := H.xhat_min y z x
  have h2 := H.psi_le_envelope y z
  have h3 := H.minimax_le_envelope z
  simp only [potential, psi] at *
  linarith

lemma Hyp.initial_potential [ProperSpace E] (H : Hyp f gx gy L μx μy) (x0 : E) (y0 : F) :
    potential f L x0 x0 y0 - minimaxValue f ≤
      2 * maxValue f x0 - minimaxValue f - f x0 y0 + ‖gx x0 y0‖ ^ 2 / L := by
  have hL := H.hL
  have h1 : f x0 y0 - ‖gx x0 y0‖ ^ 2 / (2 * L) ≤ psi f L y0 x0 := by
    set x := xhat f L y0 x0
    have h := H.fhat_lower x0 x0 x y0
    simp only [sub_self, smul_zero, add_zero, fhat, norm_zero] at h
    have hi : -(‖gx x0 y0‖ * ‖x - x0‖) ≤ ⟪gx x0 y0, x - x0⟫ := by
      have := abs_le.1 (abs_real_inner_le_norm (gx x0 y0) (x - x0)); linarith
    have hq : ‖gx x0 y0‖ * ‖x - x0‖ - L / 2 * ‖x - x0‖ ^ 2 ≤ ‖gx x0 y0‖ ^ 2 / (2 * L) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [sq_nonneg (‖gx x0 y0‖ - L * ‖x - x0‖)]
    have hpsi : psi f L y0 x0 = f x y0 + L * ‖x - x0‖ ^ 2 := rfl
    have hsq : 0 ≤ L / 2 * ‖x - x0‖ ^ 2 := by positivity
    linarith
  have h2 : envelope f L x0 ≤ maxValue f x0 := by
    have := H.xbar_min x0 x0
    simpa [phat] using this
  simp only [potential, fhat, sub_self, norm_zero] at *
  have e : ‖gx x0 y0‖ ^ 2 / L = 2 * (‖gx x0 y0‖ ^ 2 / (2 * L)) := by field_simp
  rw [e]
  linarith

lemma Hyp.window [ProperSpace E] (H : Hyp f gx gy L μx μy) {τ : ℝ} (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (s : ℕ → E × F × E) (e1 : ℕ → E) (e2 : ℕ → F)
    (hrec : ∀ t, s (t + 1) = nextState gx gy L μy τ (s t) (e1 t) (e2 t)) (n : ℕ) :
    ∑ t ∈ Ico n (n + (n + 1)), gapValue f (s t) ≤
      2 * (2 ^ 18 * L / (μx * μy * τ)) *
        ((1 - 1 / (2 ^ 18 * L / (μx * μy * τ))) ^ n * (statePotential f L (s 0) - minimaxValue f) +
          ∑ t ∈ range n, (1 - 1 / (2 ^ 18 * L / (μx * μy * τ))) ^ (n - 1 - t) *
            (9 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx / (2 ^ 18 * L / (μx * μy * τ)) +
              2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
              martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t)) +
          ∑ t ∈ Ico n (n + (n + 1)), (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
              martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))) +
      ∑ t ∈ Ico n (n + (n + 1)), 12 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx := by
  have hL := H.hL
  have hμx := H.hμx
  have hμy := H.hμy
  set C := 2 ^ 18 * L / (μx * μy * τ) with hCdef
  have hm : 0 < μx * μy * τ := by positivity
  have hC1 : 1 ≤ C := by
    rw [hCdef, le_div_iff₀ hm]
    have h1 : μx * μy * τ ≤ L * L * τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul H.hμxL H.hμyL hμy.le hL.le) hτ.le
    have h2 := mul_le_mul_of_nonneg_left hs hL.le
    linarith
  have hx' : ∀ t, (s (t + 1)).1 = (s t).1 - τ • (xgrad gx L (s t).2.2 (s t).1 (s t).2.1 + e1 t) := by
    intro t; rw [hrec t]; rfl
  have hstep : ∀ t, decrease f gx gy L μy τ (s t) (s (t + 1)) -
      2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) +
      martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t) ≤
      statePotential f L (s t) - statePotential f L (s (t + 1)) := by
    intro t
    have h := H.step hτ hs (s t).1 (s t).2.2 (e1 t) (s (t + 1)).1 (s (t + 1)).2.2 (s t).2.1 (e2 t)
      (s (t + 1)).2.1 (hx' t) (by rw [hrec t]; rfl) (by rw [hrec t]; rfl)
    simp only [decrease, martingale, statePotential]
    linarith
  have hpl : ∀ t, statePotential f L (s t) - minimaxValue f ≤
      C * decrease f gx gy L μy τ (s t) (s (t + 1)) + 9 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx := by
    intro t
    have h := H.potential_gap hτ hs (s t).1 (s t).2.2 (e1 t) (s (t + 1)).1 (s t).2.1 (hx' t)
    simp only [decrease, statePotential]
    rw [← mul_le_mul_iff_of_pos_left hm]
    have e : μx * μy * τ * (C * (τ / 3 * ‖xgrad gx L (s t).2.2 (s t).1 (s t).2.1‖ ^ 2 +
        τ / 64 * ‖gy (xhat f L (s t).2.1 (s t).2.2) (s t).2.1‖ ^ 2 +
        L * τ * μy / 24576 * ‖(s (t + 1)).1 - (s t).2.2‖ ^ 2) +
        9 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx) =
        2 ^ 18 * L * (τ / 3 * ‖xgrad gx L (s t).2.2 (s t).1 (s t).2.1‖ ^ 2 +
        τ / 64 * ‖gy (xhat f L (s t).2.1 (s t).2.2) (s t).2.1‖ ^ 2 +
        L * τ * μy / 24576 * ‖(s (t + 1)).1 - (s t).2.2‖ ^ 2) +
        9 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2 := by
      rw [hCdef]; field_simp
    rw [e]
    exact h
  have hab : ∀ t, gapValue f (s t) ≤
      2 * C * decrease f gx gy L μy τ (s t) (s (t + 1)) + 12 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx := by
    intro t
    have h := H.criterion_gap hτ hs (s t).1 (s t).2.2 (e1 t) (s (t + 1)).1 (s t).2.1 (hx' t)
    simp only [decrease, gapValue]
    rw [← mul_le_mul_iff_of_pos_left hm]
    have e : μx * μy * τ * (2 * C * (τ / 3 * ‖xgrad gx L (s t).2.2 (s t).1 (s t).2.1‖ ^ 2 +
        τ / 64 * ‖gy (xhat f L (s t).2.1 (s t).2.2) (s t).2.1‖ ^ 2 +
        L * τ * μy / 24576 * ‖(s (t + 1)).1 - (s t).2.2‖ ^ 2) +
        12 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx) =
        2 ^ 19 * L * (τ / 3 * ‖xgrad gx L (s t).2.2 (s t).1 (s t).2.1‖ ^ 2 +
        τ / 64 * ‖gy (xhat f L (s t).2.1 (s t).2.2) (s t).2.1‖ ^ 2 +
        L * τ * μy / 24576 * ‖(s (t + 1)).1 - (s t).2.2‖ ^ 2) +
        12 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2 := by
      rw [hCdef]; field_simp
    rw [e]
    exact h
  have hlow : ∀ t, minimaxValue f ≤ statePotential f L (s t) :=
    fun t => H.minimax_le_potential _ _ _
  have hw := window_sum (V := fun t => statePotential f L (s t))
    (D := fun t => decrease f gx gy L μy τ (s t) (s (t + 1)))
    (ns := fun t => 2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2))
    (M := fun t => martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))
    (Nab := fun t => 12 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx) (ab := fun t => gapValue f (s t))
    (by linarith : (0 : ℝ) ≤ C) hstep hlow hab n (n + 1)
  have hu := potential_unroll (V := fun t => statePotential f L (s t))
    (D := fun t => decrease f gx gy L μy τ (s t) (s (t + 1)))
    (ns := fun t => 2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2))
    (M := fun t => martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))
    (N := fun t => 9 * L ^ 2 * τ ^ 2 * ‖e1 t‖ ^ 2 / μx) hC1 hstep hpl n
  have h2C : 0 ≤ 2 * C := by linarith
  linarith [mul_le_mul_of_nonneg_left hu h2C]

end OracleTemplate.TwoSidedPL
