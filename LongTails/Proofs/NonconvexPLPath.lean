import LongTails.Proofs.NonconvexPLStep

open Finset
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.NonconvexPL

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

noncomputable def statePotential (f : E → F → ℝ) (L : ℝ) (s : E × F × E) : ℝ :=
  potential f L s.2.2 s.1 s.2.1

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μy : ℝ}

lemma Hyp.minimax_le_potential [ProperSpace E] (H : Hyp f gx gy L μy) (z x : E) (y : F) :
    minimaxValue f ≤ potential f L z x y := by
  have h1 := H.xhat_min y z x
  have h2 := H.psi_le_envelope y z
  have h3 := H.minimax_le_envelope z
  simp only [potential, psi] at *
  linarith

lemma Hyp.initial_potential [ProperSpace E] (H : Hyp f gx gy L μy) (x0 : E) (y0 : F) :
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

end OracleTemplate.NonconvexPL
