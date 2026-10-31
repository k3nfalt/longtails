import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedLipschitzConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gap_le_norm_mul_distance (f : E → ℝ) (g : E) (x xstar : E)
    (hsub : f x - f xstar ≤ ⟪g, x - xstar⟫) :
    f x - f xstar ≤ ‖g‖ * ‖x - xstar‖ :=
  hsub.trans (real_inner_le_norm _ _)

lemma gap_le_twice_radius (f : E → ℝ) (g : E) (x x0 xstar : E) {R : ℝ}
    (hx : ‖x - x0‖ ≤ R) (hstar : ‖x0 - xstar‖ ≤ R)
    (hsub : f x - f xstar ≤ ⟪g, x - xstar⟫) :
    f x - f xstar ≤ 2 * R * ‖g‖ := by
  have hd : ‖x - xstar‖ ≤ 2 * R := by
    have he : x - xstar = (x - x0) + (x0 - xstar) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  have h := mul_le_mul_of_nonneg_left hd (norm_nonneg g)
  have hg := gap_le_norm_mul_distance f g x xstar hsub
  nlinarith

lemma local_gap_le (f : E → ℝ) (g : E) (x y xstar : E) (G0 G1 : ℝ)
    (hmin : f xstar ≤ f y)
    (hsub : f y - f x ≤ ⟪g, y - x⟫)
    (hgrad : ‖g‖ ≤ G0 + G1 * (f y - f xstar))
    (hsmall : G1 * ‖y - x‖ ≤ 1 / 2) :
    f y - f xstar ≤ 2 * (f x - f xstar) + 2 * G0 * ‖y - x‖ := by
  have h1 := gap_le_norm_mul_distance f g y x hsub
  have h2 := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (y - x))
  have h3 := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hmin)
  nlinarith

lemma gap_bound_of_local (f : E → ℝ) (xstar x : E) (G0 G : ℝ) (N : ℕ)
    (hG0 : 0 ≤ G0) (hG : 0 < G) (hN : 0 < N)
    (hd : 2 * G * ‖x - xstar‖ ≤ N)
    (hloc : ∀ y z, G * ‖y - z‖ ≤ 1 / 2 →
      f y - f xstar ≤ 2 * (f z - f xstar) + 2 * G0 * ‖y - z‖) :
    f x - f xstar ≤ ((2 : ℝ) ^ N - 1) * (G0 / G) := by
  let y : ℕ → E := fun j => xstar + ((j : ℝ) / N) • (x - xstar)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff (j : ℕ) : y (j + 1) - y j = (1 / (N : ℝ)) • (x - xstar) := by
    dsimp [y]
    rw [Nat.cast_add, Nat.cast_one, add_div, add_smul]
    abel
  have hnorm (j : ℕ) : ‖y (j + 1) - y j‖ = ‖x - xstar‖ / N := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hNr)]
    ring
  have hsmall : G * (‖x - xstar‖ / N) ≤ 1 / 2 := by
    have h : (2 * G * ‖x - xstar‖) / (N : ℝ) ≤ 1 :=
      (div_le_iff₀ hNr).mpr (by simpa using hd)
    have he : (2 * G * ‖x - xstar‖) / (N : ℝ) = 2 * (G * (‖x - xstar‖ / N)) := by ring
    rw [he] at h
    linarith
  have herr : 2 * G0 * (‖x - xstar‖ / N) ≤ G0 / G := by
    apply (le_div_iff₀ hG).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hG0]
  have hind (j : ℕ) : f (y j) - f xstar ≤ ((2 : ℝ) ^ j - 1) * (G0 / G) := by
    induction j with
    | zero => simp [y]
    | succ j ih =>
      have h := hloc (y (j + 1)) (y j) (by rw [hnorm]; exact hsmall)
      rw [hnorm] at h
      rw [pow_succ]
      nlinarith
  simpa [y, ne_of_gt hNr] using hind N

end LongTails.Proofs.GeneralizedLipschitzConvex
