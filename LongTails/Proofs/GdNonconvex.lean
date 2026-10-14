import LongTails.Algorithms.GdNonconvex
import LongTails.Proofs.GdConvex

namespace OracleTemplate.NonconvexGradient

open LongTails.Setups.SmoothNonconvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma bestGradient_accuracy (f : E → ℝ) (L Δ ε : ℝ) (x0 : E)
    (hL : 0 < L) (hε : 0 < ε)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f x0 - lower ≤ Δ) :
    let K := max 1 ⌈2 * L * Δ / ε ^ 2⌉₊
    let result := execute { answer := fun _ (_, x) _ => gradient f x } (gdBest (L, Δ, ε, x0)) (fun _ => K)
    ‖gradient f result‖ ^ 2 ≤ ε ^ 2 := by
  let T := fun s : E × E × ℝ => bestGradientStep L s (gradient f s.1)
  let s := fun k => T^[k] (x0, x0, 2 * L * Δ)
  have hs (k : ℕ) : s (k + 1) = T (s k) := Function.iterate_succ_apply' _ _ _
  have hden : 0 < 2 * L := by positivity
  have hinit : ‖gradient f x0‖ ^ 2 ≤ 2 * L * Δ := by
    have hd := Gradient.descent hL hg hlip x0
    have hb := hlower (x0 - (1 / L) • gradient f x0)
    have : ‖gradient f x0‖ ^ 2 / (2 * L) ≤ Δ := by linarith
    exact (div_le_iff₀ hden).mp this |>.trans_eq (by ring)
  have hinv : ∀ k, ‖gradient f (s k).2.1‖ ^ 2 ≤ (s k).2.2 ∧
      f (s k).1 + (k : ℝ) * (s k).2.2 / (2 * L) ≤ f x0 := by
    intro k
    induction k with
    | zero => simpa [s] using And.intro hinit (le_refl (f x0))
    | succ k ih =>
      have hd := Gradient.descent hL hg hlip (s k).1
      rw [hs]
      dsimp [T, bestGradientStep]
      split_ifs with h
      · refine ⟨le_refl _, ?_⟩
        have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        have hd' := (div_le_div_iff_of_pos_right hden).mpr hm
        push_cast
        simp only [add_mul, add_div, one_mul] at *
        linarith [ih.2]
      · refine ⟨ih.1, ?_⟩
        have hd' := (div_le_div_iff_of_pos_right hden).mpr (le_of_lt (lt_of_not_ge h))
        push_cast
        simp only [add_mul, add_div, one_mul] at *
        linarith [ih.2]
  let K := max 1 ⌈2 * L * Δ / ε ^ 2⌉₊
  have hK : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hceil : 2 * L * Δ / ε ^ 2 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (⌈2 * L * Δ / ε ^ (2 : ℕ)⌉₊)))
  have hbudget : 2 * L * Δ ≤ (K : ℝ) * ε ^ 2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp hceil
  have henergy := (hinv K).2
  have hb := hlower (s K).1
  have hbound : (K : ℝ) * (s K).2.2 ≤ 2 * L * Δ := by
    have : (K : ℝ) * (s K).2.2 / (2 * L) ≤ Δ := by linarith
    have := (div_le_iff₀ hden).mp this
    nlinarith
  have hsmall : (s K).2.2 ≤ ε ^ 2 := (mul_le_mul_iff_right₀ hK).mp (hbound.trans hbudget)
  dsimp only
  erw [execute_iterate]
  exact (hinv K).1.trans hsmall

end OracleTemplate.NonconvexGradient
