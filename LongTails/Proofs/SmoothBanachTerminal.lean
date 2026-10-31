import LongTails.Proofs.SmoothBanachSampling
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SmoothBanachTerminal

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachAnchoring SmoothBanachTuning SmoothBanachProcess SmoothBanachSampling

lemma epochError_eq (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (g : q.E → q.Ω → q.E)
    (j : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    epochError q T hT g j ξ = strength q j ^ 2 *
      ‖(epochState q g (j + 1) ξ).2.2 - root q T hT j (epochState q g j ξ).2.1‖ ^ 2 := by
  dsimp only [epochError, energy]
  rw [epochState_stage, ← epochState_succ]

lemma terminal_anchored_residual (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (g : q.E → q.Ω → q.E)
    (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    ‖(1 + strength q 0) • (epochState q g (levels q + 1) ξ).2.2 -
      T (epochState q g (levels q + 1) ξ).2.2 - strength q 0 • q.x0‖ ≤
      4 * ∑ j ∈ Finset.range (levels q + 1), strength q j *
        ‖(epochState q g (j + 1) ξ).2.2 - root q T hT j (epochState q g j ξ).2.1‖ := by
  let b := fun j => (epochState q g j ξ).2.1
  let z := fun j => (epochState q g (j + 1) ξ).2.2
  let u := fun j => root q T hT j (b j)
  have hb (j : ℕ) : b (j + 1) = b j + strength q j • z j := epochState_anchor_succ q g j ξ
  have hu (j : ℕ) : (1 + strength q j) • u j - T (u j) - b j = 0 :=
    root_equation q T hT j (b j)
  have hm (j : ℕ) : ‖u j - u (j + 1)‖ ≤ ‖z j - u j‖ / 2 := by
    have hn := hu (j + 1)
    rw [strength_double, hb] at hn
    exact doubled_anchor_root_movement T hT (strength q j) (strength_pos q j)
      (b j) (z j) (u j) (u (j + 1)) (hu j) hn
  have hc := correction_sum_bound (strength q) b u z (strength_pos q 0).le
    (strength_initial_le q) (strength_double q) hb hm (levels q)
  have hf := residual_from_correction T hT (strength q (levels q)) (strength q 0)
    (strength_pos q 0).le (b (levels q)) (b 0) (u (levels q)) (z (levels q)) (hu (levels q))
  have hb0 : b 0 = strength q 0 • q.x0 := rfl
  rw [hb0] at hf hc
  have ha : strength q 0 ≤ 1 := by simpa only [strength_last] using strength_initial_le q (levels q)
  have hs : 0 ≤ ∑ j ∈ Finset.range (levels q), strength q j * ‖z j - u j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (strength_pos q j).le (norm_nonneg _))
  change ‖(1 + strength q 0) • z (levels q) - T (z (levels q)) - strength q 0 • q.x0‖ ≤
    4 * ∑ j ∈ Finset.range (levels q + 1), strength q j * ‖z j - u j‖
  rw [Finset.sum_range_succ, strength_last]
  nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (z (levels q) - u (levels q))),
    norm_nonneg (z (levels q) - u (levels q))]

lemma terminal_anchored_square (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (g : q.E → q.Ω → q.E)
    (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    ‖(1 + strength q 0) • (epochState q g (levels q + 1) ξ).2.2 -
      T (epochState q g (levels q + 1) ξ).2.2 - strength q 0 • q.x0‖ ^ 2 ≤
      16 * (levels q + 1 : ℝ) *
        ∑ j ∈ Finset.range (levels q + 1), epochError q T hT g j ξ := by
  let e := fun j => strength q j *
    ‖(epochState q g (j + 1) ξ).2.2 - root q T hT j (epochState q g j ξ).2.1‖
  have hs : 0 ≤ ∑ j ∈ Finset.range (levels q + 1), e j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (strength_pos q j).le (norm_nonneg _))
  have hb := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs)).mpr
    (terminal_anchored_residual q T hT g ξ)
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range (levels q + 1)) (f := e)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hc
  have he : ∀ j, e j ^ 2 = epochError q T hT g j ξ := by
    intro j
    simp only [e, mul_pow, epochError_eq]
  simp_rw [he] at hc
  nlinarith

lemma terminal_residual_square (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hε : 0 < q.ε)
    (g : q.E → q.Ω → q.E) (xstar : q.E) (hstar : T xstar = xstar)
    (hR : ‖q.x0 - xstar‖ ≤ q.R) (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    ‖T (epochState q g (levels q + 1) ξ).2.2 - (epochState q g (levels q + 1) ξ).2.2‖ ^ 2 ≤
      128 * (levels q + 1 : ℝ) *
        ∑ j ∈ Finset.range (levels q + 1), epochError q T hT g j ξ + q.ε ^ 2 / 32 := by
  let z := (epochState q g (levels q + 1) ξ).2.2
  let u := root q T hT 0 (strength q 0 • q.x0)
  have hu := root_equation q T hT 0 (strength q 0 • q.x0)
  have hd := initial_root_distance T hT (strength q 0) q.R (strength_pos q 0)
    q.x0 xstar u hstar hR hu
  have hf := remove_initial_anchor T hT (strength q 0) q.R (strength_pos q 0).le q.x0 u z hu hd
  have hh := terminal_anchored_square q T hT g ξ
  have hr := initial_strength_radius q hε
  have hR0 : 0 ≤ q.R := (norm_nonneg _).trans hR
  have hr2 := (sq_le_sq₀ (mul_nonneg (strength_pos q 0).le hR0) (by positivity)).mpr hr
  have ha0 := (strength_pos q 0).le
  have hf2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hf
  change ‖T z - z‖ ^ 2 ≤ _
  rw [norm_sub_rev]
  nlinarith [sq_nonneg (‖(1 + strength q 0) • z - T z - strength q 0 • q.x0‖ - strength q 0 * q.R)]

end LongTails.Proofs.SmoothBanachTerminal
