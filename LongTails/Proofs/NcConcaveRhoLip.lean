import LongTails.Proofs.NcConcaveLine
import LongTails.Proofs.NcConcavePartTwo
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveRhoLip

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcaveLine
open LongTails.Proofs.NcConcavePartTwo

variable {n : ℕ}

lemma rho_line_at (u d : Fin (n + 1) → ℝ) (w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, w i * rho (fun j => u j + s * d j) i)
      (∑ i, w i * drho (fun j => u j + t * d j) d i) t := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => HasDerivAt.const_mul (w i) (rho_line (fun j => u j + t * d j) d i))
  have h0 : HasDerivAt (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
      w i * rho (fun j => u j + t * d j + y * d j) i)
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * drho (fun j => u j + t * d j) d i) (t - t) := by
    rw [sub_self]; exact h
  have hshift := HasDerivAt.comp_sub_const t t h0
  convert hshift using 1
  funext s
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2; funext j; ring

theorem rho_lipschitz (u u' : Fin (n + 1) → ℝ) :
    sq2 (fun i => rho u' i - rho u i) ≤ 9 * sq1 (fun j => u' j - u j) := by
  set d : Fin (n + 1) → ℝ := fun j => u' j - u j
  set w : Fin n → ℝ := fun i => rho u' i - rho u i
  set g : ℝ → ℝ := fun s => ∑ i, w i * rho (fun j => u j + s * d j) i
  have hg : ∀ t, HasDerivAt g (∑ i, w i * drho (fun j => u j + t * d j) d i) t :=
    fun t => rho_line_at u d w t
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope g _ (by norm_num : (0 : ℝ) < 1)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have h0 : g 0 = ∑ i, w i * rho u i := by
    simp only [g, zero_mul, add_zero]
  have h1 : g 1 = ∑ i, w i * rho u' i := by
    simp only [g, one_mul, d]; congr 1; funext i; congr 2; funext j; ring
  have hdiff : g 1 - g 0 = sq2 w := by
    rw [h0, h1, ← Finset.sum_sub_distrib]; simp only [sq2, w]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [sub_zero, div_one, hdiff] at hξ
  have hcs := cs_bound w (drho (fun j => u j + ξ * d j) d)
  have hd9 := sq2_drho_le_nine (fun j => u j + ξ * d j) d
  have hW := sq2_nonneg w
  have hD := sq1_nonneg d
  have hs : Real.sqrt (sq2 (drho (fun j => u j + ξ * d j) d)) ≤ 3 * Real.sqrt (sq1 d) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hD]; linarith
  have key : sq2 w ≤ Real.sqrt (sq2 w) * (3 * Real.sqrt (sq1 d)) := by
    have h := (le_abs_self _).trans (hcs.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (sq2 w))))
    rwa [hξ] at h
  have hw2 := Real.sq_sqrt hW
  have hd2 := Real.sq_sqrt hD
  have hsw := Real.sqrt_nonneg (sq2 w)
  have hsd := Real.sqrt_nonneg (sq1 d)
  have : Real.sqrt (sq2 w) ≤ 3 * Real.sqrt (sq1 d) := by
    by_contra hc; push Not at hc
    nlinarith
  nlinarith

end LongTails.Proofs.NcConcaveRhoLip
