import LongTails.Proofs.MultiscaleAggregateSchedule
import LongTails.Proofs.MultiscaleAggregateCodec

namespace LongTails.Proofs.MultiscaleAggregateBudget

open LongTails.Algorithms.MultiscaleAggregate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open MultiscaleAggregateCodec MultiscaleAggregateSchedule
open DistributedTemplate

variable {p : Params}

lemma batch_pos (i : Fin p.n) : 0 < batch p i :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma targetTime_nonneg : 0 ≤ targetTime p := by
  unfold targetTime
  exact div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (p.h i).coe_nonneg (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma worker_time (hh : ∀ i, 0 < p.h i) (i : Fin p.n) :
    (batch p i : ℝ) * (p.h i : ℝ) ≤ targetTime p + p.h i := by
  have hi : (0 : ℝ) < p.h i := hh i
  unfold batch
  rw [Nat.cast_max, max_mul_of_nonneg _ _ hi.le]
  apply max_le
  · simpa using targetTime_nonneg (p := p)
  · have hx := Nat.ceil_lt_add_one (div_nonneg (targetTime_nonneg (p := p)) hi.le)
    have hx' := mul_le_mul_of_nonneg_right hx.le hi.le
    rwa [add_mul, div_mul_cancel₀ _ hi.ne', one_mul] at hx'

lemma batch_variance (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) :
    (∑ i, p.σ i ^ 2 / (batch p i : ℝ)) ≤ (p.n : ℝ) ^ 2 * precision p ^ 2 := by
  have he := precision_pos hε
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  let v := ∑ i, (p.h i : ℝ) * p.σ i ^ 2
  have hv : 0 ≤ v := Finset.sum_nonneg fun i _ => mul_nonneg (p.h i).coe_nonneg (sq_nonneg _)
  by_cases hzero : v = 0
  · have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin p.n))) =>
          mul_nonneg (p.h i).coe_nonneg (sq_nonneg (p.σ i)))).mp hzero
    have hσ (i : Fin p.n) : p.σ i ^ 2 = 0 :=
      (mul_eq_zero.mp (hterms i (Finset.mem_univ i))).resolve_left (ne_of_gt (hh i))
    simp only [hσ, zero_div, Finset.sum_const_zero]
    positivity
  · have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hzero)
    have ht : 0 < targetTime p := div_pos hv' (by positivity)
    have hb (i : Fin p.n) : targetTime p ≤ (batch p i : ℝ) * p.h i := by
      apply (div_le_iff₀ (show (0 : ℝ) < p.h i from hh i)).mp
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
    calc
      (∑ i, p.σ i ^ 2 / (batch p i : ℝ)) ≤ ∑ i, (p.h i : ℝ) * p.σ i ^ 2 / targetTime p := by
        apply Finset.sum_le_sum
        intro i _
        apply (div_le_div_iff₀ (by exact_mod_cast batch_pos (p := p) i) ht).mpr
        nlinarith [mul_le_mul_of_nonneg_right (hb i) (sq_nonneg (p.σ i))]
      _ = (p.n : ℝ) ^ 2 * precision p ^ 2 := by
        rw [← Finset.sum_div]
        change v / (v / _) = _
        field_simp

lemma round_count_lower : 2 * p.L * p.Δ / precision p ^ 2 ≤ (rounds p : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.lt_size_self _).le)

lemma initial_radius (hε : 0 < p.ε) {u : ℝ}
    (hu : u ^ 2 ≤ 2 * p.L * p.Δ) : u ≤ radius p 0 := by
  have he := precision_pos hε
  have hK : (1 : ℝ) ≤ (rounds p : ℝ) := by
    exact_mod_cast (show 1 ≤ rounds p by exact Nat.two_pow_pos _)
  have h := (div_le_iff₀ (sq_pos_of_pos he)).mp (round_count_lower (p := p))
  have hR : radius p 0 = (rounds p : ℝ) * precision p := by simp [radius, exponent, rounds]
  rw [hR]
  nlinarith [mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg (show 0 ≤ (rounds p : ℝ) by positivity) (sq_nonneg (precision p))),
    mul_nonneg (show 0 ≤ (rounds p : ℝ) by positivity) he.le]

end LongTails.Proofs.MultiscaleAggregateBudget
