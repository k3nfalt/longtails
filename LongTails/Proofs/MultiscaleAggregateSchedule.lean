import LongTails.Algorithms.MultiscaleAggregate
import LongTails.Proofs.DyadicHolderTrajectory

namespace LongTails.Proofs.MultiscaleAggregateSchedule

open LongTails.Algorithms.MultiscaleAggregate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open OracleTemplate.DyadicHolder

lemma level_even {j : ℕ} (hj : j ≠ 0) :
    padicValNat 2 (2 * j) = 1 + padicValNat 2 j := by
  rw [padicValNat.mul (by norm_num) hj, padicValNat.self (by norm_num)]

lemma level_odd (j : ℕ) : padicValNat 2 (2 * j + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

lemma sum_levels (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), padicValNat 2 k =
      m - 1 + ∑ k ∈ Finset.range m, padicValNat 2 k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, level_odd]
    by_cases hm : m = 0
    · simp [hm]
    · rw [level_even hm]
      omega

lemma sum_levels_block (j : ℕ) :
    j + ∑ k ∈ Finset.range (2 ^ j), padicValNat 2 k = 2 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_comm (2 ^ j), sum_levels]
    have : 0 < 2 ^ j := by positivity
    omega

lemma exponent_sum (p : Params) :
    (∑ k ∈ Finset.range (rounds p), exponent p k) = rounds p - 1 := by
  classical
  have hrewrite (k : ℕ) (hk : k ∈ Finset.range (rounds p)) :
      exponent p k = (if k = 0 then depth p else 0) + padicValNat 2 k := by
    have hmod : (schedule p).pos k = k := Nat.mod_eq_of_lt (Finset.mem_range.mp hk)
    by_cases h : k = 0 <;> simp [exponent, h, DyadicConfig.level, hmod]
  rw [Finset.sum_congr rfl hrewrite, Finset.sum_add_distrib]
  simpa [rounds, Finset.sum_ite_eq'] using sum_levels_block (depth p)

lemma scale_parent (p : Params) (k : ℕ) (hk : k < rounds p) (hk₀ : k ≠ 0) :
    exponent p k < exponent p ((schedule p).pred k) := by
  have hpos : (schedule p).pos k = k := Nat.mod_eq_of_lt hk
  have hn : (schedule p).pos k ≠ 0 := by rwa [hpos]
  have hp := (schedule p).pred_lt hn
  have hpmod : (schedule p).pos ((schedule p).pred k) = (schedule p).pred k :=
    Nat.mod_eq_of_lt (hp.trans hk)
  by_cases hp₀ : (schedule p).pred k = 0
  · rw [hp₀]
    simp [exponent, hk₀]
    exact (schedule p).level_lt hn
  · simpa [exponent, hk₀, hp₀] using (schedule p).level_pred_gt hn (by rwa [hpmod])

end LongTails.Proofs.MultiscaleAggregateSchedule
