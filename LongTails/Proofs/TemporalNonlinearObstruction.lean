import LongTails.Algorithms.TemporalAccelerated
import LongTails.Proofs.TemporalDiscrepancyObstructions

noncomputable section

namespace OracleTemplate.TemporalDiscrepancy

def bentQuadratic (x : ℝ) : ℝ := if 0 ≤ x then x ^ 2 else x ^ 2 / 2

def bentGradient (x : ℝ) : ℝ := if 0 ≤ x then 2 * x else x

def cycleError (k : ℕ) : ℝ := if k = 0 then -29 else -38 * (-1 : ℝ) ^ k

lemma bent_gradient (x : ℝ) : HasGradientAt bentQuadratic (bentGradient x) x := by
  have hd : HasDerivAt bentQuadratic (bentGradient x) x := by
    have hp (y : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
      convert (hasDerivAt_id y).pow 2 using 1 <;> first | rfl | simp
    have hn (y : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
      convert (hp y).div_const 2 using 1; simp
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [bentGradient, ite_eq_right (not_le.mpr hx)]
      apply (hn x).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [bentQuadratic, not_le.mpr hy]
    · subst x
      have hr : HasDerivWithinAt bentQuadratic 0 (Set.Ici 0) 0 := by
        apply ((hp 0).hasDerivWithinAt.congr_deriv (by ring)).congr
        · intro y hy
          simp [bentQuadratic, Set.mem_Ici.mp hy]
        · norm_num [bentQuadratic]
      have hl : HasDerivWithinAt bentQuadratic 0 (Set.Iic 0) 0 := by
        apply (hn 0).hasDerivWithinAt.congr
        · intro y hy
          dsimp [bentQuadratic]
          split_ifs with h
          · have : y = 0 := le_antisymm hy h
            simp [this]
          · rfl
        · norm_num [bentQuadratic]
      have h := hr.union hl
      rw [Set.Ici_union_Iic, hasDerivWithinAt_univ] at h
      simpa [bentGradient] using h
    · rw [bentGradient, ite_eq_left hx.le]
      apply (hp x).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [bentQuadratic, hy.le]
  simpa using hd.hasGradientAt

lemma bent_strong_support (x y : ℝ) :
    bentQuadratic x + bentGradient x * (y - x) + (y - x) ^ 2 / 2 ≤ bentQuadratic y := by
  dsimp [bentQuadratic, bentGradient]
  split_ifs <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (y - x)]

lemma bent_smooth (x y : ℝ) : |bentGradient x - bentGradient y| ≤ 2 * |x - y| := by
  dsimp [bentGradient]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    nlinarith [le_abs_self (x - y), neg_le_abs (x - y)]

lemma bent_minimizer : IsMinOn bentQuadratic Set.univ 0 := by
  intro x _
  norm_num [bentQuadratic]
  split_ifs <;> positivity

lemma cycle_error_sum (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), cycleError k) = -10 - 19 * (-1 : ℝ) ^ N := by
  induction N with
  | zero => norm_num [cycleError]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [cycleError, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, pow_succ]
    ring

lemma cycle_discrepancy (N : ℕ) : |∑ k ∈ Finset.range N, cycleError k| ≤ 29 := by
  cases N with
  | zero => norm_num
  | succ N =>
    rw [cycle_error_sum]
    rcases neg_one_pow_eq_or ℝ N with h | h <;> rw [h] <;> norm_num

lemma nonlinear_cycle (k : ℕ) :
    acceleratedRun (fun k x => bentGradient x + cycleError k) (1 / 2) 1 (-7) (k + 1) =
      (-5 / 2 + (9 / 2) * (-1 : ℝ) ^ k, -5 / 2 + (27 / 2) * (-1 : ℝ) ^ k) := by
  induction k with
  | zero => norm_num [acceleratedRun, acceleratedUpdate, acceleratedQuery, bentGradient, cycleError]
  | succ k ih =>
    rw [acceleratedRun, ih]
    simp only [cycleError, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, pow_succ]
    rcases neg_one_pow_eq_or ℝ k with h | h <;>
      norm_num [h, acceleratedUpdate, acceleratedQuery, bentGradient]

lemma nonlinear_tail_gap {K : ℕ} (hK : 0 < K) (heven : Even K) :
    let output := tailAverage
      (fun k => (acceleratedRun (fun k x => bentGradient x + cycleError k) (1 / 2) 1 (-7) k).1) K K
    bentQuadratic output - bentQuadratic 0 = 25 / 8 := by
  have hsum : (∑ k ∈ Finset.range K, (-1 : ℝ) ^ k) = 0 := by
    have h := alternating_sum 1 K
    simpa [heven.neg_one_pow] using h
  have hout : tailAverage
      (fun k => (acceleratedRun (fun k x => bentGradient x + cycleError k) (1 / 2) 1 (-7) k).1) K K = -5 / 2 := by
    unfold tailAverage
    simp_rw [nonlinear_cycle, pow_add]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_zero, add_zero, smul_eq_mul]
    have hn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp
  dsimp only
  rw [hout]
  norm_num [bentQuadratic]

end OracleTemplate.TemporalDiscrepancy
