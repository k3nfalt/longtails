import LongTails.Proofs.WeakInterpolationDesign
import LongTails.Proofs.DistributedBatchedSgd

namespace LongTails.Proofs.WeightedInterpolationAllocation

open DistributedTemplate LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeakInterpolationDesign LongTails.Algorithms.WeightedInterpolationSgd
open LongTails.Proofs.WeakInterpolationDesign

variable {p : Params}

lemma period_pos (p : Params) : 0 < period p := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

lemma phase_pos (p : Params) : 0 < phase p := Nat.mul_pos (period_pos p) (by omega)

lemma period_bound (hp : spec.valid p) : 4 * smoothness p ≤ information p * period p := by
  have hn : 4 * smoothness p / information p ≤ (period p : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈4 * smoothness p / information p⌉₊))
  linarith [(div_le_iff₀ (information_pos hp)).mp hn]

lemma step_bounds (hp : spec.valid p) (k : ℕ) :
    0 ≤ stepSize p k ∧ stepSize p k * smoothness p ≤ 1 / 2 := by
  have hi := information_pos hp
  have hm : 0 < (period p : ℝ) := by exact_mod_cast period_pos p
  have hC := smoothness_pos hp
  have hb := period_bound hp
  unfold stepSize
  split
  · constructor
    · positivity
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
  · constructor
    · positivity
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hi.le (show 0 ≤ ((k - phase p : ℕ) : ℝ) by positivity)]

lemma batch_pos (p : Params) (i : Fin p.n) : 0 < batch p i :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

lemma total_pos (p : Params) : 0 < ∑ i, batch p i :=
  (batch_pos p 0).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))

lemma fraction_pos (p : Params) (i : Fin p.n) : 0 < fraction p i :=
  div_pos (by exact_mod_cast batch_pos p i) (by exact_mod_cast total_pos p)

lemma fraction_sum (p : Params) : ∑ i, fraction p i = 1 :=
  DistributedBatchedSgd.batch_weights_sum _ (total_pos p)

lemma local_time (p : Params) (i : Fin p.n) : p.h i ≤ batchTime p :=
  (Finset.le_sup (s := Finset.univ) (f := p.h) (Finset.mem_univ i)).trans (le_max_left _ _)

lemma batch_bounds (hp : spec.valid p) (i : Fin p.n) :
    (batchTime p : ℝ) / (p.h i : ℝ) ≤ batch p i ∧
    (batch p i : ℝ) ≤ 2 * ((batchTime p : ℝ) / (p.h i : ℝ)) := by
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  have ht : (p.h i : ℝ) ≤ batchTime p := by exact_mod_cast local_time p i
  have ha : (1 : ℝ) ≤ (batchTime p : ℝ) / (p.h i : ℝ) := (one_le_div hh).mpr ht
  have h := Nat.le_ceil ((batchTime p : ℝ) / (p.h i : ℝ))
  have hb : 1 ≤ ⌈(batchTime p : ℝ) / (p.h i : ℝ)⌉₊ := by exact_mod_cast ha.trans h
  rw [batch, max_eq_right hb]
  exact ⟨h, by linarith [Nat.ceil_lt_add_one (zero_le_one.trans ha)]⟩

lemma fraction_cost (hp : spec.valid p) (i : Fin p.n) :
    1 / fraction p i ≤ 2 * (p.h i : ℝ) * ∑ j, (p.h j : ℝ)⁻¹ := by
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  have hb : 0 < (batch p i : ℝ) := by exact_mod_cast batch_pos p i
  have ht : (batchTime p : ℝ) ≤ batch p i * (p.h i : ℝ) := (div_le_iff₀ hh).mp (batch_bounds hp i).1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (batch_bounds hp j).2)
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at hs
  unfold fraction
  rw [one_div_div, div_le_iff₀ hb, Nat.cast_sum]
  have h' := mul_le_mul_of_nonneg_right ht (speed_pos hp).le
  linarith

lemma variance_cost (hp : spec.valid p) :
    (∑ i, weights p i ^ 2 / batch p i) * (batchTime p : ℝ) ≤ information p := by
  rw [Finset.sum_mul, ← weighted_noise hp]
  apply Finset.sum_le_sum
  intro i _
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  have hb : 0 < (batch p i : ℝ) := by exact_mod_cast batch_pos p i
  have ht := (div_le_iff₀ hh).mp (batch_bounds hp i).1
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (weights p i))]

end LongTails.Proofs.WeightedInterpolationAllocation
