import LongTails.Proofs.MultiscaleAggregatePipeline
import LongTails.Proofs.MultiscaleAggregateSchedule

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

variable {p : Params}

lemma rounds_upper : rounds p ≤ 2 * (1 + ⌈524288 * p.L * p.Δ / p.ε ^ 2⌉₊) := by
  have he : 2 * p.L * p.Δ / precision p ^ 2 = 524288 * p.L * p.Δ / p.ε ^ 2 := by
    unfold precision
    ring
  unfold rounds depth
  rw [he]
  generalize ⌈524288 * p.L * p.Δ / p.ε ^ 2⌉₊ = k
  cases h : k.size with
  | zero => simp; omega
  | succ j =>
    have hle : 2 ^ j ≤ k := Nat.lt_size.mp (by omega)
    rw [pow_succ]
    omega

lemma payload_sum :
    (∑ k ∈ Finset.range (rounds p), (payload p k + clockBits)) ≤
      rounds p * (clockBits + p.d * (5 + Nat.size ((p.n : ℕ) * (p.d + 1)))) := by
  simp only [payload, width, Nat.mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.mul_sum, MultiscaleAggregateSchedule.exponent_sum]
  have h := Nat.mul_le_mul_left p.d (Nat.sub_le (rounds p) 1)
  nlinarith

lemma runtime_bound (hh : ∀ i, 0 < p.h i) :
    executionTime p ≤ (2 * (1 + ⌈524288 * p.L * p.Δ / p.ε ^ 2⌉₊) : ℕ) *
      (Finset.univ.sup p.h + Real.toNNReal (262144 * (∑ i, (p.h i : ℝ) * p.σ i ^ 2) / ((p.n : ℝ) ^ 2 * p.ε ^ 2)) +
        2 * (p.l + p.b * (clockBits + p.d * (5 + Nat.size ((p.n : ℕ) * (p.d + 1))) : ℕ))) := by
  let H := Finset.univ.sup p.h + Real.toNNReal (targetTime p)
  have hcomp : computeTime p ≤ H := by
    apply Finset.sup_le
    intro i hi
    have hw := MultiscaleAggregateBudget.worker_time hh i
    have hmax := Finset.le_sup (f := p.h) hi
    change _ ≤ Finset.univ.sup p.h + Real.toNNReal (targetTime p)
    apply NNReal.coe_le_coe.mp
    push_cast
    rw [Real.toNNReal_of_nonneg MultiscaleAggregateBudget.targetTime_nonneg]
    change _ ≤ (Finset.univ.sup p.h : Time) + targetTime p
    exact hw.trans (by simpa only [add_comm] using add_le_add_left (NNReal.coe_le_coe.mpr hmax) (targetTime p))
  let B := clockBits + p.d * (5 + Nat.size ((p.n : ℕ) * (p.d + 1)))
  have hs : (∑ k ∈ Finset.range (rounds p), ((payload p k + clockBits : ℕ) : Time)) ≤ (rounds p : Time) * B := by
    exact_mod_cast (payload_sum (p := p))
  have ht : targetTime p = 262144 * (∑ i, (p.h i : ℝ) * p.σ i ^ 2) / ((p.n : ℝ) ^ 2 * p.ε ^ 2) := by
    unfold targetTime precision
    ring
  calc
    executionTime p ≤ ∑ k ∈ Finset.range (rounds p), ((H + 2 * p.l) + (2 * p.b) * ((payload p k + clockBits : ℕ) : Time)) := by
      apply Finset.sum_le_sum
      intro k _
      unfold roundTime
      calc
        _ ≤ H + p.l + p.b * ((payload p k + clockBits : ℕ) : Time) +
              (p.l + p.b * ((payload p k + clockBits : ℕ) : Time)) := by
          apply add_le_add
          · gcongr
          · split_ifs <;> first | exact le_rfl | exact zero_le
        _ = _ := by ring
    _ = (rounds p : Time) * (H + 2 * p.l) + (2 * p.b) * ∑ k ∈ Finset.range (rounds p), ((payload p k + clockBits : ℕ) : Time) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (rounds p : Time) * (H + 2 * p.l) + (2 * p.b) * ((rounds p : Time) * B) := by gcongr
    _ = (rounds p : Time) * (H + 2 * (p.l + p.b * B)) := by ring
    _ ≤ _ := by
      dsimp only [H, B]
      rw [ht]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (rounds_upper (p := p))) zero_le

end LongTails.Proofs.MultiscaleAggregateExecution
