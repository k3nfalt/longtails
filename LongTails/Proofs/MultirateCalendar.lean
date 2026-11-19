import LongTails.Algorithms.MultirateCalendar
import LongTails.Proofs.MultirateAllocation
import LongTails.Proofs.MultiscaleAggregateBudget

namespace LongTails.Proofs.MultirateCalendar

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateAllocation LongTails.Algorithms.MultirateCalendar

variable {p : Params}

lemma steps_pos (p : Params) : 0 < steps p := Nat.two_pow_pos _

lemma packet_nonneg (p : Params) : 0 ≤ packetTime p := by
  unfold packetTime
  positivity

lemma service_nonneg (p : Params) (i : Fin p.n) : 0 ≤ service p i :=
  mul_nonneg (p.h i).coe_nonneg (Nat.cast_nonneg _)

lemma slot_pos (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) : 0 < slot p := by
  have hH : (0 : DistributedTemplate.Time) < Finset.univ.sup p.h :=
    (hh 0).trans_le (Finset.le_sup (Finset.mem_univ 0))
  have hK : (0 : ℝ) < steps p := by exact_mod_cast steps_pos p
  have hnum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hL i) (service_nonneg p i))
  exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos (by have := packet_nonneg p; positivity)
    (div_pos hH hK)) (div_nonneg hnum (Finset.sum_nonneg (fun i _ => hL i)))

lemma period_pos (p : Params) (i : Fin p.n) : 0 < period p i := by unfold period; omega

lemma trip_nonneg (p : Params) (i : Fin p.n) : 0 ≤ trip p i := by
  unfold trip
  have := packet_nonneg p
  have := service_nonneg p i
  positivity

lemma trip_le (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (i : Fin p.n) :
    trip p i ≤ period p i * slot p := by
  apply (div_le_iff₀ (slot_pos hh hL)).mp
  simpa [period, add_comm] using (Nat.lt_floor_add_one (trip p i / slot p)).le

lemma weighted_period (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) :
    (∑ i, p.L i * period p i) ≤ 3 * ∑ i, p.L i := by
  let W := ∑ i, p.L i
  let A := ∑ i, p.L i * service p i
  have hs := slot_pos hh hL
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => hL i
  have hA : A ≤ W * slot p := by
    by_cases hz : W = 0
    · have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hL i)).mp hz
      simp [A,hz,fun i => hz' i (Finset.mem_univ i)]
    have hb : A / W ≤ slot p := le_add_of_nonneg_left (by
      have := packet_nonneg p
      positivity)
    simpa [mul_comm] using (div_le_iff₀ (lt_of_le_of_ne hW (Ne.symm hz))).mp hb
  calc
    _ ≤ ∑ i, p.L i * (1 + trip p i / slot p) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hL i)
      unfold period
      push_cast
      exact add_le_add_right (Nat.floor_le (div_nonneg (trip_nonneg p i) hs.le)) 1
    _ = W + (W * (2 * packetTime p) + A) / slot p := by
      simp [W,A,trip,mul_add, ← mul_div_assoc, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_mul]
    _ ≤ _ := by
      have hc : 2 * packetTime p ≤ slot p := by
        unfold slot
        have hU := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hL i) (service_nonneg p i))
        have hV := div_nonneg hU hW
        have hH : 0 ≤ ((Finset.univ.sup p.h : NNReal) : ℝ) / steps p := by positivity
        linarith
      change W + _ ≤ 3 * W
      apply le_trans (add_le_add_right ((div_le_iff₀ hs).mpr (show _ ≤ (2 * W) * slot p by
        nlinarith [mul_le_mul_of_nonneg_left hc hW])) _)
      linarith

lemma origin_le (p : Params) (i : Fin p.n) (k : ℕ) : origin p i k ≤ k :=
  (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)).trans (Nat.div_mul_le_self _ _)

lemma age_lt (p : Params) (i : Fin p.n) (k : ℕ) : k - origin p i k < 2 * period p i := by
  let q := period p i
  have hq : 0 < q := period_pos p i
  have hm := Nat.mod_lt k hq
  have he := Nat.mod_add_div k q
  change k - (k / q - 1) * q < 2 * q
  cases hj : k / q with
  | zero => rw [hj, Nat.mul_zero, Nat.add_zero] at he; simp; omega
  | succ j => rw [hj, Nat.mul_succ] at he; simp; rw [Nat.mul_comm j q]; omega

end LongTails.Proofs.MultirateCalendar
