import LongTails.Proofs.DistributedNormalizedTuning
import LongTails.Proofs.DistributedNormalizedProtocol
import Mathlib.Data.Nat.Factorization.Basic

namespace LongTails.Proofs.DistributedNormalizedRuntime

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning
open LongTails.Algorithms.DistributedNormalizedProtocol
open DistributedNormalizedTuning

lemma framed_payload_cost (p : Params) (count width : ℕ) (hc : 1 ≤ count) :
    (p.b : ℝ) * (count * width + DistributedTemplate.clockBits : ℕ) ≤
      count * ((p.b : ℝ) * (width + 64 : ℕ)) := by
  have hc' : (1 : ℝ) ≤ count := by exact_mod_cast hc
  have hb : (0 : ℝ) ≤ p.b := p.b.property
  simp only [DistributedTemplate.clockBits, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [mul_nonneg hb (show 0 ≤ (count : ℝ) - 1 by linarith)]

lemma uplink_time (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) :
    (p.b : ℝ) * (uplinkPayload p (config p) + DistributedTemplate.clockBits : ℕ) ≤ phaseScale p := by
  cases hf : fullUplink p
  · have hb := framed_payload_cost p (uplinkCount p) (uplinkWidth p) (uplinkCount p).pos
    have hc := (compressed_uplink_count p hf).2.2
    simpa only [uplinkPayload, config, hf, Bool.false_eq_true, ↓reduceIte, uplinkCost] using hb.trans hc
  · have hb := framed_payload_cost p p.d (uplinkWidth p) hd
    have hc : p.d * uplinkCost p ≤ phaseScale p := by
      have he : uplinkCost p = 0 ∨ p.d * uplinkCost p ≤ phaseScale p := by
        simpa only [fullUplink, decide_eq_true_eq] using hf
      rcases he with hz | he
      · rw [hz, mul_zero]
        exact (phaseScale_pos p hh).le
      · exact he
    simpa only [uplinkPayload, config, hf, ↓reduceIte, uplinkCost] using hb.trans hc

lemma compressed_downlink_time (p : Params) (hf : fullDownlink p = false) :
    (p.b : ℝ) * ((downlinkCount p : ℕ) * downlinkWidth p + DistributedTemplate.clockBits : ℕ) ≤
      phaseScale p := by
  exact (framed_payload_cost p (downlinkCount p) (downlinkWidth p) (downlinkCount p).pos).trans
    (by simpa only [downlinkCost] using (compressed_downlink_count p hf).2.2)

lemma batch_rounding (p : Params) (hd : 0 < p.d) :
    (batch p : ℝ) ≤ 1 + 16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2) := by
  have hω := DistributedNormalizedPrecision.compressionVariance_nonneg p hd
  have hx : 0 ≤ 16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  change ((max 1 ⌈16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2)⌉₊ : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

lemma mixed_noise_scale (p : Params) (hε : 0 < p.ε) :
    65536 * p.d * p.σ ^ 2 * (computationTime p : ℝ) * uplinkCost p ≤
      phaseScale p ^ 2 * (p.n * p.ε ^ 2) := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hN : 0 < (p.n : ℝ) * p.ε ^ 2 := by positivity
  let z := p.d * p.σ ^ 2 * (computationTime p : ℝ) * uplinkCost p / (p.n * p.ε ^ 2)
  have hz : 0 ≤ z := by dsimp [z]; exact div_nonneg (by positivity [uplinkCost_nonneg p]) hN.le
  have hb : 256 * Real.sqrt z ≤ phaseScale p := (phaseScale_bounds p).2.2.2.2.2.2.2.1
  have hp := pow_le_pow_left₀ (show 0 ≤ 256 * Real.sqrt z by positivity) hb 2
  rw [mul_pow, Real.sq_sqrt hz] at hp
  norm_num at hp
  apply (div_le_iff₀ hN).mp
  convert hp using 1
  dsimp [z]
  ring

lemma batch_time (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    (batch p : ℝ) * computationTime p ≤ 65 * phaseScale p := by
  have hH : (0 : ℝ) ≤ computationTime p := (computationTime p).property
  have ht := phaseScale_pos p hh
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hN : 0 < (p.n : ℝ) * p.ε ^ 2 := by positivity
  have hbase := (phaseScale_bounds p).2.2.2.2.2.2.1
  have hbase' : 256 * p.σ ^ 2 * (computationTime p : ℝ) ≤ phaseScale p * (p.n * p.ε ^ 2) := by
    apply (div_le_iff₀ hN).mp
    convert hbase using 1
    ring
  have hm := mixed_noise_scale p hε
  have hv := mul_le_mul_of_nonneg_right (compression_variance_scale p hd hh)
    (show 0 ≤ p.σ ^ 2 * (computationTime p : ℝ) by positivity)
  have hc : 32768 * compressionVariance p * p.σ ^ 2 * (computationTime p : ℝ) ≤
      phaseScale p * (p.n * p.ε ^ 2) := by
    apply (mul_le_mul_iff_left₀ ht).mp
    nlinarith
  have hbatch := mul_le_mul_of_nonneg_right (batch_rounding p hd) hH
  have hHbound := (phaseScale_bounds p).1
  have hsum : (1 + 16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2)) *
      (computationTime p : ℝ) ≤ 65 * phaseScale p := by
    apply (mul_le_mul_iff_left₀ hN).mp
    field_simp
    nlinarith
  exact hbatch.trans hsum

lemma refresh_cost_scale (p : Params) (hh : ∀ i, 0 < p.h i)
    (hf : fullDownlink p = false) :
    p.d * downlinkCost p ≤ 2 * (refreshPeriod p : ℝ) * phaseScale p := by
  have ht := phaseScale_pos p hh
  have hlo := Nat.lt_floor_add_one (p.d * downlinkCost p / phaseScale p)
  have he : (refreshPeriod p : ℝ) = max 1 (⌊p.d * downlinkCost p / phaseScale p⌋₊ : ℝ) := by
    simp only [refreshPeriod, hf, Bool.false_eq_true, ↓reduceIte]
    change ((max 1 ⌊p.d * downlinkCost p / phaseScale p⌋₊ : ℕ) : ℝ) = _
    rw [Nat.cast_max, Nat.cast_one]
  have hr : 1 ≤ (refreshPeriod p : ℝ) := by rw [he]; exact le_max_left _ _
  have hfloor : (⌊p.d * downlinkCost p / phaseScale p⌋₊ : ℝ) ≤ refreshPeriod p := by
    rw [he]
    exact le_max_right _ _
  apply (div_le_iff₀ ht).mp
  linarith

lemma refresh_sum (p : Params) (K : ℕ) (a : ℝ) :
    (∑ k ∈ Finset.range K, if LongTails.Algorithms.DistributedNormalizedDownlink.refresh (config p) k
      then a else 0) = (K / (refreshPeriod p : ℕ) : ℕ) * a := by
  simp only [LongTails.Algorithms.DistributedNormalizedDownlink.refresh, config, decide_eq_true_eq,
    ← Nat.dvd_iff_mod_eq_zero]
  rw [← Finset.sum_filter, Finset.sum_const, Nat.card_multiples, nsmul_eq_mul]

lemma downlink_time_sum (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) (K : ℕ) :
    (∑ k ∈ Finset.range K,
      (p.b : ℝ) * (downlinkPayload p (config p) k + DistributedTemplate.clockBits : ℕ)) ≤
      3 * K * phaseScale p := by
  have ht := (phaseScale_pos p hh).le
  cases hf : fullDownlink p
  · have hs := compressed_downlink_time p hf
    have hr := refresh_cost_scale p hh hf
    have hpoint (k : ℕ) :
        (p.b : ℝ) * (downlinkPayload p (config p) k + DistributedTemplate.clockBits : ℕ) ≤
          phaseScale p + if LongTails.Algorithms.DistributedNormalizedDownlink.refresh (config p) k
            then p.d * downlinkCost p else 0 := by
      unfold downlinkPayload
      split_ifs
      · exact (framed_payload_cost p p.d (downlinkWidth p) hd).trans (le_add_of_nonneg_left ht)
      · simpa only [config, add_zero] using hs
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range K) => hpoint k)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, refresh_sum] at hsum
    have hcount : ((K / (refreshPeriod p : ℕ) : ℕ) : ℝ) * refreshPeriod p ≤ K := by
      exact_mod_cast Nat.div_mul_le_self K (refreshPeriod p)
    have hterm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (K / (refreshPeriod p : ℕ)))
    have hcount' := mul_le_mul_of_nonneg_right hcount ht
    nlinarith
  · have hr : refreshPeriod p = 1 := by simp only [refreshPeriod, hf, ↓reduceIte]
    have hc : p.d * downlinkCost p ≤ phaseScale p := by
      have he : downlinkCost p = 0 ∨ p.d * downlinkCost p ≤ phaseScale p := by
        simpa only [fullDownlink, decide_eq_true_eq] using hf
      rcases he with hz | he
      · simpa only [hz, mul_zero] using ht
      · exact he
    have hpoint (k : ℕ) :
        (p.b : ℝ) * (downlinkPayload p (config p) k + DistributedTemplate.clockBits : ℕ) ≤ phaseScale p := by
      simpa only [downlinkPayload, LongTails.Algorithms.DistributedNormalizedDownlink.refresh,
        config, hr, PNat.one_coe, Nat.mod_one, decide_true, ↓reduceIte, downlinkCost] using
        (framed_payload_cost p p.d (downlinkWidth p) hd).trans hc
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range K) => hpoint k)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    nlinarith [mul_nonneg (Nat.cast_nonneg K) ht]

lemma execution_time (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    (executionTime p (config p) : ℝ) ≤ (iterations p : ℝ) * (69 * phaseScale p + 2 * p.l) := by
  have hb := batch_time p hd hε hh
  have hu := uplink_time p hd hh
  have hdow := downlink_time_sum p hd hh (iterations p)
  have hround (k : ℕ) : (roundTime p (config p) k : ℝ) ≤
      66 * phaseScale p + 2 * p.l +
        (p.b : ℝ) * (downlinkPayload p (config p) k + DistributedTemplate.clockBits : ℕ) := by
    have hn : 0 ≤ (p.l : ℝ) + (p.b : ℝ) *
        (downlinkPayload p (config p) k + DistributedTemplate.clockBits : ℕ) := by positivity
    dsimp only [roundTime]
    split_ifs <;> simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_zero]
    all_goals
      change (batch p : ℝ) * (computationTime p : ℝ) + (p.l : ℝ) +
        (p.b : ℝ) * (uplinkPayload p (config p) + DistributedTemplate.clockBits : ℕ) + _ ≤ _
      linarith
  unfold executionTime
  rw [NNReal.coe_sum]
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (iterations p)) => hround k)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  change (∑ k ∈ Finset.range (iterations p), (roundTime p (config p) k : ℝ)) ≤ _
  nlinarith

lemma execution_time_scale (p : Params) (hd : 0 < p.d) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ)
    (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    (executionTime p (config p) : ℝ) ≤
      33554432 * accuracyScale p * ((p.l : ℝ) + phaseScale p / 256) := by
  have hA : 0 ≤ accuracyScale p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DistributedNormalizedPrecision.accuracyScale_ge_one p hL hΔ)
  have ht := (phaseScale_pos p hh).le
  have hl : (0 : ℝ) ≤ p.l := p.l.property
  have hK := mul_le_mul_of_nonneg_right
    (DistributedNormalizedPrecision.iterations_le_scale p hL hΔ)
    (show 0 ≤ 69 * phaseScale p + 2 * (p.l : ℝ) by positivity)
  have he := (execution_time p hd hε hh).trans hK
  nlinarith [mul_nonneg hA ht, mul_nonneg hA hl]

lemma execution_time_explicit (p : Params) (hd : 0 < p.d) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ)
    (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    executionTime p (config p) ≤ Real.toNNReal (33554432 * (1 + p.L * p.Δ / p.ε ^ 2) * ((p.l : ℝ) + (max ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / p.n) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) / Real.sqrt p.n) (max (((p.d : ℝ) ^ 3 * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) ^ 2 / p.n) ^ (1 / 3 : ℝ)) (max (p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) / (p.n * p.ε ^ 2)) (max (Real.sqrt (p.d * p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / (p.n * p.ε ^ 2))) (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) * min 1 (Real.sqrt (p.Q * p.ε) / p.L)))))))))))) := by
  have he : (33554432 * (1 + p.L * p.Δ / p.ε ^ 2) * ((p.l : ℝ) + (max ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / p.n) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) / Real.sqrt p.n) (max (((p.d : ℝ) ^ 3 * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) ^ 2 / p.n) ^ (1 / 3 : ℝ)) (max (p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) / (p.n * p.ε ^ 2)) (max (Real.sqrt (p.d * p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / (p.n * p.ε ^ 2))) (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) * min 1 (Real.sqrt (p.Q * p.ε) / p.L)))))))))))) = 33554432 * accuracyScale p * ((p.l : ℝ) + phaseScale p / 256) := by
    unfold accuracyScale phaseScale computationTime uplinkCost downlinkCost uplinkWidth downlinkWidth
    simp only [accuracyScale]
    norm_num [Nat.add_assoc]
  rw [he]
  exact NNReal.coe_le_coe.mp ((execution_time_scale p hd hL hΔ hε hh).trans (Real.le_coe_toNNReal _))

end LongTails.Proofs.DistributedNormalizedRuntime
