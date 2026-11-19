import LongTails.Proofs.WeightedInterpolationCost
import LongTails.Proofs.WeightedInterpolationExecution

namespace LongTails.Proofs.WeightedInterpolationRuntime

open DistributedTemplate LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open WeakInterpolationDesign WeightedInterpolationAllocation WeightedInterpolationCost

variable {p : Params}

lemma time_suffices (hp : spec.valid p) (T : Time)
    (hT : 2048*(p.σ^2/(information p*p.ε)+condition p*burn p*
      ((Finset.univ.sup p.h : Time)+ (p.l : ℝ) + p.b*(64+1024*(p.d : ℝ)*Nat.size ⌈magnitude p⌉₊))) ≤ (T : ℝ)) :
    Algorithms.DistributedBatchedSgd.timeBudget (transport p) (config p T) = T := by
  let cfg : Algorithms.DistributedBatchedSgd.Config (transport p) :=
    {iterations := ⟨rounds p, by unfold rounds; omega⟩, batch := batch p, width := width p}
  have hh : Algorithms.DistributedBatchedSgd.computationTime (transport p) cfg ≤ 2*batchTime p := by
    apply DistributedBatchedSgd.computationTime_le
    intro i
    change (batch p i : Time)*p.h i ≤ _
    apply NNReal.coe_le_coe.mp
    push_cast
    have hi : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
    have hb := (batch_bounds hp i).2
    rw [← mul_div_assoc] at hb
    exact (le_div_iff₀ hi).mp hb
  let H := ((Finset.univ.sup p.h : Time) : ℝ)
  let S := p.σ^2/(information p*p.ε)
  let L := (p.l : ℝ)+p.b*(64+1024*(p.d : ℝ)*Nat.size ⌈magnitude p⌉₊)
  let K : ℝ := rounds p
  have hH : 0 ≤ H := NNReal.coe_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hS : 0 ≤ S := div_nonneg (sq_nonneg _) (mul_nonneg (information_pos hp).le hp.2.2.2.2.2.2.le)
  have hP : 0 < (phase p : ℝ) := by exact_mod_cast phase_pos p
  have hI := information_pos hp
  have hε := hp.2.2.2.2.2.2
  have hsmall : (batchTime p : ℝ) ≤ H+256*S/phase p := by
    unfold batchTime
    rw [NNReal.coe_max, Real.coe_toNNReal _ (by positivity)]
    apply max_le (le_add_of_nonneg_right (by positivity))
    change 256*p.σ^2/(information p*p.ε*(phase p:ℝ)) ≤ _
    dsimp [S]
    rw [← div_div, ← mul_div_assoc]
    linarith
  have hK : K ≤ 3*phase p := by
    dsimp [K,rounds]
    push_cast
    linarith [show 1 ≤ (phase p : ℝ) by exact_mod_cast (show 1 ≤ phase p from phase_pos p)]
  have hs : K*(256*S/phase p) ≤ 768*S := by
    rw [←mul_div_assoc,div_le_iff₀ hP]
    linarith only [mul_le_mul_of_nonneg_right hK hS]
  have hb : ((p.d * (width p : ℕ) + clockBits : ℕ) : ℝ) ≤ 64+1024*(p.d : ℝ)*Nat.size ⌈magnitude p⌉₊ := by
    have hw : ((width p : ℕ):ℝ) ≤ 1024*(Nat.size ⌈magnitude p⌉₊ : ℝ) := by exact_mod_cast width_bound hp
    unfold clockBits
    push_cast
    linarith only [mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg p.d)]
  have hc := NNReal.coe_le_coe.mpr hh
  push_cast at hc
  have hr : (Algorithms.DistributedBatchedSgd.roundTime (transport p) cfg : ℝ) ≤ 2*(H+L)+2*(256*S/phase p) := by
    unfold Algorithms.DistributedBatchedSgd.roundTime
    push_cast
    push_cast at hb
    change (Algorithms.DistributedBatchedSgd.computationTime (transport p) cfg : ℝ) +
      2*((p.l : ℝ)+p.b*((p.d : ℝ)*((width p : ℕ):ℝ)+(clockBits:ℝ))) ≤ _
    dsimp [L]
    linarith only [hc,hsmall,mul_le_mul_of_nonneg_left hb p.b.coe_nonneg]
  have htotal : Algorithms.DistributedBatchedSgd.timeBudget (transport p) cfg ≤ T := by
    apply NNReal.coe_le_coe.mp
    change ((↑(rounds p) * Algorithms.DistributedBatchedSgd.roundTime (transport p) cfg + 0 : Time):ℝ) ≤ _
    push_cast
    change K*_+0 ≤ _
    rw [add_assoc (↑(Finset.univ.sup p.h) : ℝ)] at hT
    change 2048*(S+condition p*burn p*(H+L)) ≤ (T : ℝ) at hT
    have hmain := mul_le_mul_of_nonneg_right (rounds_bound hp) (add_nonneg hH hL)
    change K*(H+L) ≤ _ at hmain
    linarith only [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (rounds p) : 0 ≤ K),hmain,hs,hT,hS]
  change ↑cfg.iterations * Algorithms.DistributedBatchedSgd.roundTime (transport p) cfg +
    (T - Algorithms.DistributedBatchedSgd.timeBudget (transport p) cfg) = _
  have heq : Algorithms.DistributedBatchedSgd.timeBudget (transport p) cfg =
      ↑cfg.iterations * Algorithms.DistributedBatchedSgd.roundTime (transport p) cfg := add_zero _
  rw [←heq,add_tsub_cancel_of_le htotal]

end LongTails.Proofs.WeightedInterpolationRuntime
