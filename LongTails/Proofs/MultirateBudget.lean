import LongTails.Proofs.MultirateReservations
import LongTails.Proofs.MultiscaleAggregateRuntime

namespace LongTails.Proofs.MultirateBudget

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateCalendar LongTails.Algorithms.MultirateAllocation
open MultirateReservations

variable {p : Params}

lemma finish_bound (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (hΔ : 0 ≤ p.Δ)
    (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    let δ := p.ε / 1024
    let τ := p.Δ / ((p.n : ℝ) * δ^2)
    let K := 1 + ⌈τ * ∑ i, p.L i⌉₊
    let c := p.l + p.b * (clockBits + p.d * (4 + Nat.size ((p.n : ℕ) * (p.d + 1)) + K.size) : ℕ)
    finishTime p ≤ (4 * K + 2 : ℕ) * c + 6 * Finset.univ.sup p.h +
      Real.toNNReal (10 * (∑ i, (p.h i : ℝ) * p.σ i^2) / ((p.n : ℝ) * δ)^2 +
        2 * τ * ((∑ i, p.L i * p.h i) + 2 * (∑ i, p.σ i * Real.sqrt (p.L i * p.h i))^2 / ((p.n : ℝ) * δ)^2)) := by
  intro δ τ K c
  let W := ∑ i, p.L i
  let A := ∑ i, p.L i * service p i
  let V := (∑ i, startupWeight p i) / ((p.n : ℝ) * δ)^2
  let B := (∑ i, p.L i * p.h i) + 2 * (∑ i, refreshWeight p i)^2 / ((p.n : ℝ) * δ)^2
  let H : Time := Finset.univ.sup p.h
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => hL i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => mul_nonneg (hL i) (MultirateCalendar.service_nonneg _ _)
  have hV : 0 ≤ V := div_nonneg (Finset.sum_nonneg fun i _ => MultirateAllocation.startup_nonneg i) (sq_nonneg _)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hτ : 0 ≤ τ := div_nonneg hΔ (mul_nonneg hn.le (sq_nonneg _))
  have hv (i) : service p i ≤ H + 2 * V := by
    have h := MultirateAllocation.startup_time hσ hε i
    have hH : (p.h i : ℝ) ≤ H := NNReal.coe_le_coe.mpr (Finset.le_sup (Finset.mem_univ i))
    dsimp only [V]
    change (p.h i : ℝ) * (batch p i : ℝ) ≤ p.h i + 2 * _ / ((p.n : ℝ) * δ)^2 at h
    unfold service
    linarith only [h, hH, show 2 * (∑ i, startupWeight p i) / ((p.n : ℝ) * δ)^2 =
        2 * ((∑ i, startupWeight p i) / ((p.n : ℝ) * δ)^2) by ring]
  have hb : A ≤ B := by simpa only [A,B,service,δ,precision,← mul_assoc] using MultirateAllocation.refresh_time hL hσ hε
  have hm : A/W ≤ H + 2*V := by
    rcases hW.eq_or_lt with hz | hp
    · rw [← hz, div_zero]
      positivity
    apply (div_le_iff₀ hp).mpr
    rw [mul_comm, show W*(H + 2*V) = ∑ i, p.L i * ((H : ℝ) + 2*V) by simp [W,Finset.sum_mul]]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hL i)
  have hratio : W*(A/W) ≤ A := by
    rcases hW.eq_or_lt with hz | hp
    · simpa [← hz] using hA
    · exact (mul_div_cancel₀ A hp.ne').le
  let θ := 2 * (aggregate p).L * p.Δ / Algorithms.MultiscaleAggregate.precision (aggregate p)^2
  have heq : θ = τ * W / 2 := by
    dsimp only [θ,τ,W,δ,Algorithms.MultiscaleAggregate.precision,aggregate]
    ring
  have hθ : θ ≤ τ*W := by rw [heq]; linarith [mul_nonneg hτ hW]
  have hsize : (Nat.size ⌈θ⌉₊) ≤ K.size := Nat.size_le_size ((Nat.ceil_le_ceil hθ).trans (Nat.le_add_left _ _))
  have hk : steps p ≤ 2 * (1 + ⌈θ⌉₊) := by
    have h := MultiscaleAggregateExecution.rounds_upper (p := aggregate p)
    have ht : 524288*(aggregate p).L*p.Δ/p.ε^2 = θ := by unfold θ Algorithms.MultiscaleAggregate.precision; change _ = 2 * _ * _ / (p.ε / 512)^2; ring
    rwa [ht] at h
  have hK : steps p ≤ 2*K := hk.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.ceil_le_ceil hθ) 1))
  have hK' : (steps p : ℝ) ≤ 4 + 2*τ*W := by
    have ht := Nat.ceil_lt_add_one (le_trans (by rw [heq]; positivity) (le_refl θ))
    have h : (steps p : ℝ) ≤ 2 * (1 + (⌈θ⌉₊ : ℝ)) := by exact_mod_cast hk
    linarith
  have hc : packetDelay p ≤ c := by
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ zero_le
    apply Nat.cast_le.mpr
    rw [Nat.add_comm]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left hsize _)) _
  have hC : packetTime p = (packetDelay p : ℝ) := by simp [packetTime,packetDelay]
  have hst : (firstFrame p : ℝ) ≤ 2*(packetDelay p : ℝ) + H + 2*V := by
    have hr : 0 ≤ 2*(packetDelay p : ℝ) + H + 2*V := by positivity
    apply (show (firstFrame p : ℝ) ≤ _ ↔ firstFrame p ≤ Real.toNNReal _ by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr]).mpr
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simp only [span,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,Real.coe_toNNReal _ hr]
    have h := hv i
    unfold service at h
    linarith
  have hKpos : (0 : ℝ) < steps p := by exact_mod_cast MultirateCalendar.steps_pos p
  have ha : (steps p : ℝ)*(A/W) ≤ 4*((H : ℝ)+2*V) + 2*τ*B := by
    calc
      _ ≤ (4 + 2*τ*W)*(A/W) := mul_le_mul_of_nonneg_right hK' (div_nonneg hA hW)
      _ = 4*(A/W) + 2*τ*(W*(A/W)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
        (mul_le_mul_of_nonneg_left (hratio.trans hb) (by positivity))
  have hmsg : (steps p : ℝ) * (2 * (packetDelay p : ℝ)) ≤ (4 * (K : ℝ)) * c := by
    calc
      _ ≤ (2*K : ℕ) * (2*(c : ℝ)) := mul_le_mul (Nat.cast_le.mpr hK)
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hc) (by norm_num)) (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  apply NNReal.coe_le_coe.mp
  simp only [finishTime, frame, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat, Real.coe_toNNReal _ (MultirateCalendar.slot_pos hh hL).le]
  have hinit : (steps p : ℝ) * ((H : ℝ) / steps p) = H := mul_div_cancel₀ _ hKpos.ne'
  have hcost : 10*V + 2*τ*B ≤ ((Real.toNNReal (10 * (∑ i, (p.h i : ℝ)*p.σ i^2) / ((p.n : ℝ)*δ)^2 +
      2*τ*B)) : ℝ) := by
    apply le_trans _ (Real.le_coe_toNNReal _)
    dsimp only [V,startupWeight]
    ring_nf
    rfl
  change (firstFrame p : ℝ) + (steps p : ℝ) * slot p ≤ (4 * (K : ℝ)+2)*c + 6*(H : ℝ) + _
  unfold slot
  change (firstFrame p : ℝ) + (steps p : ℝ)*(2*packetTime p + (H : ℝ)/steps p + A/W) ≤ _
  rw [hC, mul_add, mul_add, hinit]
  change (firstFrame p : ℝ) + ((steps p : ℝ) * (2 * packetDelay p) + H + (steps p : ℝ)*(A/W)) ≤
    (4*(K : ℝ)+2)*c + 6*H + ((Real.toNNReal (10 * (∑ i, (p.h i : ℝ)*p.σ i^2) / ((p.n : ℝ)*δ)^2 + 2*τ*B)) : ℝ)
  nlinarith only [hst, ha, hmsg, hcost, NNReal.coe_le_coe.mpr hc]

end LongTails.Proofs.MultirateBudget
