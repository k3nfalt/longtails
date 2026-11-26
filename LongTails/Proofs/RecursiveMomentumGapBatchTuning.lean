import LongTails.Algorithms.RecursiveMomentumGapBatch
import LongTails.Theorems.RecursiveMomentumAffineVariance
import LongTails.Proofs.RecursiveMomentumGapBatchVariance

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RecursiveMomentumGapBatch

open RecursiveMomentum NormalizedStorm LongTails.Setups.AffineVarianceMeanSquaredSmooth

lemma calls_le (q : Params) (h : spec.valid q) :
    (↑(batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε + horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε) : ℝ) ≤
    let D := (q.L + q.Lbar) * q.Δ / q.ε^2
    let z := q.Λ / q.ε
    3 + 8*z^2 + 20*D + 124*q.Γ*D + 120*z*D := by
  obtain ⟨hl, hb, hg, hv, hd, he⟩ := h
  dsimp only
  unfold batch horizon
  push_cast
  have h₁ := Nat.ceil_lt_add_one (show 0 ≤ 8*(q.Λ/q.ε)^2 +
    64*q.Γ*((q.L+q.Lbar)*q.Δ/q.ε^2) by positivity)
  have h₂ := Nat.ceil_lt_add_one (show 0 ≤ 20*(1+3*q.Γ+6*(q.Λ/q.ε))*
    ((q.L+q.Lbar)*q.Δ/q.ε^2) by positivity)
  linarith

lemma budget_lt_existing (q : Params) (h : spec.valid q) (i : Fin spec.numOracles) :
    batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε + horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε <
      RecursiveMomentum.budget q i := by
  have hc := calls_le q h
  obtain ⟨hl,hb,hg,hv,hd,he⟩ := h
  unfold RecursiveMomentum.budget
  have hr := Nat.le_ceil (16 + 131*q.Γ^2 + 5*q.Γ^4 + 516*q.Λ^2/q.ε^2 +
    64*(q.L+q.Lbar)*(1+3*q.Γ)*q.Δ/q.ε^2 + 384*(q.L+q.Lbar)*q.Λ*q.Δ/q.ε^3)
  let D := (q.L+q.Lbar)*q.Δ/q.ε^2
  let z := q.Λ/q.ε
  change _ ≤ 3+8*z^2+20*D+124*q.Γ*D+120*z*D at hc
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hid : 516*q.Λ^2/q.ε^2 + 64*(q.L+q.Lbar)*(1+3*q.Γ)*q.Δ/q.ε^2 +
      384*(q.L+q.Lbar)*q.Λ*q.Δ/q.ε^3 = 516*z^2 + 64*(1+3*q.Γ)*D + 384*z*D := by
    dsimp [D,z]; field_simp
  exact_mod_cast (show (↑(batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε + horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε) : ℝ) <
    (⌈16 + 131*q.Γ^2 + 5*q.Γ^4 + 516*q.Λ^2/q.ε^2 +
      64*(q.L+q.Lbar)*(1+3*q.Γ)*q.Δ/q.ε^2 + 384*(q.L+q.Lbar)*q.Λ*q.Δ/q.ε^3⌉₊ : ℝ) + 2 by
    linarith [sq_nonneg q.Γ, sq_nonneg (q.Γ^2), sq_nonneg z, mul_nonneg hg hD, mul_nonneg hz hD])

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

variable {Δ ε : ℝ}
local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma initial_error (H : AffineHyp p F g L Lbar Γ Λ lower) (h : MTune L Lbar Γ Λ Δ ε)
    (x : E) (hx : F x - lower ≤ Δ) :
    ∫ ξ, ‖batchMean g x ξ (batch L Lbar Γ Λ Δ ε) - gradient F x‖^2 ∂P ≤ ε^2/4 := by
  let b := batch L Lbar Γ Λ Δ ε
  have hε := h.ε_pos
  have hΓ := h.Γ_nn
  have hS := h.K_pos
  have hΔ := h.Δ_nn
  have hm := ((abcHyp H h.Lbar_nn hΓ).batch_moment x b).2
  have hb : 8*(Λ/ε)^2 + 64*Γ*((L+Lbar)*Δ/ε^2) ≤ (b:ℝ) := by
    dsimp [b,batch]; push_cast; linarith [Nat.le_ceil (8*(Λ/ε)^2+64*Γ*((L+Lbar)*Δ/ε^2))]
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ε)
  have hid : (8*(Λ/ε)^2 + 64*Γ*((L+Lbar)*Δ/ε^2))*ε^2 =
      8*Λ^2 + 64*Γ*(L+Lbar)*Δ := by field_simp
  rw [hid] at hh
  apply le_of_mul_le_mul_left (a := (b:ℝ)) _ (by dsimp [b,batch]; positivity)
  linarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 12*Γ*(L+Lbar) by positivity),
    mul_nonneg (mul_nonneg hΓ hS.le) hΔ]

lemma horizon_gap (h : MTune L Lbar Γ Λ Δ ε) :
    2 * Δ ≤ mGamma L Lbar Γ Λ ε * ((horizon L Lbar Γ Λ Δ ε : ℝ)+1) * ε^2 * (2/5) := by
  have hε := h.ε_pos
  have hS := h.K_pos
  have hr := h.r_ge
  have hid : 1+3*Γ+6*(Λ/ε) = mR Γ Λ ε := by unfold mR; ring
  have hh := Nat.le_ceil (20*(1+3*Γ+6*(Λ/ε))*((L+Lbar)*Δ/ε^2))
  change _ ≤ (horizon L Lbar Γ Λ Δ ε : ℝ) at hh
  rw [hid] at hh
  have hh' := (div_le_iff₀ (sq_pos_of_pos hε)).mp
    (show 20*mR Γ Λ ε*((L+Lbar)*Δ) / ε^2 ≤ (horizon L Lbar Γ Λ Δ ε : ℝ) by
      convert hh using 1; ring)
  unfold mGamma
  field_simp
  nlinarith [sq_nonneg ε]

end OracleTemplate.RecursiveMomentumGapBatch
