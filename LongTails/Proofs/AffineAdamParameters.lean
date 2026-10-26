import LongTails.Algorithms.AffineHeavyTailedAdam
import Mathlib.Tactic

namespace LongTails.Proofs.AffineAdamParameters

open LongTails.Setups.AffineHeavyTailedAdam LongTails.Algorithms.AffineHeavyTailedAdam

lemma scale_pos (q : Params) (hq : spec.valid q) : 0 < q.L0 + q.L1 * q.ε := by
  rcases hq with ⟨h0, h1, hL, _, _, _, _, _, he⟩
  rcases lt_or_eq_of_le h0 with h | h
  · positivity
  · rw [← h] at hL ⊢
    simp only [zero_add] at hL ⊢
    positivity

lemma tuning_pos (q : Params) (hq : spec.valid q) :
    0 < (config q).η ∧ 0 < (config q).δ ∧ 0 < (config q).batchSize := by
  have hH := scale_pos q hq
  have he := hq.2.2.2.2.2.2.2.2
  dsimp [config]
  exact ⟨by positivity, by positivity, by omega⟩

lemma curvature_tuning (q : Params) (hq : spec.valid q) :
    (2 : ℝ) ^ 26 * (config q).η * (q.L0 / q.ε + q.L1) = 1 / 8 := by
  have hH := scale_pos q hq
  have he := hq.2.2.2.2.2.2.2.2
  dsimp [config]
  have hH' : q.L0 + q.ε * q.L1 ≠ 0 := by nlinarith
  field_simp [hH.ne', hH', he.ne']
  ring

lemma local_step (q : Params) (hq : spec.valid q) : q.L1 * (80 * (config q).η) ≤ 1 := by
  have h := curvature_tuning q hq
  have hη := (tuning_pos q hq).1
  have h0 := hq.1
  have he := hq.2.2.2.2.2.2.2.2
  have hh := mul_nonneg hη.le (div_nonneg h0 he.le)
  norm_num at h
  nlinarith

lemma batch_tuning {p s : ℝ} (hp : 1 < p) (hs : 0 ≤ s) :
    16384 * ((1 + ⌈((2 : ℝ) ^ 17 * s) ^ (p / (p - 1))⌉₊ : ℕ) : ℝ) ^ ((1 - p) / p) * s ≤ 1 / 8 := by
  let n : ℕ := 1 + ⌈((2 : ℝ) ^ 17 * s) ^ (p / (p - 1))⌉₊
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hb : ((2 : ℝ) ^ 17 * s) ^ (p / (p - 1)) ≤ (n : ℝ) := by
    have h := Nat.le_ceil (((2 : ℝ) ^ 17 * s) ^ (p / (p - 1)))
    dsimp [n]
    push_cast
    linarith
  have ha : 0 < (p - 1) / p := div_pos (by linarith) (by linarith)
  have he : p / (p - 1) * ((p - 1) / p) = 1 := by field_simp [show p ≠ 0 by linarith, show p - 1 ≠ 0 by linarith]
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ 17 * s) ^ (p / (p - 1))) hb ha.le
  rw [← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ) ^ 17 * s), he, Real.rpow_one] at hpow
  have hneg : (1 - p) / p = -((p - 1) / p) := by ring
  change 16384 * (n : ℝ) ^ ((1 - p) / p) * s ≤ _
  rw [hneg, Real.rpow_neg hn.le]
  have hd := Real.rpow_pos_of_pos hn ((p - 1) / p)
  apply (mul_le_mul_iff_of_pos_right hd).mp
  field_simp
  norm_num at hpow ⊢
  linarith

lemma noise_tuning (q : Params) (hq : spec.valid q) :
    4096 * (4 * ((config q).batchSize : ℝ) ^ ((1 - q.p) / q.p)) *
      (q.σ1 + (∑ i, q.σ0 i) / q.ε) ≤ 1 / 8 := by
  rcases hq with ⟨_, _, _, hs, hs1, hp, _, _, he⟩
  have hsum : 0 ≤ ∑ i, q.σ0 i := Finset.sum_nonneg (fun i _ => hs i)
  have h := batch_tuning hp (show 0 ≤ q.σ1 + (∑ i, q.σ0 i) / q.ε by positivity)
  convert h using 1
  dsimp [config]
  ring

lemma initialization_tuning (q : Params) (hq : spec.valid q) :
    q.Δ / (config q).η ≤ (((config q).lastIndex + 1 : ℕ) : ℝ) * q.ε / 8 := by
  have hH := scale_pos q hq
  have he := hq.2.2.2.2.2.2.2.2
  have hc := Nat.le_ceil ((2 : ℝ) ^ 32 * q.Δ * (q.L0 + q.L1 * q.ε) / q.ε ^ 2)
  have hη := (tuning_pos q hq).1
  dsimp [config] at *
  generalize hK : ⌈(2 : ℝ) ^ 32 * q.Δ * (q.L0 + q.L1 * q.ε) / q.ε ^ 2⌉₊ = K at *
  push_cast
  apply (div_le_iff₀ hη).mpr
  have hh := (div_le_iff₀ (sq_pos_of_pos he)).mp hc
  calc
    q.Δ ≤ ((K : ℝ) + 1) * q.ε ^ 2 / ((2 : ℝ) ^ 32 * (q.L0 + q.L1 * q.ε)) := by
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 32 * (q.L0 + q.L1 * q.ε))).mpr
      nlinarith [sq_nonneg q.ε]
    _ = _ := by field_simp; ring

lemma damping_tuning (q : Params) (hq : spec.valid q) : (q.d : ℝ) * (config q).δ ≤ q.ε / 8 := by
  have he := hq.2.2.2.2.2.2.2.2
  dsimp [config]
  have hd : (0 : ℝ) < (q.d : ℝ) + 1 := by positivity
  apply (mul_le_mul_iff_of_pos_right (show 0 < 8 * ((q.d : ℝ) + 1) by positivity)).mp
  field_simp
  nlinarith

lemma accuracy_from_bound (q : Params) (hq : spec.valid q) {S : ℝ} (hS : 0 ≤ S)
    (hbound : (1 - 4096 * (4 * ((config q).batchSize : ℝ) ^ ((1 - q.p) / q.p) * q.σ1) -
      2 ^ 26 * (config q).η * q.L1) * S ≤ q.Δ / (config q).η +
      (((config q).lastIndex + 1 : ℕ) : ℝ) *
        (4096 * (4 * ((config q).batchSize : ℝ) ^ ((1 - q.p) / q.p) * ∑ i, q.σ0 i) +
          2 ^ 26 * (config q).η * q.L0 + q.d * (config q).δ)) :
    S ≤ (((config q).lastIndex + 1 : ℕ) : ℝ) * q.ε := by
  let A := 4096 * (4 * ((config q).batchSize : ℝ) ^ ((1 - q.p) / q.p))
  let C := (2 : ℝ) ^ 26 * (config q).η
  let T : ℝ := ((config q).lastIndex + 1 : ℕ)
  let s0 := ∑ i, q.σ0 i
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by have h := (tuning_pos q hq).1; dsimp [C]; positivity
  have hs : 0 ≤ s0 := Finset.sum_nonneg (fun i _ => hq.2.2.2.1 i)
  have hσ := hq.2.2.2.2.1
  have he := hq.2.2.2.2.2.2.2.2
  have hL0 := hq.1
  have hL1 := hq.2.1
  have hn : A * (q.σ1 + s0 / q.ε) ≤ 1 / 8 := noise_tuning q hq
  have hc : C * (q.L0 / q.ε + q.L1) = 1 / 8 := curvature_tuning q hq
  have hn1 : A * q.σ1 ≤ 1 / 8 := by nlinarith [mul_nonneg hA (div_nonneg hs he.le)]
  have hc1 : C * q.L1 ≤ 1 / 8 := by nlinarith [mul_nonneg hC (div_nonneg hL0 he.le)]
  have hn0 : A * s0 ≤ q.ε / 8 := by
    have hh := mul_le_mul_of_nonneg_right hn he.le
    have hd : s0 / q.ε * q.ε = s0 := div_mul_cancel₀ _ he.ne'
    nlinarith [mul_nonneg (mul_nonneg hA hσ) he.le]
  have hc0 : C * q.L0 ≤ q.ε / 8 := by
    have hh := congrArg (fun r => r * q.ε) hc
    have hd : q.L0 / q.ε * q.ε = q.L0 := div_mul_cancel₀ _ he.ne'
    nlinarith [mul_nonneg (mul_nonneg hC hL1) he.le]
  have hcoeff : 3 / 4 * S ≤ (1 - A * q.σ1 - C * q.L1) * S := by nlinarith
  have hd := damping_tuning q hq
  have hi := initialization_tuning q hq
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hr := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hn0 hc0) hd) hT
  change q.Δ / (config q).η ≤ T * q.ε / 8 at hi
  have hb' : (1 - A * q.σ1 - C * q.L1) * S ≤ q.Δ / (config q).η +
      T * (A * s0 + C * q.L0 + q.d * (config q).δ) := by
    convert hbound using 1 <;> dsimp [A, C, T, s0] <;> ring
  change S ≤ T * q.ε
  nlinarith [mul_nonneg hT he.le]

end LongTails.Proofs.AffineAdamParameters
