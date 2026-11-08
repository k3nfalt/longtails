import LongTails.Algorithms.BirchCausalTuning
import LongTails.Proofs.BirchCausalPhysicalCertificate

namespace LongTails.Proofs.BirchCausalTuning

open LongTails.Algorithms.BirchCausalTuning
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Proofs.BirchNonEuclideanScheduling

lemma minimum_batch (H B : ℕ) (hB : 4 * H ≤ B) :
    4 * (H * (B / (8 * H) + 1)) ≤ B := by
  let R := B / (8 * H)
  have hR : 8 * H * R ≤ B := Nat.mul_div_le B (8 * H)
  by_cases hz : R = 0
  · change 4 * (H * (R + 1)) ≤ B
    simpa [hz] using hB
  · have hr : 1 ≤ R := Nat.pos_of_ne_zero hz
    have hh : H ≤ H * R := by nlinarith
    change 4 * (H * (R + 1)) ≤ B
    nlinarith

lemma matched_calls (m H B R D T Q t z : ℝ)
    (hm : 1 ≤ m) (hH : 1 ≤ H) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hT : T ≤ 48 * t * D)
    (hD : H * D = B + 2 * H * (R + 1) + 1)
    (hBlow : 8 * H * R ≤ B) (hBup : B ≤ 8 * H * (R + 1))
    (hBnoise : B ≤ 4 * H + 32 * z)
    (hQ : Q ≤ B + H * (m + T * (1 + (m - 1) / (R + 1)))) :
    Q ≤ (5 + 528 * t) * (m * H) + (32 + 1920 * t) * z := by
  have hr : 0 < R + 1 := by linarith
  have hh : 0 ≤ H := by linarith
  have hm1 : 0 ≤ m - 1 := by linarith
  have hf : 0 ≤ 1 + (m - 1) / (R + 1) := by positivity
  have ha : H * D ≤ (5 / 4 : ℝ) * B + 3 * H := by nlinarith
  have hb : H * D / (R + 1) ≤ 11 * H := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have he : H * D * (1 + (m - 1) / (R + 1)) ≤ 11 * m * H + 40 * z := by
    have hid : H * D * (1 + (m - 1) / (R + 1)) =
        H * D + (m - 1) * (H * D / (R + 1)) := by ring
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hb hm1
    nlinarith
  have hbase : B + H * m ≤ 5 * m * H + 32 * z := by nlinarith
  calc
    Q ≤ B + H * (m + 48 * t * D * (1 + (m - 1) / (R + 1))) := by
      apply hQ.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ hh
      exact add_le_add_right (mul_le_mul_of_nonneg_right hT hf) m
    _ = B + H * m + 48 * t * (H * D * (1 + (m - 1) / (R + 1))) := by ring
    _ ≤ 5 * m * H + 32 * z + 48 * t * (11 * m * H + 40 * z) :=
      add_le_add hbase (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by ring


lemma batch_minimum (H : ℕ) (κ σ ε : ℝ) : 4 * H ≤ batchSize H κ σ ε := le_max_left _ _

lemma batch_upper (H : ℕ) (κ σ ε : ℝ) (hH : 0 < H) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    (batchSize H κ σ ε : ℝ) ≤ 4 * H + 32 * (κ * σ ^ 2 / ε) := by
  have hz : 0 ≤ 32 * κ * σ ^ 2 / ε := by positivity
  have hc := (Nat.ceil_lt_add_one hz).le
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  simp only [batchSize, Nat.cast_max, Nat.cast_mul, Nat.cast_ofNat]
  apply max_le
  · linarith [show 0 ≤ 32 * (κ * σ ^ 2 / ε) by positivity]
  · nlinarith [show 32 * κ * σ ^ 2 / ε = 32 * (κ * σ ^ 2 / ε) by ring]

lemma batch_noise (H : ℕ) (κ σ ε : ℝ) (hH : 0 < H) (hε : 0 < ε) :
    16 * κ * σ ^ 2 * (1 / (batchSize H κ σ ε : ℝ)) ≤ ε / 2 := by
  have hB : (0 : ℝ) < batchSize H κ σ ε := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < 4 * H) (batch_minimum H κ σ ε)
  have hb : 32 * κ * σ ^ 2 / ε ≤ (batchSize H κ σ ε : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (4 * H) ⌈32 * κ * σ ^ (2 : ℕ) / ε⌉₊))
  have hm := (div_le_iff₀ hε).1 hb
  rw [mul_one_div]
  apply (div_le_iff₀ hB).2
  nlinarith

lemma drift_lower (H B : ℕ) (hH : 0 < H) : 2 ≤ drift H B := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  unfold drift
  apply (le_div_iff₀ hHr).2
  nlinarith [show (0 : ℝ) ≤ H * packetCutoff H B by positivity]

lemma drift_certificate (H B : ℕ) (hH : 0 < H) :
    ((((max (H - 1) (2 * (H * (packetCutoff H B + 1)) + 1) : ℕ) : ℝ) + B) / H) = drift H B := by
  have hr : H ≤ H * (packetCutoff H B + 1) := by nlinarith
  rw [max_eq_right (by omega)]
  simp only [drift, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

lemma horizon_positive (H B : ℕ) (L Δ ε : ℝ) : 0 < horizon H B L Δ ε := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma horizon_upper (H B : ℕ) (L Δ ε : ℝ) (hH : 0 < H) (hL : 0 < L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    ((horizon H B L Δ ε - 1 : ℕ) : ℝ) ≤ 48 * (L * Δ / ε) * drift H B := by
  have hd := drift_lower H B hH
  have hz : 0 ≤ 48 * L * Δ * drift H B / ε := by positivity
  have hc := (Nat.ceil_lt_add_one hz).le
  have hk := horizon_positive H B L Δ ε
  rw [Nat.cast_sub (by omega : 1 ≤ horizon H B L Δ ε), Nat.cast_one]
  have hu : (horizon H B L Δ ε : ℝ) ≤ 48 * L * Δ * drift H B / ε + 1 := by
    simp only [horizon, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hc
  nlinarith [show 48 * L * Δ * drift H B / ε = 48 * (L * Δ / ε) * drift H B by ring]

lemma step_conditions (H B : ℕ) (L : ℝ) (hH : 0 < H) (hL : 0 < L) :
    0 < stepSize H B L ∧ stepSize H B L * L ≤ 1 / 2 ∧
      stepSize H B L * L * drift H B = 1 / 4 := by
  have hd := drift_lower H B hH
  have hd0 : 0 < drift H B := by linarith
  have he : stepSize H B L * L = 1 / (4 * drift H B) := by unfold stepSize; field_simp
  refine ⟨by unfold stepSize; positivity, ?_, ?_⟩
  · rw [he]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  · rw [he]
    field_simp

lemma tuning_valid (H B : ℕ) (L : ℝ) (hH : 0 < H) (hB : 0 < B) (hL : 0 < L) :
    LongTails.Setups.BirchNonEuclidean.Tuning.Valid
      (LongTails.Setups.BirchNonEuclidean.canonicalTuning (stepSize H B L) B) := by
  refine ⟨fun _ => (step_conditions H B L hH hL).1.le, fun _ => ⟨by change 0 ≤ 1 / (B : ℝ); positivity, ?_⟩⟩
  change 1 / (B : ℝ) ≤ 1
  apply (div_le_one (by exact_mod_cast hB : (0 : ℝ) < B)).2
  exact_mod_cast hB

lemma accuracy_bound (H : ℕ) (L Δ κ σ ε : ℝ) (hH : 0 < H)
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let B := batchSize H κ σ ε
    let K := horizon H B L Δ ε
    6 * Δ / (stepSize H B L * K) + 16 * κ * σ ^ 2 * (1 / (B : ℝ)) ≤ ε := by
  let B := batchSize H κ σ ε
  let K := horizon H B L Δ ε
  have hk : (0 : ℝ) < K := by exact_mod_cast horizon_positive H B L Δ ε
  have hstep := step_conditions H B L hH hL
  have hd := drift_lower H B hH
  have hklow : 48 * L * Δ * drift H B / ε ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈48 * L * Δ * drift H B / ε⌉₊))
  have hklow' := (div_le_iff₀ hε).1 hklow
  have hprod : 48 * L * Δ * drift H B * stepSize H B L ≤ (K : ℝ) * ε * stepSize H B L :=
    mul_le_mul_of_nonneg_right hklow' hstep.1.le
  have hinit : 6 * Δ / (stepSize H B L * K) ≤ ε / 2 := by
    apply (div_le_iff₀ (mul_pos hstep.1 hk)).2
    have he := hstep.2.2
    nlinarith
  exact (add_le_add hinit (batch_noise H κ σ ε hH hε)).trans_eq (by ring)

lemma scheduler_calls_real {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hK : 0 < K) (hm : 0 < m) :
    ((B + H * (K + (ignored (finalSchedule H K B word)).length) : ℕ) : ℝ) ≤
      B + (H : ℝ) * (m + ((K - 1 : ℕ) : ℝ) * (1 + ((m : ℝ) - 1) / (packetCutoff H B + 1))) := by
  let R := packetCutoff H B
  let rejected := (finalSchedule H K B word).rejected.length
  have hr : 0 < (R : ℝ) + 1 := by positivity
  have hrej : ((R : ℝ) + 1) * (rejected : ℝ) ≤ ((m : ℝ) - 1) * ((K - 1 : ℕ) : ℝ) := by
    have hh := scheduleRun_rejected_final_bound K R word (completionLimit m K R) hm
    have hcast : ((R + 1 : ℕ) : ℝ) * (rejected : ℝ) ≤ ((m - 1 : ℕ) : ℝ) * ((K - 1 : ℕ) : ℝ) := by
      exact_mod_cast hh
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ m)] using hcast
  have hrej' : (rejected : ℝ) ≤ ((m : ℝ) - 1) * ((K - 1 : ℕ) : ℝ) / (R + 1) :=
    (le_div_iff₀ hr).2 (by nlinarith)
  rw [ignored_length H K B word hK hm]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ K)]
  simp only [Nat.cast_one]
  change (B : ℝ) + H * (K + (rejected + (m - 1))) ≤ _
  have hmul := mul_le_mul_of_nonneg_left hrej' (show (0 : ℝ) ≤ H by positivity)
  rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one] at hmul
  nlinarith [show (((m : ℝ) - 1) * ((K : ℝ) - 1) / ((R : ℝ) + 1)) =
    ((K : ℝ) - 1) * (((m : ℝ) - 1) / ((R : ℝ) + 1)) by ring]

lemma tuned_calls {m : ℕ} (H : ℕ) (L Δ κ σ ε : ℝ) (word : ℕ → ℕ → ℕ → Fin m)
    (hH : 0 < H) (hm : 0 < m) (hL : 0 < L) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    let B := batchSize H κ σ ε
    let K := horizon H B L Δ ε
    ((B + H * (K + (ignored (finalSchedule H K B (word K B))).length) : ℕ) : ℝ) ≤
      (5 + 528 * (L * Δ / ε)) * ((m : ℝ) * H) + (32 + 1920 * (L * Δ / ε)) * (κ * σ ^ 2 / ε) := by
  let B := batchSize H κ σ ε
  let K := horizon H B L Δ ε
  let R := packetCutoff H B
  have hk := horizon_positive H B L Δ ε
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hD : (H : ℝ) * drift H B = B + 2 * H * ((R : ℝ) + 1) + 1 := by
    unfold drift
    dsimp only [R]
    field_simp
  have hlo : (8 : ℝ) * H * R ≤ B := by
    exact_mod_cast (Nat.mul_div_le B (8 * H))
  have hup : (B : ℝ) ≤ 8 * H * ((R : ℝ) + 1) := by
    exact_mod_cast (Nat.lt_mul_div_succ B (by omega : 0 < 8 * H)).le
  exact matched_calls m H B R (drift H B) ((K - 1 : ℕ) : ℝ)
    ((B + H * (K + (ignored (finalSchedule H K B (word K B))).length) : ℕ) : ℝ) (L * Δ / ε) (κ * σ ^ 2 / ε)
    (by exact_mod_cast hm) (by exact_mod_cast hH) (by positivity) (by positivity)
    (horizon_upper H B L Δ ε hH hL hΔ hε) hD hlo hup (batch_upper H κ σ ε hH hκ hε)
    (scheduler_calls_real H K B (word K B) hk hm)

lemma tuned_calls_nat {m : ℕ} (H : ℕ) (L Δ κ σ ε : ℝ) (word : ℕ → ℕ → ℕ → Fin m)
    (hH : 0 < H) (hm : 0 < m) (hL : 0 < L) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    let B := batchSize H κ σ ε
    let K := horizon H B L Δ ε
    B + H * (K + (ignored (finalSchedule H K B (word K B))).length) ≤
      ⌈(5 + 528 * (L * Δ / ε)) * ((m : ℝ) * H) + (32 + 1920 * (L * Δ / ε)) * (κ * σ ^ 2 / ε)⌉₊ := by
  have h := (tuned_calls H L Δ κ σ ε word hH hm hL hΔ hκ hε).trans (Nat.le_ceil _)
  exact_mod_cast h

end LongTails.Proofs.BirchCausalTuning
