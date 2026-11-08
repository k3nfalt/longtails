import LongTails.Proofs.BirchNonEuclideanPhysicalSuccess

namespace LongTails.Proofs.BirchNonEuclideanPhysicalBudget

open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Proofs.BirchNonEuclideanScheduling

lemma rejected_scaled {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (hH : 0 < H) (hm : 0 < m) :
    B * (finalSchedule H K B word).rejected.length ≤ 8 * H * m * K := by
  have hb : B ≤ 8 * H * (packetCutoff H B + 1) :=
    (Nat.lt_mul_div_succ B (by omega : 0 < 8 * H)).le
  have hd := scheduleRun_rejected_final_bound K (packetCutoff H B) word
    (completionLimit m K (packetCutoff H B)) hm
  change (packetCutoff H B + 1) * (finalSchedule H K B word).rejected.length ≤ (m - 1) * (K - 1) at hd
  calc
    _ ≤ (8 * H * (packetCutoff H B + 1)) * (finalSchedule H K B word).rejected.length :=
      Nat.mul_le_mul_right _ hb
    _ = (8 * H) * ((packetCutoff H B + 1) * (finalSchedule H K B word).rejected.length) := by ring
    _ ≤ (8 * H) * ((m - 1) * (K - 1)) := Nat.mul_le_mul_left _ hd
    _ ≤ (8 * H) * (m * K) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
    _ = _ := by ring

lemma physical_calls_bound {m : ℕ} (H K B : ℕ) (word : ℕ → ℕ → ℕ → Fin m)
    (hH : 0 < H) (hK : 0 < K) (hB : 0 < B) (hm : 0 < m) :
    (physicalLocalCalls H word K B : ℝ) ≤
      B + (H : ℝ) * K + (8 * m * H / B) * ((H : ℝ) * K) + (m : ℝ) * H := by
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hd : (B : ℝ) * (finalSchedule H K B (word K B)).rejected.length ≤ 8 * H * m * K := by
    exact_mod_cast rejected_scaled H K B (word K B) hH hm
  have hd' : ((finalSchedule H K B (word K B)).rejected.length : ℝ) ≤ 8 * H * m * K / B :=
    (le_div_iff₀ hB0).mpr (by nlinarith [hd])
  rw [physicalLocalCalls_exact H word K B hK hm]
  push_cast
  have hn : ((K + (finalSchedule H K B (word K B)).rejected.length + m - 1 : ℕ) : ℝ) ≤
      K + ((finalSchedule H K B (word K B)).rejected.length : ℝ) + m := by
    exact_mod_cast Nat.sub_le (K + (finalSchedule H K B (word K B)).rejected.length + m) 1
  calc
    _ ≤ B + (H : ℝ) * (K + 8 * H * m * K / B + m) := by
      gcongr
      linarith
    _ = _ := by ring

lemma physical_rate_algebra (m H B K : ℝ) (t z Q : ℝ)
    (hm : 1 ≤ m) (hH : 0 < H) (hB : 8 * H ≤ B) (ht : 0 ≤ t)
    (hupperB : B ≤ 9 * H + 64 * z)
    (hupperK : K ≤ 2 + 144 * t * (1 + B / H))
    (hQ : Q ≤ B + H * K + (8 * m * H / B) * (H * K) + m * H) :
    Q ≤ (64 + 9216 * t) * (m * H + z) := by
  have hB0 : 0 < B := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hratio : 8 * H / B ≤ 1 := (div_le_iff₀ hB0).mpr (by linarith)
  have hHK : H * K ≤ (2 + 144 * t) * H + 144 * t * B := by
    calc
      _ ≤ H * (2 + 144 * t * (1 + B / H)) := mul_le_mul_of_nonneg_left hupperK hH.le
      _ = _ := by field_simp; ring
  have hHK' : H * K ≤ (2 + 144 * t) * (m * H) + 144 * t * B := by
    apply hHK.trans
    gcongr
    nlinarith
  have hdelay : (8 * m * H / B) * (H * K) ≤ (2 + 1296 * t) * (m * H) := by
    calc
      _ ≤ (8 * m * H / B) * ((2 + 144 * t) * H + 144 * t * B) :=
        mul_le_mul_of_nonneg_left hHK (by positivity)
      _ = ((8 * H / B) * (2 + 144 * t) + 1152 * t) * (m * H) := by field_simp; ring
      _ ≤ (1 * (2 + 144 * t) + 1152 * t) * (m * H) := by gcongr
      _ = _ := by ring
  have hB' : B ≤ 9 * (m * H) + 64 * z := by
    apply hupperB.trans
    nlinarith
  calc
    Q ≤ (5 + 1440 * t) * (m * H) + (1 + 144 * t) * B := by nlinarith [hQ, hHK', hdelay]
    _ ≤ (5 + 1440 * t) * (m * H) + (1 + 144 * t) * (9 * (m * H) + 64 * z) := by gcongr
    _ = (14 + 2736 * t) * (m * H) + (64 + 9216 * t) * z := by ring
    _ ≤ (64 + 9216 * t) * (m * H) + (64 + 9216 * t) * z := by gcongr <;> norm_num
    _ = _ := by ring

lemma physical_tuned_calls {m : ℕ} (L Δ κ σ ε : ℝ) (H : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (hL : 0 < L) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ)
    (hε : 0 < ε) (hH : 0 < H) (hm : 0 < m) :
    let B := 8 * H + ⌈64 * κ * σ ^ 2 / ε⌉₊
    let K := 1 + ⌈144 * L * Δ * (1 + (B : ℝ) / H) / ε⌉₊
    (physicalLocalCalls H word K B : ℝ) ≤
      (64 + 9216 * (L * Δ / ε)) * ((m : ℝ) * H + κ * σ ^ 2 / ε) := by
  let B := 8 * H + ⌈64 * κ * σ ^ 2 / ε⌉₊
  let K := 1 + ⌈144 * L * Δ * (1 + (B : ℝ) / H) / ε⌉₊
  have hB : 8 * H ≤ B := by dsimp [B]; omega
  have hB0 : 0 < B := by omega
  have hK : 0 < K := by dsimp [K]; omega
  have ht : 0 ≤ L * Δ / ε := by positivity
  have hupperB : (B : ℝ) ≤ 9 * H + 64 * (κ * σ ^ 2 / ε) := by
    have hc := (Nat.ceil_lt_add_one (show 0 ≤ 64 * κ * σ ^ 2 / ε by positivity)).le
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    dsimp [B]
    push_cast
    rw [show 64 * κ * σ ^ 2 / ε = 64 * (κ * σ ^ 2 / ε) by ring] at hc ⊢
    nlinarith
  have hupperK : (K : ℝ) ≤ 2 + 144 * (L * Δ / ε) * (1 + (B : ℝ) / H) := by
    have hc := (Nat.ceil_lt_add_one (show 0 ≤ 144 * L * Δ * (1 + (B : ℝ) / H) / ε by positivity)).le
    dsimp [K]
    push_cast
    calc
      _ ≤ 2 + 144 * L * Δ * (1 + (B : ℝ) / H) / ε := by linarith
      _ = _ := by ring
  exact physical_rate_algebra m H B K (L * Δ / ε) (κ * σ ^ 2 / ε) _
    (by exact_mod_cast hm) (Nat.cast_pos.mpr hH) (by exact_mod_cast hB) ht hupperB hupperK
    (physical_calls_bound H K B word hH hK hB0 hm)

end LongTails.Proofs.BirchNonEuclideanPhysicalBudget
