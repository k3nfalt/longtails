import LongTails.Proofs.NonlinearTemporalTuning

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

lemma scaled_log_upper {r t : ℝ} (hr : 1 ≤ r) (ht : 0 ≤ t) :
    Real.log (2 + 4096 * t) ≤ 9 * Real.log (2 + r + t) := by
  let X := 2 + r + t
  have hX : 3 ≤ X := by dsimp [X]; linarith
  have hX0 : 0 ≤ X := by linarith
  have hpow : (4096 : ℝ) ≤ X ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hX 8
    norm_num at hh
    linarith
  have harg : 2 + 4096 * t ≤ X ^ 9 := by
    calc
      _ ≤ 4096 * X := by dsimp [X]; linarith
      _ ≤ X ^ 8 * X := mul_le_mul_of_nonneg_right hpow hX0
      _ = _ := by ring
  have hh := Real.log_le_log (show 0 < 2 + 4096 * t by positivity) harg
  simpa only [Real.log_pow, Nat.cast_ofNat, X] using hh

lemma normalized_call_budget {κ a b r t : ℝ} (hκ : 1 ≤ κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hr : 1 ≤ r) (ht : 0 ≤ t) (B N₀ N : ℕ)
    (hB : (B : ℝ) ≤ 65536 * (1 + a) + 1)
    (hN₀ : (N₀ : ℝ) ≤ 32 * κ * Real.log (2 + 4096 * t) + 1)
    (hN : (N : ℝ) ≤ 262144 * (1 + κ + a + b) * Real.log (2 + r) + 1) :
    ((2 * N + B * N₀ : ℕ) : ℝ) ≤
      10 ^ 9 * (κ * (1 + a) + b + 1) * Real.log (2 + r + t) := by
  let H := Real.log (2 + r + t)
  let F := κ * (1 + a) + b + 1
  have hH : 1 / 2 ≤ H := log_half_lower (by linarith)
  have hH0 : 0 ≤ H := by linarith
  have hF : 1 ≤ F := by dsimp [F]; nlinarith
  have hκH : 1 / 2 ≤ κ * H := by nlinarith
  have hFH : 1 / 2 ≤ F * H := by nlinarith
  have hB' : (B : ℝ) ≤ 65537 * (1 + a) := by linarith
  have hl := scaled_log_upper hr ht
  have hN₀' : (N₀ : ℝ) ≤ 290 * κ * H := by
    have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 32 * κ by positivity)
    change Real.log (2 + 4096 * t) ≤ 9 * H at hl
    nlinarith
  have hw := mul_le_mul hB' hN₀' (Nat.cast_nonneg N₀)
    (show 0 ≤ 65537 * (1 + a) by positivity)
  have hlog : Real.log (2 + r) ≤ H := Real.log_le_log (by linarith) (by linarith)
  have hcoeff : 1 + κ + a + b ≤ F := by dsimp [F]; nlinarith
  have hn' : (N : ℝ) ≤ 262146 * F * H := by
    have hh := mul_le_mul hcoeff hlog (Real.log_nonneg (by linarith)) (by linarith : 0 ≤ F)
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 262144)
    nlinarith
  have hpart : κ * (1 + a) ≤ F := by dsimp [F]; linarith
  have hpartH := mul_le_mul_of_nonneg_right hpart hH0
  push_cast
  nlinarith

lemma execution_budget_bound (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ) :
    2 * finalLength p + warmupBatch p * warmupLength p ≤
      ⌈10 ^ 9 * (Real.sqrt (p.L / p.μ) * (1 + p.M * p.D / p.μ ^ 2) +
        p.D / Real.sqrt (p.μ * p.ε) + 1) *
        Real.log (2 + p.Δ / p.ε + p.M ^ 2 * p.Δ / p.μ ^ 3)⌉₊ := by
  obtain ⟨hκ, _⟩ := condition_root_bounds p hp
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  let κ := Real.sqrt (p.L / p.μ)
  let a := p.M * p.D / p.μ ^ 2
  let b := p.D / Real.sqrt (p.μ * p.ε)
  let r := p.Δ / p.ε
  let t := p.M ^ 2 * p.Δ / p.μ ^ 3
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 1 ≤ r := (le_div_iff₀ hε).mpr (by linarith)
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hlr : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hlt : 0 ≤ Real.log (2 + 4096 * t) := Real.log_nonneg (by linarith)
  have hB : (warmupBatch p : ℝ) ≤ 65536 * (1 + a) + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 65536 * (1 + a) by positivity)).le
  have hN₀ : (warmupLength p : ℝ) ≤ 32 * κ * Real.log (2 + 4096 * t) + 1 := by
    unfold warmupLength
    split
    · simp only [Nat.cast_zero]
      positivity
    · have he : 16 / warmupMomentum p * Real.log (2 + 4096 * p.M ^ 2 * p.Δ / p.μ ^ 3) =
          32 * κ * Real.log (2 + 4096 * t) := by
        dsimp [warmupMomentum, κ, t]
        congr 1
        · ring_nf; simp only [inv_inv]
        · congr 1; ring
      rw [he]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 32 * κ * Real.log (2 + 4096 * t))).le
  have hN : (finalLength p : ℝ) ≤ 262144 * (1 + κ + a + b) * Real.log (2 + r) + 1 := by
    have he : 64 / finalMomentum p * Real.log (2 + p.Δ / p.ε) =
        262144 * (1 + κ + a + b) * Real.log (2 + r) := by
      dsimp [finalMomentum, κ, a, b, r]
      ring_nf; simp only [inv_inv]; ring
    unfold finalLength
    rw [he]
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 262144 * (1 + κ + a + b) * Real.log (2 + r))).le
  have hh := normalized_call_budget hκ ha hb hr ht (warmupBatch p) (warmupLength p)
    (finalLength p) hB hN₀ hN
  exact_mod_cast hh.trans (Nat.le_ceil _)

end OracleTemplate.NonlinearTemporalDiscrepancy
