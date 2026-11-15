import LongTails.Proofs.InterpolatedFiniteSumSearchRate

open OracleTemplate MeasureTheory Classical
open LongTails LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

namespace LongTails.Proofs.InterpolatedFiniteSumCombinedLower

open InterpolatedFiniteSumRateLower

set_option maxHeartbeats 1600000 in
lemma combined_failure (p : Params) (hp : spec.valid p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : (b : ℝ) ≤ ((p.n : ℝ) + Real.sqrt (p.n * (p.L0 * p.R ^ 2 / p.ε)) +
      Real.sqrt p.n * (p.L1 * p.R) + p.n * (p.L1 * p.R) ^ (2 / 3 : ℝ)) /
      (1000000000 * (1 + Real.log (2 + p.n + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε)) ^ 2)) :
    Failure p A b := by
  let H := p.L0 * p.R ^ 2 / p.ε
  let q := p.L1 * p.R
  let D := 1 + Real.log (2 + p.n + q + H)
  have hL0 := hp.1
  have hL1 := hp.2.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  have hn : (2 : ℝ) ≤ p.n := by exact_mod_cast hp.2.2.2.2.1
  have hH : 0 < H := by dsimp [H]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h4n : 4 * p.n ≤ H := by
    apply (le_div_iff₀ hε).mpr
    exact hp.2.2.2.2.2.2.1
  have hD : 1 ≤ D := InterpolatedFiniteSumRateParameters.log_scale p.n q H (Nat.cast_nonneg _) hq hH.le
  have hηX : Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) ≤ 2 * D := by
    have he : 8 * p.ε * p.L1 ^ 2 / p.L0 = 8 * q ^ 2 / H := by dsimp [q, H]; field_simp
    rw [he]
    have hh := InterpolatedFiniteSumRateParameters.logarithm_bound p.n q H 8 (Nat.cast_nonneg _) hq hH
      (by norm_num) (by linarith)
    dsimp [D]
    linarith only [hh]
  have hηQ : Real.log (1 + 8 * (p.n / 2 : ℕ) * p.ε * p.L1 ^ 2 / p.L0) ≤ 2 * D := by
    have hg : 2 * (p.n / 2) ≤ p.n := by omega
    have hgR : 2 * ((p.n / 2 : ℕ) : ℝ) ≤ p.n := by exact_mod_cast hg
    have he : 8 * (p.n / 2 : ℕ) * p.ε * p.L1 ^ 2 / p.L0 = 8 * (p.n / 2 : ℕ) * q ^ 2 / H := by
      dsimp [q, H]; field_simp
    rw [he]
    have hh := InterpolatedFiniteSumRateParameters.logarithm_bound p.n q H (8 * (p.n / 2 : ℕ))
      (Nat.cast_nonneg _) hq hH (by positivity) (by linarith)
    dsimp [D]
    linarith only [hh]
  have hb' : 1000000000 * D ^ 2 * b ≤
      p.n + Real.sqrt (p.n * H) + Real.sqrt p.n * q + p.n * q ^ (2 / 3 : ℝ) := by
    have hh := (le_div_iff₀ (show 0 < 1000000000 * D ^ 2 by positivity)).mp hb
    nlinarith only [hh]
  have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD]
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hDb := mul_le_mul_of_nonneg_right hD2 hb0
  have hmax : 4000000 * D ^ 2 * b ≤
      (p.n + Real.sqrt (p.n * H) + Real.sqrt p.n * q + p.n * q ^ (2 / 3 : ℝ)) / 4 := by
    have hh : 0 ≤ D ^ 2 * (b : ℝ) := by positivity
    nlinarith only [hb', hh]
  rcases InterpolatedFiniteSumRateParameters.four_terms _ _ _ _ _ hmax with hc | hs | hx | hsearch
  · apply component_failure p hp A b
    nlinarith only [hc, hDb, hb0]
  · apply smooth_rate_failure p hp A b
    change 1000 * (b : ℝ) ≤ Real.sqrt (p.n * H)
    nlinarith only [hs, hDb, hb0]
  · apply exponential_rate_failure p hp D hD hηX A b
    change 1000000 * D ^ 2 * b ≤ Real.sqrt p.n * q
    have hh : 0 ≤ D ^ 2 * (b : ℝ) := by positivity
    nlinarith only [hx, hh]
  · exact InterpolatedFiniteSumSearchRate.search_rate_failure p hp D hD hηX hηQ A b hsearch

lemma valid_example (L1 : ℝ) (hL1 : 0 ≤ L1) :
    spec.valid
    { d := ⌈(2 : ℝ) ^ 80 * (1 + (2 : ℝ) + L1 * 1 + 8 * 1 ^ 2 / 1) ^ 24⌉₊,
      n := 2, L0 := 8, L1 := L1, R := 1, Δ := 2, ε := 1 } := by
  norm_num [spec, hL1]

end LongTails.Proofs.InterpolatedFiniteSumCombinedLower
