import LongTails.Proofs.InterpolatedFiniteSumRateLower

open OracleTemplate MeasureTheory Classical
open LongTails LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

namespace LongTails.Proofs.InterpolatedFiniteSumSearchRate

open InterpolatedFiniteSumRateLower

set_option maxHeartbeats 1600000 in
lemma search_rate_failure (p : Params) (hp : spec.valid p) (D : ℝ) (hD : 1 ≤ D)
    (hηX : Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) ≤ 2 * D)
    (hηQ : Real.log (1 + 8 * (p.n / 2 : ℕ) * p.ε * p.L1 ^ 2 / p.L0) ≤ 2 * D)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 4000000 * D ^ 2 * b ≤ p.n * (p.L1 * p.R) ^ (2 / 3 : ℝ)) : Failure p A b := by
  let q := p.L1 * p.R
  let t := (q / 64) ^ (2 / 3 : ℝ)
  let g := p.n / 2
  let η := Real.log (1 + 8 * (g : ℝ) * p.ε * p.L1 ^ 2 / p.L0)
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hg : 0 < g := by dsimp [g]; have := hp.2.2.2.2.1; omega
  have hng : (p.n : ℝ) ≤ 3 * g := by exact_mod_cast (show p.n ≤ 3 * g by dsimp [g]; omega)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hq : 0 ≤ q := mul_nonneg hp.2.1 hp.2.2.1.le
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hpower := InterpolatedFiniteSumLinkLength.scale_power q hq
  change q ^ (2 / 3 : ℝ) = 16 * t at hpower
  change 4000000 * D ^ 2 * b ≤ p.n * q ^ (2 / 3 : ℝ) at hb
  rw [hpower] at hb
  have hid := InterpolatedFiniteSumLinkLength.scale_identity q hq
  change q = 64 * t * Real.sqrt t at hid
  have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD]
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hDb := mul_le_mul_of_nonneg_right hD2 hb0
  by_cases hq64 : 64 ≤ q
  · have ht : 1 ≤ t := InterpolatedFiniteSumLinkLength.scale_ge_one q hq64
    have hL : 0 < p.L1 := by
      have hL0 := hp.2.1
      have hR := hp.2.2.1
      by_contra hh
      have he : p.L1 = 0 := le_antisymm (le_of_not_gt hh) hL0
      have heq : q = 0 := by dsimp [q]; rw [he]; ring
      linarith
    by_cases hgt : 4 * t ≤ g
    · by_cases heta : η ≤ t / 8
      · apply InterpolatedFiniteSumLinkTuning.link_failure p hp hL t ht hid hq64 hgt heta A b
        have hL0 := hp.1
        have hε := hp.2.2.2.1
        have hη : 0 ≤ η := by
          apply Real.log_nonneg
          have hh : 0 ≤ 8 * (g : ℝ) * p.ε * p.L1 ^ 2 / p.L0 := by positivity
          linarith
        have hηD : (1 + η) ^ 2 ≤ 9 * D ^ 2 := by
          have hh : 1 + η ≤ 3 * D := by linarith only [hηQ, hD]
          nlinarith only [hh, hη, hD]
        apply (le_div_iff₀ (show 0 < 4096 * (1 + η) ^ 2 by positivity)).mpr
        have hm := mul_le_mul_of_nonneg_right hηD hb0
        have hnmt := mul_le_mul_of_nonneg_right hng ht0
        nlinarith only [hb, hm, hnmt, hDb, hb0]
      · apply component_failure p hp A b
        have htη : t < 8 * η := by linarith
        have hm := mul_lt_mul_of_pos_left htη hnR
        have hηn := mul_le_mul_of_nonneg_right hηQ hnR.le
        have hh : 1000000 * D ^ 2 * b ≤ 256 * D * p.n := by nlinarith only [hb, hm, hηn]
        have hc : 1000000 * D * b ≤ 256 * p.n := by
          apply (mul_le_mul_iff_right₀ (show 0 < D by linarith)).mp
          nlinarith only [hh]
        have hDb1 := mul_le_mul_of_nonneg_right hD hb0
        nlinarith only [hc, hDb1]
    · apply exponential_rate_failure p hp D hD hηX A b
      have hnt : (p.n : ℝ) ≤ 12 * t := by linarith only [hng, lt_of_not_ge hgt]
      have hs : Real.sqrt p.n ≤ 4 * Real.sqrt t := by
        have h1 := Real.sq_sqrt hnR.le
        have h2 := Real.sq_sqrt ht0
        have h3 := Real.sqrt_nonneg (p.n : ℝ)
        have h4 := Real.sqrt_nonneg t
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 16 * t * Real.sqrt p.n by positivity)
      have hnid : 16 * t * Real.sqrt p.n * Real.sqrt p.n = 16 * t * p.n := by
        calc _ = 16 * t * (Real.sqrt p.n) ^ 2 := by ring
             _ = _ := by rw [Real.sq_sqrt hnR.le]
      rw [hnid] at hm
      change 1000000 * D ^ 2 * b ≤ Real.sqrt p.n * q
      rw [hid]
      nlinarith only [hb, hm]
  · apply component_failure p hp A b
    have ht : t ≤ 1 := by
      have hh : q / 64 ≤ 1 := by linarith only [lt_of_not_ge hq64]
      have hh' := Real.rpow_le_rpow (by positivity : 0 ≤ q / 64) hh (by norm_num : (0 : ℝ) ≤ 2 / 3)
      simpa only [Real.one_rpow] using hh'
    have hm := mul_le_mul_of_nonneg_left ht hnR.le
    nlinarith only [hb, hm, hDb, hb0]

end LongTails.Proofs.InterpolatedFiniteSumSearchRate
