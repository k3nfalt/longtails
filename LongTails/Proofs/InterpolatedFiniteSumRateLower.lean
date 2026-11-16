import LongTails.Proofs.InterpolatedFiniteSumSmoothLower
import LongTails.Proofs.InterpolatedFiniteSumExponentialLower
import LongTails.Proofs.InterpolatedFiniteSumLinkTuning
import LongTails.Proofs.InterpolatedFiniteSumRateParameters

open OracleTemplate MeasureTheory Classical
open LongTails LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

namespace LongTails.Proofs.InterpolatedFiniteSumRateLower

abbrev Failure (p : Params) (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ) : Prop :=
  ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
    spec.admissible p f O ∧ ¬ spec.successful p f
      (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩

lemma dimension_pos (p : Params) (hp : spec.valid p) : 0 < p.d := by
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hH : 0 ≤ p.L0 * p.R ^ 2 / p.ε := div_nonneg (mul_nonneg hp.1.le (sq_nonneg _)) hp.2.2.2.1.le
  have hbase : 0 < 1 + (p.n : ℝ) + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε := by positivity
  have hc : 0 < ⌈(2 : ℝ) ^ 80 * (1 + p.n + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε) ^ 24⌉₊ :=
    Nat.ceil_pos.mpr (by positivity)
  exact hc.trans_le hp.2.2.2.2.2.2.2

lemma component_failure (p : Params) (hp : spec.valid p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 4 * (b : ℝ) ≤ p.n) : Failure p A b := by
  apply InterpolatedFiniteSumHiddenComponent.exists_failure p hp (dimension_pos p hp) A b
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
  have hh : 4 * b ≤ p.n := by exact_mod_cast hb
  omega

lemma smooth_rate_failure (p : Params) (hp : spec.valid p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 1000 * (b : ℝ) ≤ Real.sqrt ((p.n : ℝ) * (p.L0 * p.R ^ 2 / p.ε))) : Failure p A b := by
  let H := p.L0 * p.R ^ 2 / p.ε
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hH : 0 ≤ H := by dsimp [H]; exact div_nonneg (mul_nonneg hp.1.le (sq_nonneg _)) hp.2.2.2.1.le
  change 1000 * (b : ℝ) ≤ Real.sqrt ((p.n : ℝ) * H) at hb
  by_cases hr : 144 * p.n ≤ H
  · have hlen := InterpolatedFiniteSumSmoothParameters.length_bounds p.n hn H hr
    apply InterpolatedFiniteSumSmoothLower.smooth_failure p hp hr A b
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr
    have hid : Real.sqrt ((p.n : ℝ) * H) = p.n * Real.sqrt (H / p.n) := by
      rw [Real.sqrt_div hH, Real.sqrt_mul hnR.le]
      have hs := Real.sq_sqrt hnR.le
      have hsp : 0 < Real.sqrt (p.n : ℝ) := Real.sqrt_pos.mpr hnR
      field_simp
      rw [hs]
      ring
    rw [hid] at hb
    have hm := mul_le_mul_of_nonneg_left hlen.2.2 hnR.le
    have hh : (b : ℝ) * 8 ≤ p.n * ⌊Real.sqrt (H / p.n) / 12⌋₊ := by
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      nlinarith only [hb, hm, hb0]
    exact_mod_cast hh
  · apply component_failure p hp A b
    have hs := Real.sq_sqrt (mul_nonneg hnR.le hH)
    have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hr) hnR
    have hroot : Real.sqrt ((p.n : ℝ) * H) ≤ 12 * p.n := by
      have hsr := Real.sqrt_nonneg ((p.n : ℝ) * H)
      nlinarith only [hs, hmul, hsr, hnR]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith only [hb, hroot, hb0]

set_option maxHeartbeats 1200000 in
lemma exponential_rate_failure (p : Params) (hp : spec.valid p) (D : ℝ) (hD : 1 ≤ D)
    (hηD : Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) ≤ 2 * D)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 1000000 * D ^ 2 * b ≤ Real.sqrt p.n * (p.L1 * p.R)) : Failure p A b := by
  let η := Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0)
  let g := p.n / 2
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hg : 0 < g := by dsimp [g]; have := hp.2.2.2.2.1; omega
  have hng : p.n ≤ 3 * g := by dsimp [g]; omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hL0 := hp.1
  have hL := hp.2.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD]
  have hDb := mul_le_mul_of_nonneg_right hD2 hb0
  by_cases hr : p.L0 < p.ε * p.L1 ^ 2
  · have hLpos : 0 < p.L1 := by
      by_contra hnL
      have he : p.L1 = 0 := le_antisymm (le_of_not_gt hnL) hL
      rw [he] at hr
      norm_num at hr
      linarith
    have hη : 0 < η := by
      apply Real.log_pos
      have hh : 0 < 8 * p.ε * p.L1 ^ 2 / p.L0 := by positivity
      linarith
    by_cases ha : 84 * η * Real.sqrt g ≤ p.L1 * p.R
    · exact InterpolatedFiniteSumExponentialLower.exponential_failure p hp hr ha A b
        (InterpolatedFiniteSumRateParameters.exponential_budget p.n g b hg hng (p.L1 * p.R) η D
          (by positivity) hη hD hηD ha hb)
    · apply component_failure p hp A b
      have hgn : (g : ℝ) ≤ p.n := by exact_mod_cast (show g ≤ p.n by dsimp [g]; omega)
      have hsg := Real.sqrt_le_sqrt hgn
      have hsn := Real.sqrt_nonneg (p.n : ℝ)
      have hsn2 := Real.sq_sqrt hnR.le
      have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge ha) (Real.sqrt_pos.mpr hnR)
      have hmul2 := mul_le_mul_of_nonneg_left hsg (show 0 ≤ 84 * η * Real.sqrt p.n by positivity)
      have he : 84 * η * Real.sqrt p.n * Real.sqrt p.n = 84 * η * p.n := by
        calc _ = 84 * η * (Real.sqrt p.n) ^ 2 := by ring
             _ = _ := by rw [hsn2]
      rw [he] at hmul2
      have hηmul := mul_le_mul_of_nonneg_right hηD hnR.le
      change η * p.n ≤ 2 * D * p.n at hηmul
      have hDb2 : D ≤ D ^ 2 := by nlinarith only [hD]
      have hh : 1000000 * D ^ 2 * b ≤ 168 * D * p.n := by
        nlinarith only [hb, hmul, hmul2, hsn2, hηmul]
      have hcancel : 1000000 * D * b ≤ 168 * p.n := by
        apply (mul_le_mul_iff_right₀ (show 0 < D by linarith)).mp
        nlinarith only [hh]
      have hDb1 := mul_le_mul_of_nonneg_right hD hb0
      nlinarith only [hcancel, hDb1]
  · apply smooth_rate_failure p hp A b
    have hreg : p.ε * p.L1 ^ 2 ≤ p.L0 := le_of_not_gt hr
    have hm := mul_le_mul_of_nonneg_right hreg (sq_nonneg p.R)
    have hqH : (p.L1 * p.R) ^ 2 ≤ p.L0 * p.R ^ 2 / p.ε := by
      apply (le_div_iff₀ hε).mpr
      nlinarith only [hm]
    have hq := mul_nonneg hL hR.le
    have hH : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by positivity
    have hsn := Real.sq_sqrt hnR.le
    have hsH := Real.sq_sqrt (mul_nonneg hnR.le hH)
    have hsqmul := mul_le_mul_of_nonneg_left hqH hnR.le
    have hroot : Real.sqrt p.n * (p.L1 * p.R) ≤ Real.sqrt ((p.n : ℝ) * (p.L0 * p.R ^ 2 / p.ε)) := by
      have hn0 := Real.sqrt_nonneg (p.n : ℝ)
      have hH0 := Real.sqrt_nonneg ((p.n : ℝ) * (p.L0 * p.R ^ 2 / p.ε))
      have hid : (Real.sqrt p.n * (p.L1 * p.R)) ^ 2 = p.n * (p.L1 * p.R) ^ 2 := by rw [mul_pow, hsn]
      nlinarith only [hid, hsH, hsqmul, mul_nonneg hn0 hq, hH0]
    nlinarith only [hb, hroot, hDb, hb0]

end LongTails.Proofs.InterpolatedFiniteSumRateLower
