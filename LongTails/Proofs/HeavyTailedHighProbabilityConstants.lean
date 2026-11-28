import LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
import LongTails.Proofs.HighProbabilityConstants

namespace LongTails.Proofs.HeavyTailedHighProbabilityConstants

open LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
open LongTails.Setups.HeavyTailedHighProbabilityStationarity

variable {q : Params} (hv : spec.valid q)
include hv

lemma tailFactor_nonneg : 0 ≤ tailFactor q := by
  unfold tailFactor
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg hv.2.2.2.1 hv.2.2.2.2.2.1.le) _)

lemma effective_nonneg : 0 ≤ effectiveSigma q := by
  unfold effectiveSigma
  exact mul_nonneg hv.2.2.2.2.2.1.le (le_trans (Real.sqrt_nonneg _) (le_max_left _ _))

lemma varianceParams_valid :
    LongTails.Setups.HighProbabilityStationarity.spec.valid (varianceParams q) := by
  obtain ⟨hL, hp, hp2, hσ, hΔ, hε, hδ, hδ1⟩ := hv
  exact ⟨hL, effective_nonneg ⟨hL, hp, hp2, hσ, hΔ, hε, hδ, hδ1⟩, hΔ, hε, hδ, hδ1⟩

lemma ratio_ge_sqrt : Real.sqrt (tailFactor q) ≤ effectiveSigma q / q.ε := by
  unfold effectiveSigma
  rw [mul_div_cancel_left₀ _ hv.2.2.2.2.2.1.ne']
  exact le_max_left _ _

lemma ratio_ge_rpow : tailFactor q ^ (1 / (2 * (q.p - 1))) ≤ effectiveSigma q / q.ε := by
  unfold effectiveSigma
  rw [mul_div_cancel_left₀ _ hv.2.2.2.2.2.1.ne']
  exact le_max_right _ _

lemma sigma_rpow_eq : q.σ ^ q.p = tailFactor q * q.ε ^ q.p / 2 ^ 45 := by
  unfold tailFactor
  rw [Real.div_rpow hv.2.2.2.1 hv.2.2.2.2.2.1.le]
  have : 0 < q.ε ^ q.p := Real.rpow_pos_of_pos hv.2.2.2.2.2.1 _
  field_simp

lemma link_bound :
    2 * q.σ ^ q.p * radius (varianceParams q) ^ (2 - q.p) ≤ effectiveSigma q ^ 2 := by
  have hA := tailFactor_nonneg hv
  have hε := hv.2.2.2.2.2.1
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  set x := effectiveSigma q / q.ε with hx
  have hx0 : 0 ≤ x := div_nonneg (effective_nonneg hv) hε.le
  have hsig : effectiveSigma q = q.ε * x := by rw [hx]; field_simp
  have hrad : radius (varianceParams q) = q.ε * (2 ^ 20 * (x + 1) ^ 2) := by
    change 2 ^ 20 * (effectiveSigma q + q.ε) ^ 2 / q.ε = _
    rw [hsig]
    field_simp
  set m := max x 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hxm : x ≤ m := le_max_left _ _
  have hK0 : 0 ≤ 2 ^ 20 * (x + 1) ^ 2 := by positivity
  have hK : 2 ^ 20 * (x + 1) ^ 2 ≤ 2 ^ 22 * m ^ 2 := by
    have : x + 1 ≤ 2 * m := by linarith
    nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ x + 1) this 2]
  have h2p : 0 ≤ 2 - q.p := by linarith
  have hKp : (2 ^ 20 * (x + 1) ^ 2) ^ (2 - q.p) ≤ 2 ^ 22 * m ^ (2 * (2 - q.p)) := by
    calc (2 ^ 20 * (x + 1) ^ 2) ^ (2 - q.p) ≤ (2 ^ 22 * m ^ 2) ^ (2 - q.p) :=
          Real.rpow_le_rpow hK0 hK h2p
      _ = (2 : ℝ) ^ (22 * (2 - q.p)) * m ^ (2 * (2 - q.p)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          congr 1
          · rw [show ((2 : ℝ) ^ 22) = (2 : ℝ) ^ (22 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          · rw [show ((m : ℝ) ^ 2) = m ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by linarith)]
      _ ≤ 2 ^ 22 * m ^ (2 * (2 - q.p)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _)
          calc (2 : ℝ) ^ (22 * (2 - q.p)) ≤ (2 : ℝ) ^ (22 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
            _ = 2 ^ 22 := by norm_num
  have hεp : q.ε ^ q.p * q.ε ^ (2 - q.p) = q.ε ^ 2 := by
    rw [← Real.rpow_add hε, show q.p + (2 - q.p) = 2 by ring]
    norm_num
  have hlhs : 2 * q.σ ^ q.p * radius (varianceParams q) ^ (2 - q.p) =
      q.ε ^ 2 * (2 * tailFactor q / 2 ^ 45 * (2 ^ 20 * (x + 1) ^ 2) ^ (2 - q.p)) := by
    rw [sigma_rpow_eq hv, hrad, Real.mul_rpow hε.le hK0, ← hεp]
    ring
  have hrhs : effectiveSigma q ^ 2 = q.ε ^ 2 * x ^ 2 := by rw [hsig]; ring
  rw [hlhs, hrhs]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hstep : 2 * tailFactor q / 2 ^ 45 * (2 ^ 20 * (x + 1) ^ 2) ^ (2 - q.p) ≤
      tailFactor q * m ^ (2 * (2 - q.p)) := by
    calc 2 * tailFactor q / 2 ^ 45 * (2 ^ 20 * (x + 1) ^ 2) ^ (2 - q.p) ≤
          2 * tailFactor q / 2 ^ 45 * (2 ^ 22 * m ^ (2 * (2 - q.p))) :=
        mul_le_mul_of_nonneg_left hKp (by positivity)
      _ = tailFactor q * m ^ (2 * (2 - q.p)) / 2 ^ 22 := by ring
      _ ≤ tailFactor q * m ^ (2 * (2 - q.p)) := by
          have : 0 ≤ tailFactor q * m ^ (2 * (2 - q.p)) :=
            mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
          linarith
  refine hstep.trans ?_
  rcases le_or_gt x 1 with hle | hgt
  · have hm' : m = 1 := max_eq_right hle
    rw [hm', Real.one_rpow, mul_one]
    have h := ratio_ge_sqrt hv
    rw [← hx] at h
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hA] at this
  · have hm' : m = x := max_eq_left hgt.le
    rw [hm']
    have h := ratio_ge_rpow hv
    rw [← hx] at h
    have hp1 : 0 < 2 * (q.p - 1) := by linarith
    have hAx : tailFactor q ≤ x ^ (2 * (q.p - 1)) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hp1.le
      rwa [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ hp1.ne', Real.rpow_one] at this
    have hxx : x ^ (2 * (q.p - 1)) * x ^ (2 * (2 - q.p)) = x ^ 2 := by
      rw [← Real.rpow_add (by linarith), show 2 * (q.p - 1) + 2 * (2 - q.p) = 2 by ring]
      norm_num
    rw [← hxx]
    exact mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hx0 _)

lemma sigma_small : q.σ ≤ noiseScale (varianceParams q) / 2 ^ 22 := by
  have hA := tailFactor_nonneg hv
  have hε := hv.2.2.2.2.2.1
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  have hσ := hv.2.2.2.1
  have hS : noiseScale (varianceParams q) = effectiveSigma q + q.ε := rfl
  have heff := effective_nonneg hv
  rcases le_or_gt (q.σ / q.ε) (1 / 2 ^ 22) with hle | hgt
  · rw [hS, le_div_iff₀ (by norm_num)]
    rw [div_le_div_iff₀ hε (by norm_num)] at hle
    linarith
  · have hy0 : 0 ≤ q.σ / q.ε := div_nonneg hσ hε.le
    have hA1 : 1 ≤ tailFactor q := by
      unfold tailFactor
      have h1 : (1 / 2 ^ 22 : ℝ) ^ q.p ≤ (q.σ / q.ε) ^ q.p :=
        Real.rpow_le_rpow (by norm_num) hgt.le (by linarith)
      have h2 : (1 / 2 ^ 22 : ℝ) ^ q.p ≥ (1 / 2 ^ 22 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hp2
      have h3 : (1 / 2 ^ 22 : ℝ) ^ (2 : ℝ) = 1 / 2 ^ 44 := by norm_num
      nlinarith
    have hexp : 1 / q.p ≤ 1 / (2 * (q.p - 1)) := by
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    have hAp : tailFactor q ^ (1 / q.p) ≤ effectiveSigma q / q.ε :=
      (Real.rpow_le_rpow_of_exponent_le hA1 hexp).trans (ratio_ge_rpow hv)
    have hAeq : tailFactor q ^ (1 / q.p) = 2 ^ (45 / q.p) * (q.σ / q.ε) := by
      unfold tailFactor
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hy0 _), ← Real.rpow_mul hy0,
        mul_one_div_cancel (by linarith), Real.rpow_one]
      congr 1
      rw [show ((2 : ℝ) ^ 45) = (2 : ℝ) ^ (45 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      ring_nf
    have h22 : (2 : ℝ) ^ 22 ≤ 2 ^ (45 / q.p) := by
      calc (2 : ℝ) ^ 22 = (2 : ℝ) ^ (22 : ℝ) := by norm_num
        _ ≤ 2 ^ (45 / q.p) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            rw [le_div_iff₀ (by linarith)]; nlinarith)
    have hy : 2 ^ 22 * (q.σ / q.ε) ≤ effectiveSigma q / q.ε := by
      rw [hAeq] at hAp
      exact le_trans (mul_le_mul_of_nonneg_right h22 hy0) hAp
    have hy' : 2 ^ 22 * q.σ ≤ effectiveSigma q := by
      have := mul_le_mul_of_nonneg_right hy hε.le
      rwa [mul_assoc, div_mul_cancel₀ _ hε.ne', div_mul_cancel₀ _ hε.ne'] at this
    rw [hS, le_div_iff₀ (by norm_num)]
    linarith

lemma effective_sq_le :
    effectiveSigma q ^ 2 / q.ε ^ 2 ≤ 1 + (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1)) := by
  have hA := tailFactor_nonneg hv
  have hε := hv.2.2.2.2.2.1
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  have hσ := hv.2.2.2.1
  have hp1 : 0 < q.p - 1 := by linarith
  have hsq : effectiveSigma q ^ 2 / q.ε ^ 2 =
      max (tailFactor q) (tailFactor q ^ (1 / (q.p - 1))) := by
    unfold effectiveSigma
    rw [mul_pow, mul_div_cancel_left₀ _ (by positivity)]
    have hmax : max (Real.sqrt (tailFactor q)) (tailFactor q ^ (1 / (2 * (q.p - 1)))) ^ 2 =
        max (Real.sqrt (tailFactor q) ^ 2) ((tailFactor q ^ (1 / (2 * (q.p - 1)))) ^ 2) := by
      rcases le_total (Real.sqrt (tailFactor q)) (tailFactor q ^ (1 / (2 * (q.p - 1)))) with h | h
      · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2)]
      · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (Real.rpow_nonneg hA _) h 2)]
    rw [hmax, Real.sq_sqrt hA]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    congr 1
    push_cast
    field_simp
  rw [hsq]
  have hbig : tailFactor q ^ (1 / (q.p - 1)) ≤ (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1)) := by
    have hy0 : 0 ≤ q.σ / q.ε := div_nonneg hσ hε.le
    have he : (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1)) =
        ((2 ^ 45 * q.σ / q.ε) ^ q.p) ^ (1 / (q.p - 1)) := by
      rw [← Real.rpow_mul (div_nonneg (mul_nonneg (by norm_num) hσ) hε.le)]
      congr 1
      field_simp
    rw [he]
    refine Real.rpow_le_rpow hA ?_ (div_nonneg zero_le_one hp1.le)
    unfold tailFactor
    rw [show 2 ^ 45 * q.σ / q.ε = 2 ^ 45 * (q.σ / q.ε) by ring,
      Real.mul_rpow (by norm_num) hy0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy0 _)
    calc (2 : ℝ) ^ 45 = (2 : ℝ) ^ (45 : ℝ) := by norm_num
      _ ≤ (2 ^ 45) ^ q.p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; nlinarith)
  have hB0 : 0 ≤ (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1)) :=
    Real.rpow_nonneg (by positivity) _
  rcases le_total (tailFactor q) 1 with h1 | h1
  · exact max_le (by linarith) (by linarith)
  · have hle : tailFactor q ≤ tailFactor q ^ (1 / (q.p - 1)) := by
      have := Real.rpow_le_rpow_of_exponent_le h1 (show (1 : ℝ) ≤ 1 / (q.p - 1) by
        rw [le_div_iff₀ hp1]; linarith)
      simpa using this
    exact max_le (by linarith) (by linarith)

end LongTails.Proofs.HeavyTailedHighProbabilityConstants
