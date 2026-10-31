import LongTails.Proofs.MonotoneHessianCost
import LongTails.Proofs.MonotoneHessianRates

namespace LongTails.Proofs.MonotoneHessianBudget

open LongTails.Setups.HessianLipschitzSecondOrder LongTails.Algorithms.MonotoneHessianReuse
open LongTails.Proofs.MonotoneHessianRates LongTails.Proofs.MonotoneHessianCost

lemma charge_ratio (p : Params) (hp : spec.valid p) :
    chargeFactor p / (delta p / (4 * p.H)) =
      2 ^ 42 * p.H / (p.ε * delta p) + 3 * p.H ^ 2 / delta p ^ 3 := by
  have hH := hp.1.ne'
  have hε := hp.2.2.1.ne'
  have hδ := (MonotoneHessianParameters.delta_pos p hp).ne'
  unfold chargeFactor
  field_simp
  ring

lemma charge_ratio_bound (p : Params) (hp : spec.valid p) :
    chargeFactor p / (delta p / (4 * p.H)) ≤ 2 ^ 43 * p.H / (p.ε * delta p) := by
  have hH := hp.1
  have hε := hp.2.2.1
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have hγδ := MonotoneHessianParameters.gamma_le_delta p hp
  have hs := MonotoneHessianParameters.gamma_sq p hp
  have hrat : p.H / delta p ^ 2 ≤ 1 / p.ε := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hδ) hε).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hrat (show 0 ≤ p.H / delta p by positivity)
  have hh' : p.H ^ 2 / delta p ^ 3 ≤ p.H / (p.ε * delta p) := by
    convert hh using 1 <;> field_simp
  rw [charge_ratio p hp]
  have hpos : 0 ≤ p.H / (p.ε * delta p) := by positivity
  simp only [mul_div_assoc]
  nlinarith

lemma normalized_ratio (p : Params) (hp : spec.valid p) :
    p.H * p.Δ / (p.ε * delta p) = size p / scale p ^ 2 := by
  have hH : 0 < Real.sqrt p.H := Real.sqrt_pos.mpr hp.1
  have hε : 0 < Real.sqrt p.ε := Real.sqrt_pos.mpr hp.2.2.1
  have ht := MonotoneHessianParameters.scale_pos p
  have hγ : gamma p = Real.sqrt p.H * Real.sqrt p.ε := Real.sqrt_mul hp.1.le _
  have he : (Real.sqrt p.H) ^ 2 * p.Δ /
      ((Real.sqrt p.ε) ^ 2 * (scale p ^ 2 * (Real.sqrt p.H * Real.sqrt p.ε))) =
      (p.Δ * Real.sqrt p.H / ((Real.sqrt p.ε) ^ 2 * Real.sqrt p.ε)) / scale p ^ 2 := by
    field_simp
  simpa only [Real.sq_sqrt hp.1.le, Real.sq_sqrt hp.2.2.1.le, ← hγ, delta, size] using he

lemma hessian_envelope (p : Params) (hp : spec.valid p) :
    1 + chargeFactor p * p.Δ / (delta p / (4 * p.H)) ≤
      2 ^ 44 * (1 + size p / p.m ^ (2 / 3 : ℝ)) := by
  have hs := size_nonneg p hp
  have hr := rootCost_pos p hp
  have ht := MonotoneHessianParameters.scale_pos p
  have hscale := (scale_bounds p hp).1
  have hh := mul_le_mul_of_nonneg_right (charge_ratio_bound p hp) hp.2.1
  have he : (2 : ℝ) ^ 43 * p.H / (p.ε * delta p) * p.Δ =
      2 ^ 43 * (p.H * p.Δ / (p.ε * delta p)) := by ring
  rw [he, normalized_ratio p hp] at hh
  have hb := div_le_div_of_nonneg_left hs (sq_pos_of_pos hr) (pow_le_pow_left₀ hr.le hscale 2)
  have hrpow : rootCost p ^ 2 = p.m ^ (2 / 3 : ℝ) := by
    rw [rootCost, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hp.2.2.2.1)]
    norm_num
  rw [hrpow] at hb
  have hpos : 0 ≤ size p / p.m ^ (2 / 3 : ℝ) := by
    rw [← hrpow]
    exact div_nonneg hs (sq_nonneg _)
  have hid : chargeFactor p * p.Δ / (delta p / (4 * p.H)) =
      chargeFactor p / (delta p / (4 * p.H)) * p.Δ := by ring
  rw [hid]
  nlinarith

end LongTails.Proofs.MonotoneHessianBudget
