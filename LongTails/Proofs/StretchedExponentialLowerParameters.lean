import LongTails.Proofs.CountdownCalibration
import LongTails.Setups.StretchedExponentialMarkovConvex

namespace OracleTemplate.StretchedExponentialLowerBound

open LongTails.Setups.StretchedExponentialMarkovConvex

noncomputable def mass (p : Params) : ℝ :=
  (8 * p.ε / (p.σ * p.R)) ^ (p.α / (p.α - 1))

noncomputable def lengthScale (p : Params) : ℝ :=
  p.τ * (Real.log (1 / mass p) / 2) ^ (1 / p.γ)

noncomputable def length (p : Params) : ℕ := ⌊lengthScale p⌋₊

lemma mass_bounds (p : Params) (hp : spec.valid p) : 0 < mass p ∧ mass p ≤ 1 / 16 := by
  rcases hp with ⟨_, _, hR, hσ, hα, hα2, _, _, _, hε, _, hsmall, _⟩
  have ht : 0 < 8 * p.ε / (p.σ * p.R) := by positivity
  have ht4 : 8 * p.ε / (p.σ * p.R) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < p.σ * p.R)).mpr
    linarith
  have hk : 2 ≤ p.α / (p.α - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < p.α - 1)).mpr
    linarith
  constructor
  · exact Real.rpow_pos_of_pos ht _
  · have hr := Real.rpow_le_rpow_of_exponent_ge ht (by linarith : 8 * p.ε / (p.σ * p.R) ≤ 1) hk
    rw [Real.rpow_two] at hr
    change (8 * p.ε / (p.σ * p.R)) ^ (p.α / (p.α - 1)) ≤ 1 / 16
    nlinarith

lemma lengthScale_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ lengthScale p := by
  obtain ⟨hq, hq1⟩ := mass_bounds p hp
  have hlog := CountdownMarkov.log_inverse_half_ge_one hq hq1
  rcases hp with ⟨_, _, _, _, _, _, hτ, hγ, _⟩
  have hr : 1 ≤ (Real.log (1 / mass p) / 2) ^ (1 / p.γ) :=
    Real.one_le_rpow hlog (by positivity)
  unfold lengthScale
  nlinarith

lemma length_pos (p : Params) (hp : spec.valid p) : 0 < length p :=
  Nat.floor_pos.mpr (lengthScale_ge_one p hp)

lemma mass_noise_bound (p : Params) (hp : spec.valid p) :
    2 * mass p ^ (1 - p.α) * (4 * p.ε / p.R) ^ p.α ≤ p.σ ^ p.α := by
  rcases hp with ⟨_, _, hR, hσ, hα, _, _, _, _, hε, _⟩
  have ht : 0 < 8 * p.ε / (p.σ * p.R) := by positivity
  have hα0 : 0 < p.α - 1 := by linarith
  have he : mass p ^ (1 - p.α) = (8 * p.ε / (p.σ * p.R)) ^ (-p.α) := by
    rw [mass, ← Real.rpow_mul ht.le]
    congr 1
    field_simp
    ring
  have hr : mass p ^ (1 - p.α) * (4 * p.ε / p.R) ^ p.α = (p.σ / 2) ^ p.α := by
    rw [he, Real.rpow_neg ht.le, ← div_eq_inv_mul, ← Real.div_rpow (by positivity) ht.le]
    congr 1
    field_simp
    ring
  rw [mul_assoc, hr, Real.div_rpow hσ.le (by norm_num)]
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ p.α := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα.le
    simpa only [Real.rpow_one] using h
  have hpos : 0 < (2 : ℝ) ^ p.α := Real.rpow_pos_of_pos (by norm_num) _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hσ.le p.α)]

lemma inverse_mass (p : Params) (hp : spec.valid p) :
    (mass p)⁻¹ = (p.σ * p.R / (8 * p.ε)) ^ (p.α / (p.α - 1)) := by
  have hR : 0 < p.R := hp.2.2.1
  have hσ : 0 < p.σ := hp.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.1
  rw [mass, ← Real.inv_rpow (by positivity)]
  congr 1
  field_simp

lemma lower_budget_identity (p : Params) (hp : spec.valid p) :
    p.τ / 32 * (p.σ * p.R / (8 * p.ε)) ^ (p.α / (p.α - 1)) *
      (p.α * Real.log (p.σ * p.R / (8 * p.ε)) / (2 * (p.α - 1))) ^ (1 / p.γ) =
      lengthScale p / (32 * mass p) := by
  have hR : 0 < p.R := hp.2.2.1
  have hσ : 0 < p.σ := hp.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.1
  have hq : 0 < mass p := (mass_bounds p hp).1
  have hz : 0 < p.σ * p.R / (8 * p.ε) := by positivity
  have hl : Real.log (1 / mass p) / 2 =
      p.α * Real.log (p.σ * p.R / (8 * p.ε)) / (2 * (p.α - 1)) := by
    rw [one_div, inverse_mass p hp, Real.log_rpow hz]
    field_simp
  rw [lengthScale, hl]
  have he (x : ℝ) : x / (32 * mass p) = (x / 32) * (mass p)⁻¹ := by ring
  rw [he, inverse_mass p hp]
  ring

end OracleTemplate.StretchedExponentialLowerBound
