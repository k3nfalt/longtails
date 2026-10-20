import LongTails.Proofs.SymmetricReverseFisherDynamics
namespace LongTails.Proofs.SymmetricReverseFisherRates
lemma log_one_add_lower {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : t / 2 ≤ Real.log (1 + t) := by
  have h := Real.le_log_one_add_of_nonneg ht
  have hd : 0 < t + 2 := by linarith
  have hl : t / 2 ≤ 2 * t / (t + 2) := (le_div_iff₀ hd).mpr (by nlinarith)
  exact hl.trans h
lemma reciprocal_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    (1 / (1 + t)) ^ k ≤ Real.exp (-(t / 2) * k) := by
  have hpos : 0 < 1 + t := by positivity
  have hb : 1 / (1 + t) ≤ Real.exp (-(t / 2)) := by
    calc
      _ = Real.exp (-Real.log (1 + t)) := by rw [Real.exp_neg, Real.exp_log hpos, one_div]
      _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg (log_one_add_lower ht ht1))
  calc
    _ ≤ (Real.exp (-(t / 2))) ^ k := pow_le_pow_left₀ (by positivity) hb k
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
lemma reciprocal_pow_small {t ζ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hζ : 0 < ζ)
    {k : ℕ} (hk : 2 / t * Real.log (1 / ζ) ≤ k) : (1 / (1 + t)) ^ k ≤ ζ := by
  have hlog : Real.log (1 / ζ) ≤ (t / 2) * k := by
    have hh := mul_le_mul_of_nonneg_left hk ht.le
    have he : t * (2 / t * Real.log (1 / ζ)) = 2 * Real.log (1 / ζ) := by field_simp
    rw [he] at hh
    linarith
  calc
    _ ≤ Real.exp (-(t / 2) * k) := reciprocal_pow_le_exp ht.le ht1 k
    _ ≤ Real.exp (-Real.log (1 / ζ)) := Real.exp_le_exp.mpr (by linarith)
    _ = ζ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; simp
lemma growth_pow_large {t ζ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hζ : 0 < ζ)
    {k : ℕ} (hk : 2 / t * Real.log (1 / ζ) ≤ k) : 1 ≤ (1 + t) ^ k * ζ := by
  have h := reciprocal_pow_small ht ht1 hζ hk
  rw [div_pow, one_pow] at h
  exact ((div_le_iff₀ (by positivity : 0 < (1+t)^k)).mp h).trans_eq (mul_comm _ _)
end LongTails.Proofs.SymmetricReverseFisherRates
