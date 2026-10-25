import LongTails.Proofs.AffineMomentParameters
import LongTails.Proofs.AdaptiveHistoryAlgebra

open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentParameters

namespace LongTails.Proofs.AffineMomentConfidence

lemma confidence_exp {t : Tuning} (ht : Valid t) :
    Real.exp (confidence t) = 16 + conjugate t + 1 / t.ε + 1 / t.δ := by
  have := conjugate_ge_two ht
  have := ht.accuracy_pos
  have := ht.confidence_pos
  exact Real.exp_log (by positivity)

lemma energy_tail {t : Tuning} (ht : Valid t) : Real.exp (-(2 * confidence t)) ≤ t.δ / 2 := by
  let U := Real.exp (confidence t)
  have he := confidence_exp ht
  have hq := conjugate_ge_two ht
  have he0 := one_div_pos.mpr ht.accuracy_pos
  have hd0 := one_div_pos.mpr ht.confidence_pos
  have hU : 2 ≤ U := by dsimp [U]; linarith
  have hd : 1 / t.δ ≤ U := by dsimp [U]; linarith
  have hp : 0 < U := Real.exp_pos _
  have hprod : 2 / t.δ ≤ U ^ 2 := by
    have hh := mul_le_mul hU hd hd0.le hp.le
    simpa only [div_eq_mul_inv, one_mul, pow_two] using hh
  rw [Real.exp_neg, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul, show (Real.exp (confidence t)) ^ 2 = U ^ 2 by rfl]
  rw [← one_div]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have hh := (div_le_iff₀ ht.confidence_pos).mp hprod
  nlinarith

lemma iterations_coarse {t : Tuning} (ht : Valid t) :
    (iterations t : ℝ) ≤ (2 : ℝ) ^ 49 * Real.exp (2 * confidence t) := by
  let X := (2 : ℝ) ^ 48 * confidence t / t.ε
  have hl := confidence_ge_one ht
  have hX : 1 ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ ht.accuracy_pos).mpr
    nlinarith [ht.accuracy_le]
  have hr : t.p / (3 * t.p - 2) ≤ 1 := by
    apply (div_le_one (by linarith [ht.exponent_gt])).mpr
    linarith [ht.exponent_gt]
  have hp := Real.rpow_le_rpow_of_exponent_le hX hr
  rw [Real.rpow_one] at hp
  have hc : (iterations t : ℝ) ≤ 2 * X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ X ^ (t.p / (3 * t.p - 2)) by positivity)
    change (iterations t : ℝ) < X ^ (t.p / (3 * t.p - 2)) + 1 at hh
    linarith
  have hu := confidence_exp ht
  have hq := conjugate_ge_two ht
  have he := one_div_pos.mpr ht.accuracy_pos
  have hd := one_div_pos.mpr ht.confidence_pos
  have heU : 1 / t.ε ≤ Real.exp (confidence t) := by linarith
  have hlU : confidence t ≤ Real.exp (confidence t) := (Real.add_one_le_exp _).trans' (by linarith)
  have hmul := mul_le_mul hlU heU he.le (Real.exp_pos _).le
  rw [← Real.exp_add, ← two_mul] at hmul
  dsimp [X] at hc
  have hscale := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 2 ^ 49)
  simp only [div_eq_mul_inv, one_mul] at hc hmul
  norm_num at hc ⊢
  nlinarith [hmul]

lemma pilot_tail {t : Tuning} (ht : Valid t) :
    (2 * iterations t : ℝ) * (1 / 2 : ℝ) ^ pilotGroups t ≤ t.δ / 2 := by
  have hl := confidence_ge_one ht
  have hq := conjugate_ge_two ht
  have hg : 2048 * confidence t ≤ (pilotGroups t : ℝ) := by
    have hc := Nat.le_ceil (1024 * conjugate t * confidence t)
    change 1024 * conjugate t * confidence t ≤ (pilotGroups t : ℝ) at hc
    nlinarith
  have hh : (1 / 2 : ℝ) ^ pilotGroups t ≤ Real.exp (-(1024 * confidence t)) :=
    (LongTails.Proofs.AdaptiveHistoryAlgebra.half_power_exponential _).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hK := iterations_coarse ht
  have hU : 2 ≤ Real.exp (confidence t) := by
    rw [confidence_exp ht]
    have := one_div_pos.mpr ht.accuracy_pos
    have := one_div_pos.mpr ht.confidence_pos
    linarith
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hU 50
  rw [← Real.exp_nat_mul] at hc
  norm_num only [Nat.cast_ofNat] at hc
  calc
    _ ≤ (2 * ((2 : ℝ) ^ 49 * Real.exp (2 * confidence t))) *
        Real.exp (-(1024 * confidence t)) := by gcongr
    _ = (2 : ℝ) ^ 50 * Real.exp (2 * confidence t) * Real.exp (-(1024 * confidence t)) := by ring
    _ ≤ Real.exp (50 * confidence t) * Real.exp (2 * confidence t) *
        Real.exp (-(1024 * confidence t)) := by
      gcongr
      norm_num at hc ⊢
      exact hc
    _ = Real.exp (-(972 * confidence t)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(2 * confidence t)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ t.δ / 2 := energy_tail ht

end LongTails.Proofs.AffineMomentConfidence
