import LongTails.Proofs.StochasticQuasarOuterTuning
import LongTails.Proofs.GradientOnlyQuasarTuning
import LongTails.Proofs.StochasticQuasarWorkTail
import LongTails.Proofs.StochasticQuasarHolding

open MeasureTheory

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma confidence_log_nonneg {q : Params} (hv : spec.valid q) : 0 ≤ Real.log (8 / q.δ) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hv.2.2.2.2.2.2.1).mpr
  have hd := hv.2.2.2.2.2.2.2
  linarith

lemma outer_order_log_lower (q : Params) : 8 * Real.log (8 / q.δ) ≤ (outerOrder q : ℝ) := by
  have hh := Nat.le_ceil (8 * Real.log (8 / q.δ))
  unfold outerOrder
  push_cast
  linarith

lemma outer_order_quarter_tail {q : Params} (hv : spec.valid q) :
    Real.exp (-(outerOrder q : ℝ) / 4) ≤ q.δ / 8 := by
  have hd := hv.2.2.2.2.2.2.1
  have hp := outer_order_log_lower q
  have hl := confidence_log_nonneg hv
  have he : Real.exp (-Real.log (8 / q.δ)) = q.δ / 8 := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 8 / q.δ)]
    field_simp
  rw [← he]
  apply Real.exp_le_exp.mpr
  linarith

lemma outer_order_exponential_tail {q : Params} (hv : spec.valid q) :
    Real.exp (-(outerOrder q : ℝ)) ≤ q.δ / 8 := by
  apply (Real.exp_le_exp.mpr ?_).trans (outer_order_quarter_tail hv)
  have hp := outer_order_pos q
  linarith

lemma cleanup_replica_tail {q : Params} (hv : spec.valid q) :
    (1 / 2 : ℝ) ^ (outerOrder q + 1) ≤ q.δ / 8 := by
  apply (GradientOnlyQuasar.half_pow_le_exp _).trans
  apply (Real.exp_le_exp.mpr ?_).trans (outer_order_quarter_tail hv)
  push_cast
  have hp := outer_order_pos q
  linarith

lemma outer_horizon_large {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    32768 * (outerOrder q : ℝ) ≤ outerHorizon q := by
  have hε := hv.2.2.2.2.2.1
  have hγ := hv.2.2.1
  have hγ1 := hv.2.2.2.1
  have hp := outer_order_pos q
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hε).mpr
    nlinarith
  unfold outerHorizon
  apply (le_div_iff₀ hγ).mpr
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 65536 * (outerOrder q : ℝ))
  have hg := mul_le_mul_of_nonneg_left hγ1 (by positivity : 0 ≤ 32768 * (outerOrder q : ℝ))
  nlinarith

lemma outer_count_lower (q : Params) :
    8 * outerHorizon q + 8 * (outerOrder q : ℝ) ≤ (outerCount q : ℝ) := Nat.le_ceil _

lemma outer_count_upper {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    (outerCount q : ℝ) ≤ 9 * outerHorizon q := by
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  have hp2 : (2 : ℝ) ≤ outerOrder q := by exact_mod_cast outer_order_two q
  have hlarge := outer_horizon_large hv he
  have hc := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 8 * outerHorizon q + 8 * (outerOrder q : ℝ))).le
  change (outerCount q : ℝ) ≤ 8 * outerHorizon q + 8 * (outerOrder q : ℝ) + 1 at hc
  linarith

lemma outer_compensation_bound {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    2 * ((outerOrder q : ℝ) / (1024 * outerHorizon q)) * (outerCount q : ℝ) ≤
      (outerOrder q : ℝ) / 8 := by
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  have hh := mul_le_mul_of_nonneg_left (outer_count_upper hv he)
    (by positivity : 0 ≤ 2 * ((outerOrder q : ℝ) / (1024 * outerHorizon q)))
  have heq : 2 * ((outerOrder q : ℝ) / (1024 * outerHorizon q)) * (9 * outerHorizon q) =
      9 * (outerOrder q : ℝ) / 512 := by field_simp; norm_num
  rw [heq] at hh
  linarith

lemma outer_clock_lower_bound {q : Params} (hv : spec.valid q) :
    (RelativeQuasar.samplesLaw (outerCount q) : Measure (Fin (outerCount q) → ℝ))
      {samples | GradientOnlyQuasar.clockSum samples < 2 * outerHorizon q} ≤ ENNReal.ofReal (q.δ / 8) := by
  apply (GradientOnlyQuasar.clock_lower_tail _ _).trans
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_of_nonneg_left (GradientOnlyQuasar.half_pow_le_exp _) (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  apply (Real.exp_le_exp.mpr ?_).trans (outer_order_exponential_tail hv)
  have hK := outer_count_lower q
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  linarith

lemma outer_clock_upper_bound {q : Params} (hv : spec.valid q) :
    (RelativeQuasar.samplesLaw (outerCount q) : Measure (Fin (outerCount q) → ℝ))
      {samples | 2 * (outerCount q : ℝ) < GradientOnlyQuasar.clockSum samples} ≤ ENNReal.ofReal (q.δ / 8) := by
  apply (clock_upper_tail _ _).trans
  apply ENNReal.ofReal_le_ofReal
  have he : (2 : ℝ) ^ outerCount q = Real.exp ((outerCount q : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [he, ← Real.exp_add]
  apply (Real.exp_le_exp.mpr ?_).trans (outer_order_exponential_tail hv)
  have hlog : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (outerCount q) : (0 : ℝ) ≤ outerCount q)
  have hK := outer_count_lower q
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  linarith

lemma outer_energy_tail_constant {q : Params} (hv : spec.valid q) :
    Real.exp ((outerOrder q : ℝ) / 8) * (2 * (9 / 16 : ℝ) ^ outerOrder q) ≤ q.δ / 4 := by
  have hx : Real.exp (1 / 8 : ℝ) ≤ 5 / 4 := by
    have hh := exp_unit_chord (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    linarith
  have hy : (3 / 4 : ℝ) ≤ Real.exp (-1 / 4 : ℝ) := by
    have hh := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  have hz : Real.exp (1 / 8 : ℝ) * (9 / 16) ≤ Real.exp (-1 / 4 : ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (1 / 8 : ℝ) * (9 / 16)) hz (outerOrder q)
  have he₁ : Real.exp ((outerOrder q : ℝ) / 8) = Real.exp (1 / 8 : ℝ) ^ outerOrder q := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he₂ : Real.exp (-1 / 4 : ℝ) ^ outerOrder q = Real.exp (-(outerOrder q : ℝ) / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, he₂] at hp
  rw [he₁]
  have hh := outer_order_quarter_tail hv
  nlinarith

end OracleTemplate.StochasticQuasar
