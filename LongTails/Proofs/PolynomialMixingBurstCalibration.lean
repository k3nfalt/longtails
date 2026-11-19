import LongTails.Proofs.PolynomialMixingBurstLaw
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingBurst

open LongTails.Setups.PolynomialMixingSubgradient

noncomputable def width (a β τ : ℝ) : ℕ :=
  max 1 ⌊τ * ((2 * a) ^ (-(1 / β)) - 1)⌋₊

lemma width_pos (a β τ : ℝ) : 0 < width a β τ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)

lemma width_lower {a β τ : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4)
    (hb : 0 < β) (ht : 0 ≤ τ) :
    τ * (2 * a) ^ (-(1 / β)) / (2 * (1 + 2 * β)) ≤ width a β τ := by
  let X := (2 * a) ^ (-(1 / β))
  have hlog : 1 / 2 ≤ -Real.log (2 * a) := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * a) (by linarith : 2 * a ≤ 2⁻¹)
    rw [Real.log_inv] at hh
    linarith [Real.log_two_gt_d9]
  have hlow : 1 / (2 * β) + 1 ≤ X := by
    dsimp [X]
    rw [Real.rpow_def_of_pos (by positivity)]
    apply le_trans _ (Real.add_one_le_exp _)
    have := div_le_div_of_nonneg_right hlog hb.le
    linarith [show 1 / (2 * β) = (1 / 2) / β by ring,
      show Real.log (2 * a) * -(1 / β) = -Real.log (2 * a) / β by ring]
  have hx : X ≤ (1 + 2 * β) * (X - 1) := by
    have he := (le_sub_iff_add_le.mpr hlow : 1 / (2 * β) ≤ X - 1)
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * β)).mp he
    nlinarith
  let m := width a β τ
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast width_pos a β τ
  have hm' : (⌊τ * (X - 1)⌋₊ : ℝ) ≤ m := by
    exact_mod_cast (le_max_right 1 ⌊τ * (X - 1)⌋₊)
  have hf := Nat.lt_floor_add_one (τ * (X - 1))
  have hi : τ * (X - 1) ≤ 2 * m := by linarith
  change τ * X / (2 * (1 + 2 * β)) ≤ m
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hx ht, mul_le_mul_of_nonneg_left hi
    (show 0 ≤ 1 + 2 * β by positivity)]

lemma width_mixing {a β τ : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4)
    (hb : 0 < β) (ht : 0 < τ) {t : ℕ}
    (htpos : 0 < t) (htsmall : t < width a β τ) :
    2 * a ≤ (1 + (t : ℝ) / τ) ^ (-β) := by
  let X := (2 * a) ^ (-(1 / β))
  have hX : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by positivity) (by linarith) (neg_nonpos.mpr (by positivity))
  have hfloor : t < ⌊τ * (X - 1)⌋₊ := by
    change t < max 1 ⌊τ * (X - 1)⌋₊ at htsmall
    omega
  have ht' : (t : ℝ) ≤ τ * (X - 1) :=
    (by exact_mod_cast hfloor.le : (t : ℝ) ≤ ⌊τ * (X - 1)⌋₊).trans
      (Nat.floor_le (mul_nonneg ht.le (sub_nonneg.mpr hX)))
  have hs : 1 + (t : ℝ) / τ ≤ X := by
    have := (div_le_iff₀ ht).mpr (ht'.trans_eq (mul_comm _ _))
    linarith
  have he := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + (t : ℝ) / τ) hs (neg_nonpos.mpr hb.le)
  unfold X at he
  rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * a), show -(1 / β) * -β = 1 by field_simp,
    Real.rpow_one] at he
  exact he


noncomputable def arrival (a β τ : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) : unitInterval :=
  ⟨a / width a β τ, div_nonneg ha (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast width_pos a β τ)).mpr
      (ha'.trans (by exact_mod_cast width_pos a β τ))⟩

lemma calibrated_regular {a β τ : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4)
    (hb : 0 < β) (ht : 0 < τ) :
    AbsolutelyRegular (burstLaw (width a β τ) (arrival a β τ ha.le (by linarith))) τ β := by
  let m := width a β τ
  let l := arrival a β τ ha.le (show a ≤ 1 by linarith)
  let P := burstLaw m l
  refine ⟨burst_stationary m l, ?_⟩
  intro n t B hB
  have he := burst_block_error m n t l B hB
  have hm : Measurable (fun z => (past (n + 1) z, future (n + t) z)) := by unfold past future; fun_prop
  rw [map_measureReal_apply hm hB] at he
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast width_pos a β τ
  apply he.trans
  by_cases hi : m ≤ t
  · rw [Nat.sub_eq_zero_of_le hi]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity
  have hc : ((m - t : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m t
  have hw : (m : ℝ) * (l : ℝ) = a := by
    change (m : ℝ) * (a / m) = a
    field_simp
  have hbound : 2 * ((m - t : ℕ) : ℝ) * (l : ℝ) ≤ 2 * a := by
    nlinarith [mul_le_mul_of_nonneg_right hc l.2.1]
  apply hbound.trans
  by_cases ht0 : t = 0
  · subst t
    simp
    linarith
  exact width_mixing ha ha' hb ht (Nat.pos_of_ne_zero ht0) (lt_of_not_ge hi)

lemma silence_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (n : ℕ) :
    Real.exp (-2 * x * n) ≤ (1 - x) ^ n := by
  have hpos : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have he : Real.exp (-2 * x) ≤ 1 - x := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  simpa [← Real.exp_nat_mul, mul_comm] using
    pow_le_pow_left₀ (Real.exp_pos _).le he n

lemma burst_probability_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1)
    (n : ℕ) : n * x / (1 + n * x) ≤ 1 - (1 - x) ^ n := by
  have he : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hx') he n
  rw [← Real.exp_nat_mul, mul_neg, Real.exp_neg] at hp
  have hlow := Real.add_one_le_exp ((n : ℝ) * x)
  have hi : (Real.exp ((n : ℝ) * x))⁻¹ ≤ (1 + n * x)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have h := hp.trans hi
  rw [div_le_iff₀ (by positivity)]
  have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ 1 + (n : ℝ) * x by positivity)
  rw [inv_mul_cancel₀ (by positivity : 1 + (n : ℝ) * x ≠ 0)] at h'
  nlinarith

end LongTails.Proofs.PolynomialMixingBurst
