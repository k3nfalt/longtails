import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace OracleTemplate.FrankWolfe

lemma negative_power_le_two {p ρ : ℝ} (hp : 1 ≤ p) (hρ : ρ < 1)
    (hsmall : p * ρ ≤ 1 / 2) : (1 - ρ) ^ (-p) ≤ 2 := by
  have h := one_add_mul_self_le_rpow_one_add (s := -ρ) (by linarith) hp
  have hbase : 0 < 1 - ρ := by linarith
  have hpow : 0 < (1 - ρ) ^ p := Real.rpow_pos_of_pos hbase _
  rw [Real.rpow_neg hbase.le]
  apply (inv_le_comm₀ hpow (by norm_num : (0 : ℝ) < 2)).mpr
  norm_num
  simp only [← sub_eq_add_neg, mul_neg] at h
  nlinarith

lemma negative_power_increment {p ρ : ℝ} (hp : 0 ≤ p) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    p * ρ ≤ (1 - ρ) ^ (-p) - 1 ∧
      (1 - ρ) ^ (-p) - 1 ≤ p * ρ * (1 - ρ) ^ (-p - 1) := by
  rcases hρ.eq_or_lt with h | h
  · subst ρ
    simp
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) ρ,
      HasDerivAt (fun x : ℝ => (1 - x) ^ (-p)) (p * (1 - x) ^ (-p - 1)) x := by
    intro x hx
    have hx1 : 1 - x ≠ 0 := ne_of_gt (by linarith [hx.2])
    convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).rpow_const
      (p := -p) (Or.inl hx1) using 1 <;> simp
  obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope
    (fun x : ℝ => (1 - x) ^ (-p)) (fun x => p * (1 - x) ^ (-p - 1)) h
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
  simp only [sub_zero, Real.one_rpow] at heq
  have hxpos : 0 < 1 - x := by linarith [hx.2]
  have hlo : 1 ≤ (1 - x) ^ (-p - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hxpos (by linarith [hx.1])
      (by linarith)
  have hhi : (1 - x) ^ (-p - 1) ≤ (1 - ρ) ^ (-p - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hx.2]) (by linarith)
  have heq' := (eq_div_iff (ne_of_gt h)).mp heq
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hp]
  · have hh := mul_le_mul_of_nonneg_left hhi hp
    nlinarith [mul_le_mul_of_nonneg_right hh hρ]

lemma perturbed_contraction {F : ℝ → ℝ} {v w δ rate error : ℝ}
    (hv : |v - 1| ≤ δ) (hrate : 0 ≤ rate)
    (hF : |F v - 1| ≤ rate * |v - 1|)
    (he : |w - F v| ≤ error) (hmargin : error ≤ (1 - rate) * δ) :
    |w - 1| ≤ δ := by
  have h := (abs_add_le (w - F v) (F v - 1)).trans (add_le_add he hF)
  have hm := mul_le_mul_of_nonneg_left hv hrate
  have heq : w - F v + (F v - 1) = w - 1 := by ring
  rw [heq] at h
  nlinarith

lemma reciprocal_power_step {u p c : ℝ} (hu : 0 < u) (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hsmall : c * u ^ p < 1)
    (hfactor : (1 - c * u ^ p) ^ (-p - 1) ≤ 2) :
    p * c ≤ (u * (1 - c * u ^ p)) ^ (-p) - u ^ (-p) ∧
      (u * (1 - c * u ^ p)) ^ (-p) - u ^ (-p) ≤ 2 * p * c := by
  have hρ : 0 ≤ c * u ^ p := mul_nonneg hc (Real.rpow_nonneg hu.le p)
  have h := negative_power_increment hp hρ hsmall
  have ht : 0 ≤ u ^ (-p) := Real.rpow_nonneg hu.le _
  have hcancel : u ^ (-p) * u ^ p = 1 := by
    rw [← Real.rpow_add hu]
    simp
  have hlo := mul_le_mul_of_nonneg_left h.1 ht
  have hhi := mul_le_mul_of_nonneg_left h.2 ht
  have hh := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hp hρ)
  have hh' := mul_le_mul_of_nonneg_left hh ht
  rw [Real.mul_rpow hu.le (by linarith : 0 ≤ 1 - c * u ^ p)]
  have heq : u ^ (-p) * (p * (c * u ^ p)) = p * c := by
    calc
      _ = (p * c) * (u ^ (-p) * u ^ p) := by ring
      _ = p * c := by rw [hcancel, mul_one]
  constructor <;> nlinarith

lemma reciprocal_power_trajectory {u c : ℕ → ℝ} {p lower upper : ℝ}
    (hp : 0 ≤ p) (hlower : 0 ≤ lower)
    (hu : ∀ n, 0 < u n) (hc : ∀ n, lower ≤ c n ∧ c n ≤ upper)
    (hsmall : ∀ n, c n * (u n) ^ p < 1)
    (hfactor : ∀ n, (1 - c n * (u n) ^ p) ^ (-p - 1) ≤ 2)
    (hstep : ∀ n, u (n + 1) = u n * (1 - c n * (u n) ^ p)) (n : ℕ) :
    (u 0) ^ (-p) + p * lower * n ≤ (u n) ^ (-p) ∧
      (u n) ^ (-p) ≤ (u 0) ^ (-p) + 2 * p * upper * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := reciprocal_power_step (hu n) hp (hlower.trans (hc n).1)
      (hsmall n) (hfactor n)
    rw [← hstep n] at h
    have hlo := mul_le_mul_of_nonneg_left (hc n).1 hp
    have hhi := mul_le_mul_of_nonneg_left (hc n).2 hp
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, h.1, h.2]

lemma reciprocal_descent_step {a b p κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : 0 ≤ p) (hκ : 0 ≤ κ) (hd : b ≤ a - κ * a ^ (1 + p)) :
    p * κ ≤ b ^ (-p) - a ^ (-p) := by
  have hba : b ≤ a := by
    have := mul_nonneg hκ (Real.rpow_nonneg ha.le (1 + p))
    linarith
  let ρ := 1 - b / a
  have hρ : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one ha).mpr hba)
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := div_pos hb ha; linarith
  have h := (negative_power_increment hp hρ hρ1).1
  have heq : 1 - ρ = b / a := by dsimp [ρ]; ring
  rw [heq, Real.div_rpow hb.le ha.le] at h
  have hscaled := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg ha.le (-p))
  have hpos : 0 < a ^ (-p) := Real.rpow_pos_of_pos ha _
  have hcanc : (b ^ (-p) / a ^ (-p) - 1) * a ^ (-p) = b ^ (-p) - a ^ (-p) := by
    field_simp
  rw [hcanc] at hscaled
  have hpow : a ^ (1 + p) / a = a ^ p := by
    rw [Real.rpow_add ha, Real.rpow_one]
    field_simp
  have hρlower : κ * a ^ p ≤ ρ := by
    have hh := div_le_div_of_nonneg_right hd ha.le
    rw [sub_div, div_self ha.ne', mul_div_assoc, hpow] at hh
    dsimp [ρ]
    linarith
  have hc : a ^ p * a ^ (-p) = 1 := by rw [← Real.rpow_add ha]; simp
  have hmul := mul_le_mul_of_nonneg_right hρlower hpos.le
  have hmul' : κ ≤ ρ * a ^ (-p) := by nlinarith [hc]
  nlinarith [mul_le_mul_of_nonneg_left hmul' hp]

lemma power_lower_of_reciprocal_upper {u p r B : ℝ} (hu : 0 < u) (hp : 0 < p)
    (hr : 0 ≤ r) (hbound : u ^ (-p) ≤ B) : B ^ (-r / p) ≤ u ^ r := by
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hu (-p)) hbound
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) hp.le)
  rw [← Real.rpow_mul hu.le] at h
  have he : -p * (-r / p) = r := by field_simp
  rwa [he] at h

end OracleTemplate.FrankWolfe
