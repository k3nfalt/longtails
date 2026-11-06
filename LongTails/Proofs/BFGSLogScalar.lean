import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.BFGSLogScalar

lemma one_sub_pow_ge (l : ℝ) (k : ℕ) (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    k * l ^ k * (1 - l) ≤ 1 - l ^ k := by
  have hsum : (∑ j ∈ Finset.range k, l ^ j) * (1 - l) = 1 - l ^ k := by
    have := geom_sum_mul_neg l k
    linarith [this]
  have hge : (k : ℝ) * l ^ k ≤ ∑ j ∈ Finset.range k, l ^ j := by
    have : ∀ j ∈ Finset.range k, l ^ k ≤ l ^ j := by
      intro j hj
      exact pow_le_pow_of_le_one h0 h1 (le_of_lt (Finset.mem_range.mp hj))
    calc (k : ℝ) * l ^ k = ∑ _j ∈ Finset.range k, l ^ k := by simp
      _ ≤ ∑ j ∈ Finset.range k, l ^ j := Finset.sum_le_sum this
  rw [← hsum]
  exact mul_le_mul_of_nonneg_right hge (by linarith)

lemma boundary_max (l C : ℝ) (k : ℕ) (h0 : 0 ≤ l) (h1 : l ≤ 1)
    (hC : C * (k + 1) ≤ k) : l ^ k * (1 - C * l) ≤ 1 - C := by
  have key := one_sub_pow_ge l k h0 h1
  have hlk : 0 ≤ l ^ k := pow_nonneg h0 k
  have e : 1 - C - l ^ k * (1 - C * l) = (1 - l ^ k) * (1 - C) - C * l ^ k * (1 - l) := by ring
  have h1C : 0 ≤ 1 - C := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hm : 0 ≤ l ^ k * (1 - l) := mul_nonneg hlk (sub_nonneg.mpr h1)
  have h2 : (k : ℝ) * l ^ k * (1 - l) * (1 - C) ≤ (1 - l ^ k) * (1 - C) :=
    mul_le_mul_of_nonneg_right key h1C
  have h3 : 0 ≤ l ^ k * (1 - l) * ((k : ℝ) - C * (k + 1)) :=
    mul_nonneg hm (by linarith)
  nlinarith [h2, h3, e]

lemma amgm_bound (t : ℝ) (k : ℕ) (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    4 ^ k * t ^ (k - 1) * (1 - t) ^ k ≤ 4 * k / (2 * k - 1) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hN : (0 : ℝ) < 2 * k - 1 := by linarith
  set w1 : ℝ := ((k : ℝ) - 1) / (2 * k - 1)
  set w2 : ℝ := (k : ℝ) / (2 * k - 1)
  have hw1 : 0 ≤ w1 := div_nonneg (by linarith) hN.le
  have hw2 : 0 ≤ w2 := div_nonneg hkpos.le hN.le
  have hN' : (2 * (k : ℝ) - 1) ≠ 0 := hN.ne'
  have hw : w1 + w2 = 1 := by
    simp only [w1, w2]
    rw [← add_div, div_eq_one_iff_eq hN']
    ring
  set p1 : ℝ := t * (2 * k - 1) / ((k : ℝ) - 1)
  set p2 : ℝ := (1 - t) * (2 * k - 1) / k
  have hp1 : 0 ≤ p1 := div_nonneg (mul_nonneg ht0 hN.le) (by linarith)
  have hp2 : 0 ≤ p2 := div_nonneg (mul_nonneg (by linarith) hN.le) hkpos.le
  have hk1ne : ((k : ℝ) - 1) ≠ 0 := by linarith
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have e1 : w1 * p1 = t := by
    simp only [w1, p1]
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hN' hk1ne)]
    ring
  have e2 : w2 * p2 = 1 - t := by
    simp only [w2, p2]
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hN' hkne)]
    ring
  have hsum : w1 * p1 + w2 * p2 = 1 := by rw [e1, e2]; ring
  have hg := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 hp2 hw
  rw [hsum] at hg
  have hpow : (p1 ^ w1 * p2 ^ w2) ^ (2 * (k : ℝ) - 1) = p1 ^ ((k : ℝ) - 1) * p2 ^ (k : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hp1 _) (Real.rpow_nonneg hp2 _),
      ← Real.rpow_mul hp1, ← Real.rpow_mul hp2]
    congr 2
    · simp only [w1]; exact div_mul_cancel₀ _ hN'
    · simp only [w2]; exact div_mul_cancel₀ _ hN'
  have hle1 : p1 ^ ((k : ℝ) - 1) * p2 ^ (k : ℝ) ≤ 1 := by
    rw [← hpow]
    have hb : 0 ≤ p1 ^ w1 * p2 ^ w2 :=
      mul_nonneg (Real.rpow_nonneg hp1 _) (Real.rpow_nonneg hp2 _)
    calc (p1 ^ w1 * p2 ^ w2) ^ (2 * (k : ℝ) - 1) ≤ 1 ^ (2 * (k : ℝ) - 1) :=
          Real.rpow_le_rpow hb hg (by linarith)
      _ = 1 := Real.one_rpow _
  have hk1n : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hnat : p1 ^ (k - 1) * p2 ^ k ≤ 1 := by
    have e1 : p1 ^ ((k : ℝ) - 1) = p1 ^ (k - 1) := by
      rw [← hk1n, Real.rpow_natCast]
    have e2 : p2 ^ (k : ℝ) = p2 ^ k := Real.rpow_natCast p2 k
    rw [← e1, ← e2]
    exact hle1
  have hexp : t ^ (k - 1) * (1 - t) ^ k = p1 ^ (k - 1) * p2 ^ k * w1 ^ (k - 1) * w2 ^ k := by
    rw [← e2, ← e1, mul_pow, mul_pow]; ring
  have hconst : 4 ^ k * w1 ^ (k - 1) * w2 ^ k ≤ 4 * k / (2 * k - 1) := by
    have h4 : (4 : ℝ) ^ k = 4 ^ (k - 1) * 4 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hb : w2 ^ k = w2 ^ (k - 1) * w2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have heq : 4 ^ k * w1 ^ (k - 1) * w2 ^ k = 4 * w2 * (4 * w1 * w2) ^ (k - 1) := by
      rw [h4, hb, mul_pow, mul_pow]; ring
    have hab : 4 * w1 * w2 ≤ 1 := by
      have : 4 * w1 * w2 = (4 * ((k : ℝ) - 1) * k) / ((2 * k - 1) * (2 * k - 1)) := by
        simp only [w1, w2, div_eq_mul_inv, mul_inv]; ring
      rw [this, div_le_one (by positivity)]
      nlinarith
    have hab0 : 0 ≤ 4 * w1 * w2 := by positivity
    have hpw : (4 * w1 * w2) ^ (k - 1) ≤ 1 := pow_le_one₀ hab0 hab
    rw [heq]
    have h4w : 4 * w2 = 4 * k / (2 * k - 1) := by simp only [w2]; ring
    rw [← h4w]
    have : 0 ≤ 4 * w2 := by positivity
    calc 4 * w2 * (4 * w1 * w2) ^ (k - 1) ≤ 4 * w2 * 1 := mul_le_mul_of_nonneg_left hpw this
      _ = 4 * w2 := mul_one _
  have hc0 : 0 ≤ 4 ^ k * w1 ^ (k - 1) * w2 ^ k := by positivity
  calc 4 ^ k * t ^ (k - 1) * (1 - t) ^ k = 4 ^ k * (t ^ (k - 1) * (1 - t) ^ k) := by ring
    _ = (p1 ^ (k - 1) * p2 ^ k) * (4 ^ k * w1 ^ (k - 1) * w2 ^ k) := by rw [hexp]; ring
    _ ≤ 1 * (4 ^ k * w1 ^ (k - 1) * w2 ^ k) :=
        mul_le_mul_of_nonneg_right hnat hc0
    _ ≤ 4 * k / (2 * k - 1) := by rw [one_mul]; exact hconst

lemma core_bound (t p ν νb : ℝ) (k : ℕ) (hk : 2 ≤ k) (ht0 : 0 < t) (ht1 : t < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1 - t) (hν : ν ≤ νb) (hνb : 2 ≤ νb * (k + 1)) :
    (4 * t * p) ^ k * (1 - t - p * (1 - ν / 2)) ≤
      νb * (1 + 1 / (2 * k - 1)) * (t * (1 - t)) := by
  have hA : 0 < 1 - t := by linarith
  set C := 1 - νb / 2 with hCdef
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hC : C * (k + 1) ≤ k := by
    have : C * (k + 1) = (k + 1) - νb * (k + 1) / 2 := by ring
    rw [this]; linarith
  have step1 : 1 - t - p * (1 - ν / 2) ≤ (1 - t) - C * p := by
    have : p * (ν / 2) ≤ p * (νb / 2) := mul_le_mul_of_nonneg_left (by linarith) hp0.le
    simp only [C]; nlinarith
  set l := p / (1 - t) with hl
  have hl0 : 0 ≤ l := div_nonneg hp0.le hA.le
  have hl1 : l ≤ 1 := (div_le_one hA).mpr hp1
  have hpl : p = l * (1 - t) := by simp only [l]; field_simp
  have step2 : p ^ k * ((1 - t) - C * p) ≤ (1 - t) ^ (k + 1) * (1 - C) := by
    have hb := boundary_max l C k hl0 hl1 hC
    rw [hpl, mul_pow]
    have e : (l ^ k * (1 - t) ^ k) * ((1 - t) - C * (l * (1 - t))) =
        (1 - t) ^ (k + 1) * (l ^ k * (1 - C * l)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hb (pow_nonneg hA.le _)
  have h1C : 1 - C = νb / 2 := by simp only [C]; ring
  have hpk : 0 ≤ (4 * t * p) ^ k := by positivity
  have hamgm := amgm_bound t k hk ht0.le ht1.le
  calc (4 * t * p) ^ k * (1 - t - p * (1 - ν / 2))
      ≤ (4 * t * p) ^ k * ((1 - t) - C * p) := mul_le_mul_of_nonneg_left step1 hpk
    _ = 4 ^ k * t ^ k * (p ^ k * ((1 - t) - C * p)) := by rw [mul_pow, mul_pow]; ring
    _ ≤ 4 ^ k * t ^ k * ((1 - t) ^ (k + 1) * (1 - C)) :=
        mul_le_mul_of_nonneg_left step2 (by positivity)
    _ = (νb / 2) * (t * (1 - t)) * (4 ^ k * t ^ (k - 1) * (1 - t) ^ k) := by
        have htk : t ^ k = t ^ (k - 1) * t := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
        rw [h1C, pow_succ (1 - t) k, htk]
        ring
    _ ≤ (νb / 2) * (t * (1 - t)) * (4 * k / (2 * k - 1)) := by
        apply mul_le_mul_of_nonneg_left hamgm
        have : 0 ≤ νb := by
          have : (0 : ℝ) < k + 1 := by linarith
          nlinarith
        positivity
    _ = νb * (1 + 1 / (2 * k - 1)) * (t * (1 - t)) := by
        have hN : (2 * (k : ℝ) - 1) ≠ 0 := by linarith
        field_simp
        ring

lemma core_bound_any (t p ν : ℝ) (k : ℕ) (hk : 1 ≤ k) (ht0 : 0 < t) (ht1 : t < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1 - t) (hν : 0 ≤ ν) :
    (4 * t * p) ^ k * (1 - t - p * (1 - ν / 2)) ≤ 4 * (1 + ν / 2) * (t * (1 - t)) := by
  have hA : 0 < 1 - t := by linarith
  have h4 : 4 * t * p ≤ 1 := by nlinarith [sq_nonneg (2 * t - 1)]
  have h4' : 0 ≤ 4 * t * p := by positivity
  have hpow : (4 * t * p) ^ k ≤ 4 * t * p := by
    calc (4 * t * p) ^ k ≤ (4 * t * p) ^ 1 := pow_le_pow_of_le_one h4' h4 hk
      _ = 4 * t * p := pow_one _
  have hlin : 1 - t - p * (1 - ν / 2) ≤ (1 - t) * (1 + ν / 2) := by nlinarith
  have hp1' : p ≤ 1 := by linarith
  rcases le_or_gt (1 - t - p * (1 - ν / 2)) 0 with hneg | hpos
  · have : (4 * t * p) ^ k * (1 - t - p * (1 - ν / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    have : 0 ≤ 4 * (1 + ν / 2) * (t * (1 - t)) := by positivity
    linarith
  · calc (4 * t * p) ^ k * (1 - t - p * (1 - ν / 2))
        ≤ (4 * t * p) * ((1 - t) * (1 + ν / 2)) :=
          mul_le_mul hpow hlin hpos.le h4'
      _ ≤ (4 * t * 1) * ((1 - t) * (1 + ν / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
      _ = 4 * (1 + ν / 2) * (t * (1 - t)) := by ring

end LongTails.Proofs.BFGSLogScalar
