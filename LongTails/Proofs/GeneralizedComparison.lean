import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import LongTails.Theorems.GeneralizedAcceleratedConvex

namespace OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

noncomputable def logPlus (x : ℝ) : ℝ := max (Real.log x) 0

lemma log_le_twice_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

lemma budget_log_le {r : ℝ} (hr : 1 ≤ r) : Real.log (4 + 4 * r) ≤ Real.log (8 * r) := by
  apply Real.log_le_log (by positivity)
  linarith

lemma ceil_power_le_twice {a : ℝ} (ha : 1 ≤ a) :
    (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) ≤ 2 * a := by
  have hp := Real.rpow_le_self_of_one_le ha (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ a) (2 / 3 : ℝ))
  linarith

lemma ceil_power_eq_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ⌈a ^ (2 / 3 : ℝ)⌉₊ = 1 := by
  apply Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0) |>.mpr
  norm_num only [Nat.sub_self, Nat.cast_zero, Nat.cast_one]
  exact ⟨Real.rpow_pos_of_pos ha _, Real.rpow_le_one ha.le ha1.le (by norm_num)⟩

lemma small_parameter_comparison {a r S u : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r) (hS : 0 < S) (hu : 0 < u)
    (hrel : S ^ 2 * u = 2 * r) :
    1 + S + (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * r) ≤
      8 * (1 + S + a * logPlus (min (a ^ 2 * u) (2 * r)) + logPlus u) := by
  rw [ceil_power_eq_one ha ha1, Nat.cast_one, one_mul]
  have hlogrel : Real.log r = 2 * Real.log S + Real.log u - Real.log 2 := by
    have h := congrArg Real.log hrel
    rw [Real.log_mul (pow_ne_zero _ hS.ne') hu.ne', Real.log_pow,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : r ≠ 0)] at h
    norm_num at h
    linarith
  have hlog := budget_log_le hr.le
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by linarith : r ≠ 0)] at hlog
  have h8 : Real.log (8 : ℝ) ≤ 7 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at hh
    exact hh
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hs := Real.log_le_sub_one_of_pos hS
  have hu' : Real.log u ≤ logPlus u := le_max_left _ _
  have hplus : 0 ≤ logPlus u := le_max_right _ _
  have hx : 0 ≤ a * logPlus (min (a ^ 2 * u) (2 * r)) :=
    mul_nonneg ha.le (le_max_right _ _)
  linarith

lemma large_parameter_log {a r S u : ℝ}
    (ha : 0 < a) (hr : 1 ≤ r) (hS : 0 < S) (hu : 0 < u)
    (hrel : S ^ 2 * u = 2 * r) :
    a * Real.log (4 + 4 * r) ≤
      8 * S + 4 * a * logPlus (min (a ^ 2 * u) (2 * r)) := by
  let t := a ^ 2 * u
  have ht : 0 < t := by dsimp [t]; positivity
  have hrp : 0 < r := by linarith
  have hlog := budget_log_le hr
  have hplus : 0 ≤ a * logPlus (min (a ^ 2 * u) (2 * r)) :=
    mul_nonneg ha.le (le_max_right _ _)
  by_cases hsmall : t ≤ 2
  · have hm := mul_le_mul_of_nonneg_left hsmall (sq_nonneg S)
    have he := congrArg (fun x => a ^ 2 * x) hrel
    have hsquare : (a * Real.sqrt r) ^ 2 = a ^ 2 * r := by
      rw [mul_pow, Real.sq_sqrt hrp.le]
    have hscale : a * Real.sqrt r ≤ S := by
      dsimp [t] at hm
      nlinarith [mul_nonneg ha.le (Real.sqrt_nonneg r)]
    have h8 : Real.sqrt (8 : ℝ) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hroot := mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg r)
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hroot
    have hl := log_le_twice_sqrt (mul_pos (by norm_num) hrp : 0 < 8 * r)
    have hb : Real.log (4 + 4 * r) ≤ 6 * Real.sqrt r := by linarith
    have hb' := mul_le_mul_of_nonneg_left hb ha.le
    nlinarith
  · by_cases hlast : 2 * r ≤ t
    · have hmin : min (a ^ 2 * u) (2 * r) = 2 * r := min_eq_right hlast
      have hlog2 : Real.log (2 : ℝ) ≤ Real.log (2 * r) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hlog8 : Real.log (8 * r) = 2 * Real.log 2 + Real.log (2 * r) := by
        rw [show 8 * r = (2 : ℝ) ^ 2 * (2 * r) by ring,
          Real.log_mul (by norm_num) (mul_pos (by norm_num) hrp).ne', Real.log_pow]
        norm_num
      have hb : Real.log (4 + 4 * r) ≤ 3 * logPlus (2 * r) := by
        have hp : Real.log (2 * r) ≤ logPlus (2 * r) := le_max_left _ _
        linarith
      have hm := mul_le_mul_of_nonneg_left hb ha.le
      rw [hmin] at hplus ⊢
      nlinarith
    · have hmin : min (a ^ 2 * u) (2 * r) = t := min_eq_left (le_of_not_ge hlast)
      have hlogsplit : Real.log (8 * r) = Real.log t + Real.log (8 * r / t) := by
        rw [Real.log_div (mul_pos (by norm_num) hrp).ne' ht.ne']
        ring
      have he : 8 * r / t = 4 * S ^ 2 / a ^ 2 := by
        dsimp [t]
        field_simp
        nlinarith only [hrel]
      have hroot : a * Real.sqrt (8 * r / t) = 2 * S := by
        rw [he, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 4 * S ^ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_sq hS.le, Real.sqrt_sq ha.le]
        norm_num
        field_simp
      have hl := log_le_twice_sqrt (show 0 < 8 * r / t by positivity)
      have hm := mul_le_mul_of_nonneg_left hl ha.le
      have hp := mul_le_mul_of_nonneg_left (le_max_left (Real.log t) 0) ha.le
      have hb := mul_le_mul_of_nonneg_left hlog ha.le
      rw [hmin] at hplus ⊢
      change a * Real.log t ≤ a * logPlus t at hp
      rw [hlogsplit] at hb
      nlinarith

lemma tyurin_comparison {a r S u : ℝ}
    (ha : 0 ≤ a) (hr : 1 < r) (hS : 0 < S) (hu : 0 < u)
    (hrel : S ^ 2 * u = 2 * r) :
    1 + S + (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * r) ≤
      32 * (1 + S + a * logPlus (min (a ^ 2 * u) (2 * r)) + logPlus u) := by
  have hplus : 0 ≤ a * logPlus (min (a ^ 2 * u) (2 * r)) :=
    mul_nonneg ha (le_max_right _ _)
  have huplus : 0 ≤ logPlus u := le_max_right _ _
  by_cases hz : a = 0
  · subst a
    norm_num
    linarith
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    by_cases hsmall : a < 1
    · have h := small_parameter_comparison hap hsmall hr hS hu hrel
      linarith
    · have hceil := ceil_power_le_twice (le_of_not_gt hsmall)
      have hlog : 0 ≤ Real.log (4 + 4 * r) := Real.log_nonneg (by linarith)
      have hm := mul_le_mul_of_nonneg_right hceil hlog
      have hl := large_parameter_log hap hr.le hS hu hrel
      nlinarith

lemma vankov_log_bound {r : ℝ} (hr : 1 ≤ r) :
    Real.log (4 + 4 * r) ≤ 3 * (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ) := by
  have hrp : 0 < r := by linarith
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h2one : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (2 * r) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog8 : Real.log (8 * r) = 2 * Real.log 2 + Real.log (2 * r) := by
    rw [show 8 * r = (2 : ℝ) ^ 2 * (2 * r) by ring,
      Real.log_mul (by norm_num) (mul_pos (by norm_num) hrp).ne', Real.log_pow]
    norm_num
  have hceil := (div_le_iff₀ h2).mp (Nat.le_ceil (Real.log (2 * r) / Real.log 2))
  have hmul := mul_le_mul_of_nonneg_left h2one
    (show 0 ≤ (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ) by positivity)
  have hlog := budget_log_le hr
  linarith

lemma vankov_comparison {a r S : ℝ} (ha : 0 ≤ a) (hr : 1 < r) (hS : 0 ≤ S) :
    1 + S + (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * r) ≤
      3 * (1 + Real.sqrt 48 * S +
        (⌈3 * (2 : ℝ) ^ (2 / 3 : ℝ) * a ^ (2 / 3 : ℝ)⌉₊ : ℝ) *
          (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ)) := by
  have hb := vankov_log_bound hr.le
  have ht := Real.rpow_nonneg ha (2 / 3 : ℝ)
  have h2 : 1 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hcoeff : a ^ (2 / 3 : ℝ) ≤ 3 * (2 : ℝ) ^ (2 / 3 : ℝ) * a ^ (2 / 3 : ℝ) := by
    nlinarith
  have hceil : (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) ≤
      (⌈3 * (2 : ℝ) ^ (2 / 3 : ℝ) * a ^ (2 / 3 : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_mono hcoeff
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) by positivity)
  have hm' := mul_le_mul_of_nonneg_right hceil
    (show 0 ≤ (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ) by positivity)
  have hs : 1 ≤ Real.sqrt (48 : ℝ) := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs' := mul_le_mul_of_nonneg_right hs hS
  nlinarith

lemma budget_shape_bound (q : Params)
     (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    (budget q 0 : ℝ) ≤ 16384 * (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) +
      (⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * q.Δ / q.ε)) := by
  let X := 1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) +
    (⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * q.Δ / q.ε)
  have hlog : 0 ≤ Real.log (4 + 4 * q.Δ / q.ε) := by
    apply Real.log_nonneg
    have h := div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hΔ) hε
    linarith
  have hX : 1 ≤ X := by
    dsimp [X]
    have h := mul_nonneg (Nat.cast_nonneg ⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊) hlog
    linarith [Real.sqrt_nonneg (q.L0 * q.R ^ 2 / q.ε)]
  unfold budget
  split_ifs with h
  · norm_num only [Nat.cast_zero]
    change 0 ≤ 16384 * X
    linarith
  · have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4096 * X by linarith)
    push_cast
    change 2 * (⌈4096 * X⌉₊ : ℝ) ≤ 16384 * X
    linarith

lemma budget_tyurin_bound (q : Params) (hL0 : 0 < q.L0) (hL1 : 0 ≤ q.L1)
    (hR : 0 < q.R) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    let S := Real.sqrt (q.L0 * q.R ^ 2 / q.ε)
    let a := q.L1 * q.R
    let r := q.Δ / q.ε
    let u := 2 * q.Δ / (q.L0 * q.R ^ 2)
    (budget q 0 : ℝ) ≤ 524288 * (1 + S + a * logPlus (min (a ^ 2 * u) (2 * r)) + logPlus u) := by
  let S := Real.sqrt (q.L0 * q.R ^ 2 / q.ε)
  let a := q.L1 * q.R
  let r := q.Δ / q.ε
  let u := 2 * q.Δ / (q.L0 * q.R ^ 2)
  have ha : 0 ≤ a := mul_nonneg hL1 hR.le
  have hS : 0 < S := by dsimp [S]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  change (budget q 0 : ℝ) ≤ 524288 * (1 + S + a * logPlus (min (a ^ 2 * u) (2 * r)) + logPlus u)
  by_cases h : q.Δ ≤ q.ε
  · rw [budget, ite_eq_left h]
    norm_num only [Nat.cast_zero]
    dsimp [logPlus]
    positivity
  · have hr : 1 < r := (one_lt_div hε).mpr (lt_of_not_ge h)
    have hrel : S ^ 2 * u = 2 * r := by
      dsimp [S, u, r]
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    have ht := tyurin_comparison ha hr hS hu hrel
    have hb : (budget q 0 : ℝ) ≤ 16384 * (1 + S +
        (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * r)) := by
      simpa only [S, a, r, mul_div_assoc] using budget_shape_bound q hΔ hε
    nlinarith only [ht, hb]

lemma budget_vankov_bound (q : Params) (hL0 : 0 < q.L0) (hL1 : 0 ≤ q.L1)
    (hR : 0 < q.R) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    let S := Real.sqrt (q.L0 * q.R ^ 2 / q.ε)
    let a := q.L1 * q.R
    let r := q.Δ / q.ε
    (budget q 0 : ℝ) ≤ 49152 * (1 + Real.sqrt 48 * S +
      (⌈3 * (2 : ℝ) ^ (2 / 3 : ℝ) * a ^ (2 / 3 : ℝ)⌉₊ : ℝ) *
        (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ)) := by
  let S := Real.sqrt (q.L0 * q.R ^ 2 / q.ε)
  let a := q.L1 * q.R
  let r := q.Δ / q.ε
  have ha : 0 ≤ a := mul_nonneg hL1 hR.le
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  dsimp only
  by_cases h : q.Δ ≤ q.ε
  · rw [budget, ite_eq_left h]
    norm_num only [Nat.cast_zero]
    positivity
  · have hr : 1 < r := (one_lt_div hε).mpr (lt_of_not_ge h)
    have hv := vankov_comparison ha hr hS
    have hb : (budget q 0 : ℝ) ≤ 16384 * (1 + S +
        (⌈a ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * r)) := by
      simpa only [S, a, r, mul_div_assoc] using budget_shape_bound q hΔ hε
    change (budget q 0 : ℝ) ≤ 49152 * (1 + Real.sqrt 48 * S +
      (⌈3 * (2 : ℝ) ^ (2 / 3 : ℝ) * a ^ (2 / 3 : ℝ)⌉₊ : ℝ) *
        (⌈Real.log (2 * r) / Real.log 2⌉₊ : ℝ))
    nlinarith only [hv, hb]

end OracleTemplate.GeneralizedAccelerated
