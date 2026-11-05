import LongTails.Algorithms.SymmetricThirdOrder
import LongTails.Proofs.SymmetricThirdOrderTuning

namespace LongTails.Proofs.SymmetricThirdOrderBudget

open LongTails.Algorithms.SymmetricThirdOrder
open SymmetricThirdOrderTuning

lemma shape_bounds {F H K : ℝ} (hF : 0 ≤ F) (hH : 0 ≤ H) (hK : 0 ≤ K) :
    let Z := 2 + F + H + K
    let l := 1 + Real.log Z
    let S := 1 + Real.sqrt H + K ^ (1 / 5 : ℝ)
    2 ≤ Z ∧ 1 ≤ l ∧ 1 ≤ S ∧ S ≤ 3 * Z := by
  let Z := 2 + F + H + K
  have hZ : 2 ≤ Z := by dsimp [Z]; linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hrootH : Real.sqrt H ≤ Z := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    have hHZ : H ≤ Z := by dsimp [Z]; linarith
    nlinarith
  have hrootK : K ^ (1 / 5 : ℝ) ≤ Z := by
    have hKZ : K ≤ Z := by dsimp [Z]; linarith
    have hh := Real.rpow_le_rpow hK hKZ (by norm_num : (0 : ℝ) ≤ 1 / 5)
    have he := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : (1 / 5 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using hh.trans he
  refine ⟨hZ, ?_, ?_, ?_⟩
  · have hh := Real.log_nonneg hZ1
    linarith
  · have hh := Real.rpow_nonneg hK (1 / 5 : ℝ)
    have hs := Real.sqrt_nonneg H
    linarith
  · change 1 + Real.sqrt H + K ^ (1 / 5 : ℝ) ≤ 3 * Z
    linarith

lemma outer_ceil_bounds {S l : ℝ} (hS : 1 ≤ S) (hl : 1 ≤ l) :
    let T := ⌈(2 : ℝ) ^ 24 * S * l ^ 2⌉₊
    (2 : ℝ) ^ 24 * S * l ^ 2 ≤ T ∧ (T : ℝ) ≤ (2 : ℝ) ^ 25 * S * l ^ 2 ∧
      (2 : ℝ) ^ 24 ≤ T := by
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hSl : 1 ≤ S * l ^ 2 := by nlinarith
  have hpos : 0 ≤ (2 : ℝ) ^ 24 * S * l ^ 2 := by positivity
  have hlo := Nat.le_ceil ((2 : ℝ) ^ 24 * S * l ^ 2)
  have hhi := Nat.ceil_lt_add_one hpos
  refine ⟨hlo, ?_, ?_⟩
  · norm_num only [show (2 : ℝ) ^ 25 = 33554432 by norm_num,
      show (2 : ℝ) ^ 24 = 16777216 by norm_num] at *
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hSl (by positivity : 0 ≤ (2 : ℝ) ^ 24)
    nlinarith only [hh, hlo]

lemma normalized_curvature_bounds {H Z S l T : ℝ}
    (hH : 0 ≤ H) (hHZ : H ≤ Z) (hZ : 1 ≤ Z) (hl : 1 ≤ l)
    (hSZ : S ≤ 3 * Z)
    (hT : (2 : ℝ) ^ 24 ≤ T) (hTu : T ≤ (2 : ℝ) ^ 25 * S * l ^ 2) :
    1 ≤ T ^ 2 / (2 : ℝ) ^ 24 + 288 * H ∧
      T ^ 2 / (2 : ℝ) ^ 24 + 288 * H ≤ (2 : ℝ) ^ 30 * Z ^ 2 * l ^ 4 := by
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hl4 : 1 ≤ l ^ 4 := by nlinarith [sq_nonneg (l ^ 2 - 1)]
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZl : Z ≤ Z ^ 2 * l ^ 4 := by nlinarith [sq_nonneg Z]
  have hT0 : 0 ≤ T := by norm_num at hT; linarith
  have ht : T ≤ (2 : ℝ) ^ 25 * (3 * Z) * l ^ 2 := hTu.trans (by gcongr)
  have htsq : T ^ 2 ≤ ((2 : ℝ) ^ 25 * (3 * Z) * l ^ 2) ^ 2 := by gcongr
  have he : ((2 : ℝ) ^ 25 * (3 * Z) * l ^ 2) ^ 2 =
      9 * (2 : ℝ) ^ 50 * (Z ^ 2 * l ^ 4) := by ring
  rw [he] at htsq
  constructor
  · norm_num at hT ⊢
    nlinarith
  · norm_num at htsq ⊢
    nlinarith

lemma log_polynomial_bound {x Z l : ℝ} (hx : 0 < x) (hZ : 1 ≤ Z) (hl : 1 ≤ l)
    (hlogZ : Real.log Z ≤ l) (q r s : ℕ)
    (hbound : x ≤ (2 : ℝ) ^ q * Z ^ r * l ^ s) :
    Real.log x ≤ ((q + r + s : ℕ) : ℝ) * l := by
  have hZ0 : 0 < Z := by linarith
  have hl0 : 0 < l := by linarith
  have hh := Real.log_le_log hx hbound
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ q * Z ^ r ≠ 0) (by positivity : l ^ s ≠ 0),
    Real.log_mul (by positivity : (2 : ℝ) ^ q ≠ 0) (by positivity : Z ^ r ≠ 0),
    Real.log_pow, Real.log_pow, Real.log_pow] at hh
  have htwo : Real.log 2 ≤ l := log_two_bounds.2.trans hl
  have hlogl : Real.log l ≤ l := (Real.log_le_sub_one_of_pos hl0).trans (by linarith)
  have hq := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg q)
  have hr := mul_le_mul_of_nonneg_left hlogZ (Nat.cast_nonneg r)
  have hs := mul_le_mul_of_nonneg_left hlogl (Nat.cast_nonneg s)
  push_cast
  nlinarith

lemma ceil_log_bound {x base l c b : ℝ} (hx : 1 ≤ x) (hl : 1 ≤ l)
    (hc : 0 ≤ c) (hb : 0 < b) (hbase : 1 / b ≤ Real.log base) (hlog : Real.log x ≤ c * l) :
    (⌈Real.log x / Real.log base⌉₊ : ℝ) ≤ (b * c + 1) * l := by
  have hb₀ : 0 < Real.log base := (by positivity : 0 < 1 / b).trans_le hbase
  have hnum : 0 ≤ Real.log x := Real.log_nonneg hx
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnum hb₀.le)
  have hdiv : Real.log x / Real.log base ≤ b * c * l := by
    apply (div_le_iff₀ hb₀).mpr
    have he : 1 ≤ b * Real.log base := by simpa only [mul_comm] using (div_le_iff₀ hb).mp hbase
    have hh := mul_le_mul_of_nonneg_right he (mul_nonneg hc (by linarith : 0 ≤ l))
    nlinarith
  linarith

lemma grid_log_bound {K d Z l : ℝ} (hK : 0 ≤ K) (hKZ : K ≤ Z) (hd : 1 ≤ d)
    (hZ : 1 ≤ Z) (hl : 1 ≤ l) (hlogZ : Real.log Z ≤ l) :
    (⌈Real.log (1 + 32 * K / d) / Real.log 4⌉₊ : ℝ) ≤ 32 * l := by
  have hd0 : 0 < d := by linarith
  have hx : 1 ≤ 1 + 32 * K / d := le_add_of_nonneg_right (by positivity)
  have hdiv : K / d ≤ K := (div_le_iff₀ hd0).mpr (by nlinarith)
  have hbound : 1 + 32 * K / d ≤ (2 : ℝ) ^ 6 * Z ^ 1 * l ^ 0 := by
    norm_num
    have hh : 32 * K / d = 32 * (K / d) := by ring
    rw [hh]
    linarith
  have hg := log_polynomial_bound (by linarith : 0 < 1 + 32 * K / d) hZ hl hlogZ 6 1 0 hbound
  have hbase : 1 / (1 : ℝ) ≤ Real.log 4 := by
    have hh := log_two_bounds.1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hh := ceil_log_bound hx hl (by norm_num : (0 : ℝ) ≤ 7) (by norm_num : (0 : ℝ) < 1) hbase (by norm_num at hg ⊢; exact hg)
  norm_num at hh
  linarith

lemma phase_log_bound {K d Z l : ℝ} (hK : 0 ≤ K) (hKZ : K ≤ Z) (hd : 0 ≤ d)
    (hdu : d ≤ (2 : ℝ) ^ 30 * Z ^ 2 * l ^ 4)
    (hZ : 1 ≤ Z) (hl : 1 ≤ l) (hlogZ : Real.log Z ≤ l) :
    (⌈Real.log (1 + 24 * (d + 32 * K)) / Real.log 2⌉₊ : ℝ) ≤ 128 * l := by
  have hl4 : 1 ≤ l ^ 4 := by nlinarith [sq_nonneg (l ^ 2 - 1)]
  have hZl : Z ≤ Z ^ 2 * l ^ 4 := by nlinarith [sq_nonneg Z]
  have hx : 1 ≤ 1 + 24 * (d + 32 * K) := by linarith
  have hbound : 1 + 24 * (d + 32 * K) ≤ (2 : ℝ) ^ 36 * Z ^ 2 * l ^ 4 := by
    norm_num at hdu ⊢
    nlinarith
  have hg := log_polynomial_bound (by linarith : 0 < 1 + 24 * (d + 32 * K)) hZ hl hlogZ 36 2 4 hbound
  have hh := ceil_log_bound hx hl (by norm_num : (0 : ℝ) ≤ 42) (by norm_num : (0 : ℝ) < 2)
    log_two_bounds.1 (by norm_num at hg ⊢; exact hg)
  norm_num at hh
  linarith

lemma inner_log_bound {F K d Z S l T : ℝ}
    (hF : 0 ≤ F) (hFZ : F ≤ Z) (hK : 0 ≤ K) (hKZ : K ≤ Z) (hd : 0 ≤ d)
    (hdu : d ≤ (2 : ℝ) ^ 30 * Z ^ 2 * l ^ 4)
    (hZ : 1 ≤ Z) (hl : 1 ≤ l) (hlogZ : Real.log Z ≤ l) (hSZ : S ≤ 3 * Z)
    (hT : 0 ≤ T) (hTu : T ≤ (2 : ℝ) ^ 25 * S * l ^ 2) :
    (⌈Real.log (1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d)) / Real.log (7 / 6)⌉₊ : ℝ) + 1 ≤
      1024 * l := by
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hl4 : 1 ≤ l ^ 4 := by nlinarith [sq_nonneg (l ^ 2 - 1)]
  have hZl : Z ≤ Z ^ 2 * l ^ 4 := by nlinarith [sq_nonneg Z]
  have ht : T ≤ (2 : ℝ) ^ 27 * Z * l ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hSZ (by positivity : 0 ≤ (2 : ℝ) ^ 25 * l ^ 2)
    norm_num at hh hTu ⊢
    nlinarith
  have hD : F + 3 * K + d ≤ (2 : ℝ) ^ 31 * Z ^ 2 * l ^ 4 := by
    norm_num at hdu ⊢
    nlinarith
  have hprod := mul_le_mul ht hD (by positivity : 0 ≤ F + 3 * K + d)
    (by positivity : 0 ≤ (2 : ℝ) ^ 27 * Z * l ^ 2)
  have hx : 1 ≤ 1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d) := le_add_of_nonneg_right (by positivity)
  have hZ3 : 1 ≤ Z ^ 3 := one_le_pow₀ hZ
  have hl6 : 1 ≤ l ^ 6 := one_le_pow₀ hl
  have hmon : 1 ≤ Z ^ 3 * l ^ 6 := by nlinarith
  have hbound : 1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d) ≤ (2 : ℝ) ^ 86 * Z ^ 3 * l ^ 6 := by
    have he : ((2 : ℝ) ^ 27 * Z * l ^ 2) * ((2 : ℝ) ^ 31 * Z ^ 2 * l ^ 4) =
        (2 : ℝ) ^ 58 * (Z ^ 3 * l ^ 6) := by ring
    rw [he] at hprod
    norm_num at hprod ⊢
    nlinarith
  have hg := log_polynomial_bound (by linarith : 0 < 1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d))
    hZ hl hlogZ 86 3 6 hbound
  have hbase : 1 / (7 : ℝ) ≤ Real.log (7 / 6) := by
    have hh := log_lower_inverse (by norm_num : (0 : ℝ) < 7 / 6)
    norm_num at hh ⊢
    exact hh
  have hh := ceil_log_bound hx hl (by norm_num : (0 : ℝ) ≤ 95) (by norm_num : (0 : ℝ) < 7)
    hbase (by norm_num at hg ⊢; exact hg)
  norm_num at hh
  linarith

lemma groups_log_bound {Z S l T J : ℝ}
    (hZ : 1 ≤ Z) (hl : 1 ≤ l) (hlogZ : Real.log Z ≤ l) (hSZ : S ≤ 3 * Z)
    (hT : 1 ≤ T) (hTu : T ≤ (2 : ℝ) ^ 25 * S * l ^ 2)
    (hJ : 0 ≤ J) (hJu : J ≤ 1024 * l) :
    (⌈Real.log (6 * T * (2 * J + 5)) / Real.log (3 / 2)⌉₊ : ℝ) ≤ 256 * l := by
  have ht : T ≤ (2 : ℝ) ^ 27 * Z * l ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hSZ (by positivity : 0 ≤ (2 : ℝ) ^ 25 * l ^ 2)
    norm_num at hh hTu ⊢
    nlinarith
  have hj : 2 * J + 5 ≤ 4096 * l := by linarith
  have hx : 1 ≤ 6 * T * (2 * J + 5) := by nlinarith
  have hprod := mul_le_mul ht hj (by positivity : 0 ≤ 2 * J + 5)
    (by positivity : 0 ≤ (2 : ℝ) ^ 27 * Z * l ^ 2)
  have hbound : 6 * T * (2 * J + 5) ≤ (2 : ℝ) ^ 42 * Z ^ 1 * l ^ 3 := by
    have he : ((2 : ℝ) ^ 27 * Z * l ^ 2) * (4096 * l) = (2 : ℝ) ^ 39 * (Z * l ^ 3) := by ring
    rw [he] at hprod
    norm_num at hprod ⊢
    have hnonneg : 0 ≤ Z * l ^ 3 := by positivity
    nlinarith
  have hg := log_polynomial_bound (by linarith : 0 < 6 * T * (2 * J + 5)) hZ hl hlogZ 42 1 3 hbound
  have hbase : 1 / (3 : ℝ) ≤ Real.log (3 / 2) := by
    have hh := log_lower_inverse (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at hh ⊢
    exact hh
  have hh := ceil_log_bound hx hl (by norm_num : (0 : ℝ) ≤ 46) (by norm_num : (0 : ℝ) < 3)
    hbase (by norm_num at hg ⊢; exact hg)
  norm_num at hh
  linarith

lemma normalized_batch_bounds {G d T : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hT : 0 < T)
    (hfloor : T ^ 2 / (2 : ℝ) ^ 24 ≤ d) :
    let m := ⌈144 * (2 : ℝ) ^ 24 * G * T / d⌉₊ + 1
    0 < m ∧ 144 * G ≤ (m : ℝ) * d / ((2 : ℝ) ^ 24 * T) ∧
      T * m ≤ (2 : ℝ) ^ 56 * G + 2 * T := by
  let m := ⌈144 * (2 : ℝ) ^ 24 * G * T / d⌉₊ + 1
  change 0 < m ∧ 144 * G ≤ (m : ℝ) * d / ((2 : ℝ) ^ 24 * T) ∧
    T * m ≤ (2 : ℝ) ^ 56 * G + 2 * T
  have hpos : 0 ≤ 144 * (2 : ℝ) ^ 24 * G * T / d := by positivity
  have hlo := Nat.le_ceil (144 * (2 : ℝ) ^ 24 * G * T / d)
  have hhi := Nat.ceil_lt_add_one hpos
  have hml : 144 * (2 : ℝ) ^ 24 * G * T / d ≤ (m : ℝ) := by
    dsimp [m]
    push_cast
    linarith
  have hmu : (m : ℝ) ≤ 144 * (2 : ℝ) ^ 24 * G * T / d + 2 := by
    dsimp [m]
    push_cast
    linarith
  refine ⟨by omega, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 24 * T)).mpr
    have hh := (div_le_iff₀ hd).mp hml
    nlinarith only [hh]
  · have hr : T ^ 2 / d ≤ (2 : ℝ) ^ 24 := by
      apply (div_le_iff₀ hd).mpr
      have hh := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 24)).mp hfloor
      nlinarith only [hh]
    have hmult := mul_le_mul_of_nonneg_left hmu hT.le
    have he : T * (144 * (2 : ℝ) ^ 24 * G * T / d + 2) =
        144 * (2 : ℝ) ^ 24 * G * (T ^ 2 / d) + 2 * T := by ring
    rw [he] at hmult
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 144 * (2 : ℝ) ^ 24 * G)
    norm_num at hh hmult ⊢
    linarith

lemma productive_calls_bound {S G l T m k J : ℝ}
    (hS : 1 ≤ S) (hG : 0 ≤ G) (hl : 1 ≤ l) (hT : 0 ≤ T) (hm : 0 ≤ m)
    (hk : 0 ≤ k) (hJ : 0 ≤ J)
    (hTu : T ≤ (2 : ℝ) ^ 25 * S * l ^ 2)
    (hTm : T * m ≤ (2 : ℝ) ^ 56 * G + 2 * T)
    (hku : k ≤ 256 * l) (hJu : J ≤ 1024 * l) :
    T * (k * (3 + 2 * m * (J + 1)) + m) ≤ (2 : ℝ) ^ 80 * (S + G) * l ^ 4 := by
  have hS0 : 0 ≤ S := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl
  have hl24 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hl (by decide)
  have hl34 : l ^ 3 ≤ l ^ 4 := pow_le_pow_right₀ hl (by decide)
  have hGl : G ≤ G * l ^ 2 := by nlinarith
  have hU : T * m ≤ (2 : ℝ) ^ 57 * (S + G) * l ^ 2 := by
    norm_num at hTu hTm ⊢
    nlinarith [mul_nonneg hS0 (sq_nonneg l)]
  have hj : J + 1 ≤ 2048 * l := by linarith
  have hku' := mul_le_mul hku hU (mul_nonneg hT hm) (by positivity : 0 ≤ 256 * l)
  have htriple := mul_le_mul hku' hj (by positivity : 0 ≤ J + 1)
    (by positivity : 0 ≤ (256 * l) * ((2 : ℝ) ^ 57 * (S + G) * l ^ 2))
  have hmain : 2 * k * (T * m) * (J + 1) ≤ (2 : ℝ) ^ 77 * (S + G) * l ^ 4 := by
    have he : (256 * l) * ((2 : ℝ) ^ 57 * (S + G) * l ^ 2) * (2048 * l) =
        (2 : ℝ) ^ 76 * ((S + G) * l ^ 4) := by ring
    rw [he] at htriple
    norm_num at htriple ⊢
    nlinarith only [htriple]
  have hTk := mul_le_mul hTu hku hk (by positivity : 0 ≤ (2 : ℝ) ^ 25 * S * l ^ 2)
  have hSD : S * l ^ 3 ≤ (S + G) * l ^ 4 :=
    mul_le_mul (by linarith) hl34 (by positivity) (by positivity)
  have hUD : (S + G) * l ^ 2 ≤ (S + G) * l ^ 4 :=
    mul_le_mul_of_nonneg_left hl24 (by positivity)
  have hsmall : 3 * T * k ≤ (2 : ℝ) ^ 35 * (S + G) * l ^ 4 := by
    have he : ((2 : ℝ) ^ 25 * S * l ^ 2) * (256 * l) = (2 : ℝ) ^ 33 * (S * l ^ 3) := by ring
    rw [he] at hTk
    norm_num at hTk ⊢
    nlinarith [mul_nonneg (show 0 ≤ S + G by positivity) (pow_nonneg hl0 4)]
  have hU' : T * m ≤ (2 : ℝ) ^ 57 * (S + G) * l ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hUD (by positivity : 0 ≤ (2 : ℝ) ^ 57)
    nlinarith only [hU, hh]
  have he : T * (k * (3 + 2 * m * (J + 1)) + m) =
      3 * T * k + 2 * k * (T * m) * (J + 1) + T * m := by ring
  rw [he]
  norm_num at hmain hsmall hU' ⊢
  nlinarith [mul_nonneg (show 0 ≤ S + G by positivity) (pow_nonneg hl0 4)]

lemma outer_fifth_bound {K S l T : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hl : 1 ≤ l)
    (hroot : K ^ (1 / 5 : ℝ) ≤ S) (hT : (2 : ℝ) ^ 24 * S * l ^ 2 ≤ T) :
    (2 : ℝ) ^ 42 * K ≤ T ^ 5 := by
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl
  have hSl : S ≤ S * l ^ 2 := by nlinarith
  have ht : (2 : ℝ) ^ 24 * K ^ (1 / 5 : ℝ) ≤ T := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ 24 * K ^ (1 / 5 : ℝ)) ht 5
  rw [mul_pow, fifth_root_power hK] at hp
  norm_num at hp ⊢
  nlinarith

lemma normalized_cleanup_bound {K d T : ℝ} (hT : 0 < T)
    (hfloor : T ^ 2 / (2 : ℝ) ^ 24 ≤ d) (hfifth : (2 : ℝ) ^ 42 * K ≤ T ^ 5) :
    (2 : ℝ) ^ 18 * K * (d / ((2 : ℝ) ^ 24 * T)) ≤ d ^ 3 := by
  have hd : 0 < d := (by positivity : 0 < T ^ 2 / (2 : ℝ) ^ 24).trans_le hfloor
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ T ^ 2 / (2 : ℝ) ^ 24) hfloor 2
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2 : ℝ) ^ 24 * T)
  have he : (2 : ℝ) ^ 24 * T * (T ^ 2 / (2 : ℝ) ^ 24) ^ 2 = T ^ 5 / (2 : ℝ) ^ 24 := by ring
  rw [he] at hm
  have hcore : (2 : ℝ) ^ 18 * K ≤ (2 : ℝ) ^ 24 * T * d ^ 2 := by
    norm_num at hfifth hm ⊢
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcore hd.le
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 24 * T)).mpr
  nlinarith only [hh]

lemma pilot_groups_suffice (T J : ℕ) (hT : 0 < T) :
    (T : ℝ) * (2 * J + 5) * (2 / 3 : ℝ) ^
      ⌈Real.log (6 * T * (2 * (J : ℝ) + 5)) / Real.log (3 / 2)⌉₊ ≤ 1 / 6 := by
  let k := ⌈Real.log (6 * T * (2 * (J : ℝ) + 5)) / Real.log (3 / 2)⌉₊
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hh : 6 * T * (2 * (J : ℝ) + 5) ≤ (3 / 2 : ℝ) ^ k :=
    LoraSilverTuning.pow_ceil_log (by norm_num) (by positivity)
  have he : (3 / 2 : ℝ) ^ k * (2 / 3 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hp := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (2 / 3 : ℝ) ^ k)
  rw [he] at hp
  change (T : ℝ) * (2 * J + 5) * (2 / 3 : ℝ) ^ k ≤ 1 / 6
  nlinarith only [hp]

lemma energy_budget_bound {R ε δ a σ T m : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hδ : 0 < δ) (hT : 0 < T) (hm : 0 < m)
    (ha : a ^ 2 = ε * δ / ((2 : ℝ) ^ 24 * T)) (hsize : 144 * σ ^ 2 ≤ m * a ^ 2) :
    R ^ 2 / 2 + T * ((3 * (6 * R ^ 2 / ε)) * (2450 * a ^ 2 + σ ^ 2 / m) / (2 * δ)) ≤ R ^ 2 := by
  have hvar : σ ^ 2 / m ≤ a ^ 2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [sq_nonneg σ]
  have hh := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ T * (3 * (6 * R ^ 2 / ε)) / (2 * δ))
  have he : T * (3 * (6 * R ^ 2 / ε)) / (2 * δ) * (2451 * a ^ 2) =
      (22059 / (2 : ℝ) ^ 24) * R ^ 2 := by
    rw [ha]
    field_simp
    ring
  have hbase : T * ((3 * (6 * R ^ 2 / ε)) * (2450 * a ^ 2 + σ ^ 2 / m) / (2 * δ)) ≤
      (22059 / (2 : ℝ) ^ 24) * R ^ 2 := by
    rw [← he]
    linear_combination hh
  norm_num at hbase
  nlinarith [sq_nonneg R]

lemma scaled_identities {R ε d T L Δ : ℝ} (hR : 0 < R) (hε : 0 < ε) (hd : 0 < d) (hT : 0 < T) :
    let δ := (ε / R ^ 2) * d
    let a := (ε / R) * Real.sqrt (d / ((2 : ℝ) ^ 24 * T))
    0 < δ ∧ 0 < a ∧ a ^ 2 = ε * δ / ((2 : ℝ) ^ 24 * T) ∧
      δ * (6 * R ^ 2 / ε) = 6 * d ∧
      (δ + 32 * L * R ^ 2) / δ = 1 + 32 * (L * R ^ 4 / ε) / d ∧
      8 * (Δ + 3 * L * R ^ 4 + δ * R ^ 2) * δ / a ^ 2 =
        (2 : ℝ) ^ 27 * T * (Δ / ε + 3 * (L * R ^ 4 / ε) + d) := by
  let δ := (ε / R ^ 2) * d
  let a := (ε / R) * Real.sqrt (d / ((2 : ℝ) ^ 24 * T))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₂ : a ^ 2 = ε * δ / ((2 : ℝ) ^ 24 * T) := by
    dsimp [a, δ]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ d / ((2 : ℝ) ^ 24 * T))]
    field_simp
  refine ⟨hδ, ha, ha₂, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · change 8 * (Δ + 3 * L * R ^ 4 + δ * R ^ 2) * δ / a ^ 2 = _
    rw [ha₂]
    dsimp [δ]
    field_simp
    ring

lemma scaled_hessian_floor {R ε d σ : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hfloor : 288 * (σ * R ^ 2 / ε) ≤ d) : 288 * σ ≤ (ε / R ^ 2) * d := by
  have hh := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ ε / R ^ 2)
  have he : (ε / R ^ 2) * (288 * (σ * R ^ 2 / ε)) = 288 * σ := by field_simp
  rwa [he] at hh

lemma scaled_batch_condition {R ε d T σ m a : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (ha : a ^ 2 = ε * ((ε / R ^ 2) * d) / ((2 : ℝ) ^ 24 * T))
    (hsize : 144 * (σ ^ 2 * R ^ 2 / ε ^ 2) ≤ m * d / ((2 : ℝ) ^ 24 * T)) :
    144 * σ ^ 2 ≤ m * a ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ ε ^ 2 / R ^ 2)
  have he : ε ^ 2 / R ^ 2 * (144 * (σ ^ 2 * R ^ 2 / ε ^ 2)) = 144 * σ ^ 2 := by field_simp
  have he' : ε ^ 2 / R ^ 2 * (m * d / ((2 : ℝ) ^ 24 * T)) = m * a ^ 2 := by
    rw [ha]
    ring
  rwa [he, he'] at hh

lemma scaled_cleanup_condition {R ε d T L a : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (ha : a ^ 2 = ε * ((ε / R ^ 2) * d) / ((2 : ℝ) ^ 24 * T))
    (hclean : (2 : ℝ) ^ 18 * (L * R ^ 4 / ε) * (d / ((2 : ℝ) ^ 24 * T)) ≤ d ^ 3) :
    262144 * L * a ^ 2 ≤ ((ε / R ^ 2) * d) ^ 3 := by
  have hh := mul_le_mul_of_nonneg_left hclean (by positivity : 0 ≤ ε ^ 3 / R ^ 6)
  have he : ε ^ 3 / R ^ 6 * ((2 : ℝ) ^ 18 * (L * R ^ 4 / ε) * (d / ((2 : ℝ) ^ 24 * T))) =
      262144 * L * a ^ 2 := by
    rw [ha]
    field_simp
    ring
  have he' : ε ^ 3 / R ^ 6 * d ^ 3 = ((ε / R ^ 2) * d) ^ 3 := by ring
  rwa [he, he'] at hh

lemma tuned_call_budget {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x0 : E) (L R Δ ε σg σh : ℝ) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hσh : 0 ≤ σh) :
    roundCalls (tunedConfig x0 L R Δ ε σg σh) * iterationCount L R Δ ε σh ≤
      ⌈(2 : ℝ) ^ 100 * (1 + Real.sqrt (σh * R ^ 2 / ε) + (L * R ^ 4 / ε) ^ (1 / 5 : ℝ) +
        σg ^ 2 * R ^ 2 / ε ^ 2) * (1 + Real.log (2 + Δ / ε + σh * R ^ 2 / ε + L * R ^ 4 / ε)) ^ 4⌉₊ := by
  let H := σh * R ^ 2 / ε
  let K := L * R ^ 4 / ε
  let F := Δ / ε
  let G := σg ^ 2 * R ^ 2 / ε ^ 2
  let Z := 2 + F + H + K
  let l := 1 + Real.log Z
  let S := 1 + Real.sqrt H + K ^ (1 / 5 : ℝ)
  let T := iterationCount L R Δ ε σh
  let d := (T : ℝ) ^ 2 / (2 : ℝ) ^ 24 + 288 * H
  let J := ⌈Real.log (1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d)) / Real.log (7 / 6)⌉₊ + 1
  let k := ⌈Real.log (6 * T * (2 * (J : ℝ) + 5)) / Real.log (3 / 2)⌉₊
  let m := ⌈144 * (2 : ℝ) ^ 24 * G * T / d⌉₊ + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  obtain ⟨hZ2, hl, hS, hSZ⟩ := shape_bounds hF hH hK
  change 2 ≤ Z at hZ2
  change 1 ≤ l at hl
  change 1 ≤ S at hS
  change S ≤ 3 * Z at hSZ
  have hZ : 1 ≤ Z := by linarith
  have hlogZ : Real.log Z ≤ l := by dsimp [l]; linarith
  have hFZ : F ≤ Z := by dsimp [Z]; linarith
  have hHZ : H ≤ Z := by dsimp [Z]; linarith
  have hKZ : K ≤ Z := by dsimp [Z]; linarith
  have ht := outer_ceil_bounds hS hl
  change (2 : ℝ) ^ 24 * S * l ^ 2 ≤ T ∧ (T : ℝ) ≤ (2 : ℝ) ^ 25 * S * l ^ 2 ∧ (2 : ℝ) ^ 24 ≤ T at ht
  have hTpos : 0 < (T : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 24).trans_le ht.2.2
  have hT1 : 1 ≤ (T : ℝ) := le_trans (by norm_num) ht.2.2
  have hd := normalized_curvature_bounds hH hHZ hZ hl hSZ ht.2.2 ht.2.1
  change 1 ≤ d ∧ d ≤ (2 : ℝ) ^ 30 * Z ^ 2 * l ^ 4 at hd
  have hdpos : 0 < d := by linarith [hd.1]
  have hJu : (J : ℝ) ≤ 1024 * l := by
    have hh := inner_log_bound hF hFZ hK hKZ hdpos.le hd.2 hZ hl hlogZ hSZ hTpos.le ht.2.1
    simpa only [J, Nat.cast_add, Nat.cast_one] using hh
  have hku : (k : ℝ) ≤ 256 * l := groups_log_bound hZ hl hlogZ hSZ hT1 ht.2.1 (Nat.cast_nonneg J) hJu
  have hfloor : (T : ℝ) ^ 2 / (2 : ℝ) ^ 24 ≤ d := by
    dsimp [d]
    exact le_add_of_nonneg_right (by positivity)
  have hm := normalized_batch_bounds hG hdpos hTpos hfloor
  have hcalls := productive_calls_bound hS hG hl hTpos.le (Nat.cast_nonneg m) (Nat.cast_nonneg k)
    (Nat.cast_nonneg J) ht.2.1 hm.2.2 hku hJu
  have hreal : (((k * (3 + 2 * m * (J + 1)) + m) * T : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 100 * (S + G) * l ^ 4 := by
    calc
      _ = (T : ℝ) * ((k : ℝ) * (3 + 2 * (m : ℝ) * ((J : ℝ) + 1)) + m) := by push_cast; ring
      _ ≤ (2 : ℝ) ^ 80 * (S + G) * l ^ 4 := hcalls
      _ ≤ _ := by gcongr <;> norm_num
  have hfinal := hreal.trans (Nat.le_ceil ((2 : ℝ) ^ 100 * (S + G) * l ^ 4))
  have hn : (k * (3 + 2 * m * (J + 1)) + m) * T ≤ ⌈(2 : ℝ) ^ 100 * (S + G) * l ^ 4⌉₊ := by
    exact_mod_cast hfinal
  exact hn

structure ParameterConditions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (cfg : Config E) (T : ℕ) (R Δ ε σg : ℝ) : Prop where
  iterations_pos : 0 < T
  delta_pos : 0 < cfg.δ
  tolerance_pos : 0 < cfg.tolerance
  hessian_floor : 288 * cfg.σh ≤ cfg.δ
  threshold_pos : 0 < cfg.threshold
  weight_floor : 1 ≤ cfg.δ * cfg.threshold
  batch_pos : 0 < cfg.batch
  batch_size : 144 * σg ^ 2 ≤ (cfg.batch : ℝ) * cfg.tolerance ^ 2
  inner_pos : 0 < cfg.innerRounds
  inner_tuning : (6 / 7 : ℝ) ^ (cfg.innerRounds - 1) *
    (8 * (Δ + 3 * cfg.L * R ^ 4 + cfg.δ * R ^ 2)) ≤ cfg.tolerance ^ 2 / cfg.δ
  cleanup : 262144 * cfg.L * cfg.tolerance ^ 2 ≤ cfg.δ ^ 3
  grid_lower : cfg.δ + 32 * cfg.L * R ^ 2 ≤ cfg.δ * 4 ^ cfg.gridTop
  grid_upper : cfg.δ * 4 ^ cfg.gridTop ≤ 4 * (cfg.δ + 32 * cfg.L * R ^ 2)
  count : 1 + 64 * Real.sqrt (cfg.δ * cfg.threshold) +
    384 * (cfg.L * ((8 / 3 : ℝ) * (6 * R ^ 2)) * cfg.threshold) ^ (1 / 5 : ℝ) +
    ((cfg.gridTop : ℝ) + 2) * ⌈Real.log (1 + 4 * (cfg.δ + 32 * cfg.L * R ^ 2) * cfg.threshold) / Real.log 2⌉₊ < T
  energy : R ^ 2 / 2 + T * ((3 * cfg.threshold) *
    (2450 * cfg.tolerance ^ 2 + σg ^ 2 / cfg.batch) / (2 * cfg.δ)) ≤ R ^ 2
  pilot : (T : ℝ) * (2 * cfg.innerRounds + 5) * (2 / 3 : ℝ) ^ cfg.groups ≤ 1 / 6
  accuracy : 6 * R ^ 2 ≤ cfg.threshold * ε

lemma tuned_conditions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x0 : E) (L R Δ ε σg σh : ℝ) (hL : 0 < L) (hR : 0 < R) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hσh : 0 ≤ σh) :
    ParameterConditions (tunedConfig x0 L R Δ ε σg σh) (iterationCount L R Δ ε σh) R Δ ε σg := by
  let H := σh * R ^ 2 / ε
  let K := L * R ^ 4 / ε
  let F := Δ / ε
  let G := σg ^ 2 * R ^ 2 / ε ^ 2
  let Z := 2 + F + H + K
  let l := 1 + Real.log Z
  let S := 1 + Real.sqrt H + K ^ (1 / 5 : ℝ)
  let T := iterationCount L R Δ ε σh
  let d := (T : ℝ) ^ 2 / (2 : ℝ) ^ 24 + 288 * H
  let cfg := tunedConfig x0 L R Δ ε σg σh
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  obtain ⟨hZ2, hl, hS, hSZ⟩ := shape_bounds hF hH hK
  change 2 ≤ Z at hZ2
  change 1 ≤ l at hl
  change 1 ≤ S at hS
  change S ≤ 3 * Z at hSZ
  have hZ : 1 ≤ Z := by linarith
  have hlogZ : Real.log Z ≤ l := by dsimp [l]; linarith
  have hHZ : H ≤ Z := by dsimp [Z]; linarith
  have hKZ : K ≤ Z := by dsimp [Z]; linarith
  have ht := outer_ceil_bounds hS hl
  change (2 : ℝ) ^ 24 * S * l ^ 2 ≤ T ∧ (T : ℝ) ≤ (2 : ℝ) ^ 25 * S * l ^ 2 ∧ (2 : ℝ) ^ 24 ≤ T at ht
  have hTpos : 0 < (T : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 24).trans_le ht.2.2
  have hTnat : 0 < T := by exact_mod_cast hTpos
  have hd := normalized_curvature_bounds hH hHZ hZ hl hSZ ht.2.2 ht.2.1
  change 1 ≤ d ∧ d ≤ (2 : ℝ) ^ 30 * Z ^ 2 * l ^ 4 at hd
  have hdpos : 0 < d := by linarith [hd.1]
  have hfloor : (T : ℝ) ^ 2 / (2 : ℝ) ^ 24 ≤ d := by
    dsimp [d]
    exact le_add_of_nonneg_right (by positivity)
  obtain ⟨hδ, ha, ha₂, hδX, hgrid, hinnerarg⟩ := scaled_identities (L := L) (Δ := Δ) hR hε hdpos hTpos
  change 0 < cfg.δ at hδ
  change 0 < cfg.tolerance at ha
  change cfg.tolerance ^ 2 = ε * cfg.δ / ((2 : ℝ) ^ 24 * T) at ha₂
  change cfg.δ * cfg.threshold = 6 * d at hδX
  change (cfg.δ + 32 * L * R ^ 2) / cfg.δ = 1 + 32 * K / d at hgrid
  change 8 * (Δ + 3 * L * R ^ 4 + cfg.δ * R ^ 2) * cfg.δ / cfg.tolerance ^ 2 =
    (2 : ℝ) ^ 27 * T * (F + 3 * K + d) at hinnerarg
  have hδσ : 288 * σh ≤ cfg.δ := scaled_hessian_floor hR hε (by
    change 288 * H ≤ d
    dsimp [d]
    exact le_add_of_nonneg_left (by positivity))
  have hX : 0 < cfg.threshold := by change 0 < 6 * R ^ 2 / ε; positivity
  have hδXfloor : 1 ≤ cfg.δ * cfg.threshold := by rw [hδX]; linarith [hd.1]
  have hm := normalized_batch_bounds hG hdpos hTpos hfloor
  change 0 < cfg.batch ∧ 144 * G ≤ (cfg.batch : ℝ) * d / ((2 : ℝ) ^ 24 * T) ∧
    (T : ℝ) * cfg.batch ≤ (2 : ℝ) ^ 56 * G + 2 * T at hm
  have hsize : 144 * σg ^ 2 ≤ (cfg.batch : ℝ) * cfg.tolerance ^ 2 :=
    scaled_batch_condition hR hε ha₂ hm.2.1
  have hD : 0 ≤ Δ + 3 * L * R ^ 4 + cfg.δ * R ^ 2 := by positivity
  have hin := inner_rounds_suffice hD hδ ha
  rw [hinnerarg] at hin
  have hinner : (6 / 7 : ℝ) ^ (cfg.innerRounds - 1) *
      (8 * (Δ + 3 * L * R ^ 4 + cfg.δ * R ^ 2)) ≤ cfg.tolerance ^ 2 / cfg.δ := by
    change (6 / 7 : ℝ) ^ ((⌈Real.log (1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d)) / Real.log (7 / 6)⌉₊ + 1) - 1) * _ ≤ _
    simpa only [Nat.add_sub_cancel] using hin
  have hrootS : K ^ (1 / 5 : ℝ) ≤ S := by dsimp [S]; have := Real.sqrt_nonneg H; linarith
  have hHs : Real.sqrt H ≤ S := by dsimp [S]; have := Real.rpow_nonneg hK (1 / 5 : ℝ); linarith
  have hfifth := outer_fifth_bound hK hS hl hrootS ht.1
  have hclean : 262144 * L * cfg.tolerance ^ 2 ≤ cfg.δ ^ 3 :=
    scaled_cleanup_condition hR hε ha₂ (normalized_cleanup_bound hTpos hfloor hfifth)
  have hgrids := grid_top_bounds hδ (show cfg.δ ≤ cfg.δ + 32 * L * R ^ 2 from le_add_of_nonneg_right (by positivity))
  rw [hgrid] at hgrids
  change cfg.δ + 32 * L * R ^ 2 ≤ cfg.δ * 4 ^ cfg.gridTop ∧
    cfg.δ * 4 ^ cfg.gridTop ≤ 4 * (cfg.δ + 32 * L * R ^ 2) at hgrids
  have hM : (cfg.gridTop : ℝ) ≤ 32 * l := grid_log_bound hK hKZ hd.1 hZ hl hlogZ
  have hphase := phase_log_bound hK hKZ hdpos.le hd.2 hZ hl hlogZ
  have hcount := normalized_count_bound hH hK hl hS hHs hrootS ht.1 hM
    (Nat.cast_nonneg ⌈Real.log (1 + 24 * (d + 32 * K)) / Real.log 2⌉₊) hphase
  have hrootid : L * ((8 / 3 : ℝ) * (6 * R ^ 2)) * cfg.threshold = 96 * K := by
    change L * ((8 / 3 : ℝ) * (6 * R ^ 2)) * (6 * R ^ 2 / ε) = 96 * (L * R ^ 4 / ε)
    ring
  have hphaseid : 1 + 4 * (cfg.δ + 32 * L * R ^ 2) * cfg.threshold = 1 + 24 * (d + 32 * K) := by
    change 1 + 4 * ((ε / R ^ 2) * d + 32 * L * R ^ 2) * (6 * R ^ 2 / ε) = _
    dsimp [K]
    field_simp
    ring
  have hcount' : 1 + 64 * Real.sqrt (cfg.δ * cfg.threshold) +
      384 * (L * ((8 / 3 : ℝ) * (6 * R ^ 2)) * cfg.threshold) ^ (1 / 5 : ℝ) +
      ((cfg.gridTop : ℝ) + 2) * ⌈Real.log (1 + 4 * (cfg.δ + 32 * L * R ^ 2) * cfg.threshold) / Real.log 2⌉₊ < T := by
    rw [hδX, hrootid, hphaseid]
    exact hcount.trans_lt (by linarith)
  have henergy := energy_budget_bound hR hε hδ hTpos (show 0 < (cfg.batch : ℝ) by exact_mod_cast hm.1) ha₂ hsize
  refine {
    iterations_pos := hTnat
    delta_pos := hδ
    tolerance_pos := ha
    hessian_floor := hδσ
    threshold_pos := hX
    weight_floor := hδXfloor
    batch_pos := hm.1
    batch_size := hsize
    inner_pos := ?_
    inner_tuning := hinner
    cleanup := hclean
    grid_lower := hgrids.1
    grid_upper := hgrids.2
    count := hcount'
    energy := henergy
    pilot := pilot_groups_suffice T cfg.innerRounds hTnat
    accuracy := ?_ }
  · change 0 < ⌈Real.log (1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d)) / Real.log (7 / 6)⌉₊ + 1
    omega
  · change 6 * R ^ 2 ≤ (6 * R ^ 2 / ε) * ε
    rw [div_mul_cancel₀ _ hε.ne']

end LongTails.Proofs.SymmetricThirdOrderBudget
