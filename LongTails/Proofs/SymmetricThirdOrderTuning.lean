import LongTails.Proofs.LoraSilverTuning

namespace LongTails.Proofs.SymmetricThirdOrderTuning

lemma inner_rounds_suffice {D δ a : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) (ha : 0 < a) :
    (6 / 7 : ℝ) ^ ⌈Real.log (1 + 8 * D * δ / a ^ 2) / Real.log (7 / 6)⌉₊ * (8 * D) ≤
      a ^ 2 / δ := by
  let k := ⌈Real.log (1 + 8 * D * δ / a ^ 2) / Real.log (7 / 6)⌉₊
  have hp : 1 + 8 * D * δ / a ^ 2 ≤ (7 / 6 : ℝ) ^ k :=
    LoraSilverTuning.pow_ceil_log (by norm_num) (by positivity)
  have hpow : (6 / 7 : ℝ) ^ k * (7 / 6 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hd : 8 * D * δ ≤ a ^ 2 * (7 / 6 : ℝ) ^ k := by
    have hh := (div_le_iff₀ (sq_pos_of_pos ha)).mp
      (show 8 * D * δ / a ^ 2 ≤ (7 / 6 : ℝ) ^ k by linarith)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (6 / 7 : ℝ) ^ k)
  apply (le_div_iff₀ hδ).mpr
  have he : (6 / 7 : ℝ) ^ k * (a ^ 2 * (7 / 6 : ℝ) ^ k) = a ^ 2 := by
    calc
      _ = a ^ 2 * ((6 / 7 : ℝ) ^ k * (7 / 6 : ℝ) ^ k) := by ring
      _ = _ := by rw [hpow]; ring
  rw [he] at hm
  change (6 / 7 : ℝ) ^ k * (8 * D) * δ ≤ a ^ 2
  nlinarith

lemma phase_threshold_balance {δ b L D U h : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hU : 0 ≤ U) (hU₅ : U ^ 5 = L * D * b) (hh : h = 2 * δ + U ^ 2 / b) :
    8 * Real.sqrt h * Real.sqrt (2 * b) + 32 * L * D / (b * h ^ 2) ≤
      16 * Real.sqrt (δ * b) + 48 * U := by
  have hbh : b * h = 2 * δ * b + U ^ 2 := by rw [hh]; field_simp
  have hpos : 0 < h := by rw [hh]; positivity
  have hdb : 0 < δ * b := mul_pos hδ hb
  have hlow : U ^ 2 ≤ b * h := by nlinarith
  have hsq : U ^ 4 ≤ b ^ 2 * h ^ 2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg U) hlow 2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hU
  have hmain : L * D ≤ U * b * h ^ 2 := by
    apply (mul_le_mul_iff_right₀ hb).mp
    nlinarith only [hm, hU₅]
  have hfrac : 32 * L * D / (b * h ^ 2) ≤ 32 * U := by
    apply (div_le_iff₀ (by positivity : 0 < b * h ^ 2)).mpr
    nlinarith only [hmain]
  have ht : (Real.sqrt h * Real.sqrt (2 * b)) ^ 2 = 4 * δ * b + 2 * U ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpos.le, Real.sq_sqrt (by positivity : 0 ≤ 2 * b)]
    nlinarith only [hbh]
  have hr : Real.sqrt h * Real.sqrt (2 * b) ≤ 2 * Real.sqrt (δ * b) + 2 * U := by
    have hs := Real.sq_sqrt hdb.le
    have hn := Real.sqrt_nonneg (δ * b)
    have hp := mul_nonneg hn hU
    have ht₀ := mul_nonneg (Real.sqrt_nonneg h) (Real.sqrt_nonneg (2 * b))
    nlinarith [sq_nonneg U]
  nlinarith only [hr, hfrac]

lemma grid_top_bounds {δ Λ : ℝ} (hδ : 0 < δ) (hΛ : δ ≤ Λ) :
    Λ ≤ δ * (4 : ℝ) ^ ⌈Real.log (Λ / δ) / Real.log 4⌉₊ ∧
    δ * (4 : ℝ) ^ ⌈Real.log (Λ / δ) / Real.log 4⌉₊ ≤ 4 * Λ := by
  let M := ⌈Real.log (Λ / δ) / Real.log 4⌉₊
  have hΛ₀ : 0 < Λ := hδ.trans_le hΛ
  have hr : 1 ≤ Λ / δ := (le_div_iff₀ hδ).mpr (by simpa using hΛ)
  have hr₀ : 0 < Λ / δ := div_pos hΛ₀ hδ
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlo : Λ / δ ≤ (4 : ℝ) ^ M := LoraSilverTuning.pow_ceil_log (by norm_num) hr₀
  have hceil : (M : ℝ) < Real.log (Λ / δ) / Real.log 4 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hr) hlog.le)
  have hm := mul_lt_mul_of_pos_right hceil hlog
  have he : (Real.log (Λ / δ) / Real.log 4 + 1) * Real.log 4 =
      Real.log (Λ / δ) + Real.log 4 := by field_simp
  rw [he] at hm
  have hhi : (4 : ℝ) ^ M < 4 * (Λ / δ) := by
    apply (Real.log_lt_log_iff (by positivity : 0 < (4 : ℝ) ^ M)
      (by positivity : 0 < 4 * (Λ / δ))).mp
    rw [Real.log_pow, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr₀.ne']
    linarith
  constructor
  · exact (div_le_iff₀ hδ).mp hlo |>.trans_eq (by ring)
  · have hh := mul_le_mul_of_nonneg_left hhi.le hδ.le
    have he : δ * (4 * (Λ / δ)) = 4 * Λ := by field_simp
    exact hh.trans_eq he

lemma fifth_root_power {t : ℝ} (ht : 0 ≤ t) : (t ^ (1 / 5 : ℝ)) ^ 5 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

open scoped BigOperators

lemma geometric_sum_multiple {q K : ℝ} (hq : 0 ≤ q) (hK : 1 ≤ K)
    (hcoef : q ≤ K * (q - 1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ K * q ^ n := by
  induction n with
  | zero => simpa using hK
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hh := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hq n)
    nlinarith

lemma dyadic_rpow_sum {Q b X p K : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b)
    (hp : 0 ≤ p) (hK : 1 ≤ K) (hcoef : (2 : ℝ) ^ p ≤ K * ((2 : ℝ) ^ p - 1))
    (n : ℕ) (hlast : b * (2 : ℝ) ^ n ≤ X) :
    (∑ i ∈ Finset.range (n + 1), (Q * (b * (2 : ℝ) ^ i)) ^ p) ≤ K * (Q * X) ^ p := by
  have he (i : ℕ) : (Q * (b * (2 : ℝ) ^ i)) ^ p =
      (Q * b) ^ p * ((2 : ℝ) ^ p) ^ i := by
    rw [← mul_assoc, Real.mul_rpow (mul_nonneg hQ hb) (by positivity),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hg := geometric_sum_multiple (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p) hK hcoef n
  have hm := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (mul_nonneg hQ hb) p)
  have hl := Real.rpow_le_rpow (mul_nonneg hQ (mul_nonneg hb (by positivity)))
    (mul_le_mul_of_nonneg_left hlast hQ) hp
  have hscaled := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ K)
  rw [he n] at hscaled
  nlinarith only [hm, hscaled]

lemma dyadic_fifth_coefficient :
    (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 8 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) := by
  have hn := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 5 : ℝ)
  have hp := fifth_root_power (by norm_num : (0 : ℝ) ≤ 2)
  have hlo : (8 / 7 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := by
    by_contra hh
    have hh' := (lt_of_not_ge hh).le
    have hm := pow_le_pow_left₀ hn hh' 5
    norm_num at hm
    nlinarith
  linarith

lemma dyadic_sqrt_coefficient :
    (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 4 * ((2 : ℝ) ^ (1 / 2 : ℝ) - 1) := by
  have hn := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 2 : ℝ)
  have hp : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith

lemma dyadic_fifth_sum {Q b X : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b)
    (n : ℕ) (hlast : b * (2 : ℝ) ^ n ≤ X) :
    (∑ i ∈ Finset.range (n + 1), (Q * (b * (2 : ℝ) ^ i)) ^ (1 / 5 : ℝ)) ≤
      8 * (Q * X) ^ (1 / 5 : ℝ) :=
  dyadic_rpow_sum hQ hb (by norm_num) (by norm_num) dyadic_fifth_coefficient n hlast

lemma dyadic_sqrt_sum {Q b X : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b)
    (n : ℕ) (hlast : b * (2 : ℝ) ^ n ≤ X) :
    (∑ i ∈ Finset.range (n + 1), Real.sqrt (Q * (b * (2 : ℝ) ^ i))) ≤
      4 * Real.sqrt (Q * X) := by
  simp_rw [Real.sqrt_eq_rpow]
  exact dyadic_rpow_sum hQ hb (by norm_num) (by norm_num) dyadic_sqrt_coefficient n hlast

lemma energy_root_constant : 384 * ((8 / 3 : ℝ) ^ (1 / 5 : ℝ)) ≤ 512 := by
  have hn := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 3) (1 / 5 : ℝ)
  have hp := fifth_root_power (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have hu : (8 / 3 : ℝ) ^ (1 / 5 : ℝ) ≤ 4 / 3 := by
    by_contra hh
    have hh' := (lt_of_not_ge hh).le
    have hm := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 3) hh' 5
    norm_num at hm
    nlinarith
  linarith

lemma phase_sum_bound (count : ℕ → ℝ) {δ L D b X M : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hb : 0 ≤ b) (n : ℕ)
    (hlast : b * (2 : ℝ) ^ n ≤ X)
    (hcount : ∀ i ≤ n, count i ≤ 16 * Real.sqrt (δ * (b * (2 : ℝ) ^ i)) +
      48 * (L * D * (b * (2 : ℝ) ^ i)) ^ (1 / 5 : ℝ) + M + 2) :
    (∑ i ∈ Finset.range (n + 1), count i) ≤ 64 * Real.sqrt (δ * X) +
      384 * (L * D * X) ^ (1 / 5 : ℝ) + (M + 2) * (n + 1) := by
  have hs := dyadic_sqrt_sum hδ hb n hlast
  have hf := dyadic_fifth_sum (mul_nonneg hL hD) hb n hlast
  have hh : (∑ i ∈ Finset.range (n + 1), count i) ≤
      ∑ i ∈ Finset.range (n + 1), (16 * Real.sqrt (δ * (b * (2 : ℝ) ^ i)) +
        48 * (L * D * (b * (2 : ℝ) ^ i)) ^ (1 / 5 : ℝ) + M + 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hcount i (by have := Finset.mem_range.mp hi; omega)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hh
  nlinarith only [hh, hs, hf]

lemma log_lower_inverse {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hh
  linarith

lemma log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have hl := log_lower_inverse (by norm_num : (0 : ℝ) < 2)
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  constructor <;> norm_num at * <;> assumption

lemma root_96_bound {K : ℝ} (hK : 0 ≤ K) :
    384 * (96 * K) ^ (1 / 5 : ℝ) ≤ 1000 * K ^ (1 / 5 : ℝ) := by
  have hp := fifth_root_power (by norm_num : (0 : ℝ) ≤ 96)
  have hu : (96 : ℝ) ^ (1 / 5 : ℝ) ≤ 5 / 2 := by
    by_contra hh
    have hm := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) (lt_of_not_ge hh).le 5
    rw [hp] at hm
    norm_num at hm
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 96) hK]
  have hn := Real.rpow_nonneg hK (1 / 5 : ℝ)
  nlinarith [mul_le_mul_of_nonneg_right hu hn]

lemma normalized_count_bound {H K S l T M J : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hl : 1 ≤ l) (hS : 1 ≤ S)
    (hHs : Real.sqrt H ≤ S) (hKs : K ^ (1 / 5 : ℝ) ≤ S)
    (hT : (2 : ℝ) ^ 24 * S * l ^ 2 ≤ T)
    (hMb : M ≤ 32 * l) (hJ : 0 ≤ J) (hJb : J ≤ 128 * l) :
    1 + 64 * Real.sqrt (6 * (T ^ 2 / (2 : ℝ) ^ 24 + 288 * H)) +
      384 * (96 * K) ^ (1 / 5 : ℝ) + (M + 2) * J ≤ T / 8 := by
  have hl0 : 0 ≤ l := by linarith
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hS0 : 0 ≤ S := by linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hroot := Real.sq_sqrt hH
  have hsqrt : Real.sqrt (6 * (T ^ 2 / (2 : ℝ) ^ 24 + 288 * H)) ≤ T / 1024 + 42 * Real.sqrt H := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hcross := mul_nonneg hT0 (Real.sqrt_nonneg H)
    norm_num
    nlinarith [sq_nonneg T]
  have hterm : 64 * Real.sqrt (6 * (T ^ 2 / (2 : ℝ) ^ 24 + 288 * H)) ≤ T / 16 + 2700 * Real.sqrt H := by
    nlinarith [Real.sqrt_nonneg H]
  have hrootterm := root_96_bound hK
  have hM' : M + 2 ≤ 34 * l := by linarith
  have hprod := mul_le_mul hM' hJb hJ (by positivity : 0 ≤ 34 * l)
  have hSl : S ≤ S * l ^ 2 := by nlinarith
  have hlS : l ^ 2 ≤ S * l ^ 2 := by nlinarith [sq_nonneg l]
  have hbase : 1 + 2700 * Real.sqrt H + 1000 * K ^ (1 / 5 : ℝ) + 4352 * l ^ 2 ≤
      8053 * S * l ^ 2 := by nlinarith
  norm_num at hT
  nlinarith

end LongTails.Proofs.SymmetricThirdOrderTuning
