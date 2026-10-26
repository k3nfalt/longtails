import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace LongTails.Proofs.HessianAdaptiveCubicRate

lemma harmonic_bound (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))) ≤ 1 + Real.log N := by
  simpa [harmonic, one_div] using harmonic_le_one_add_log N

lemma harmonic_le_count (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))) ≤ N := by
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun n _ => by
      apply (div_le_one (by positivity)).2
      linarith [Nat.cast_nonneg (α := ℝ) n])
    _ = N := by simp

lemma initial_scale_square (ρ σ D : ℝ) (hD : 0 < D) :
    (2 * ρ + σ / D ^ 2) ^ 2 ≤ 8 * ρ ^ 2 + 2 * σ ^ 2 / D ^ 4 := by
  have he : (σ / D ^ 2) ^ 2 = σ ^ 2 / D ^ 4 := by field_simp
  have hs := sq_nonneg (2 * ρ - σ / D ^ 2)
  calc
    _ ≤ 8 * ρ ^ 2 + 2 * (σ / D ^ 2) ^ 2 := by nlinarith only [hs]
    _ = _ := by rw [he]; ring

lemma successor_sixth (T : ℝ) (hT : 1 ≤ T) : (T + 1) ^ 6 ≤ 64 * T ^ 6 := by
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ T + 1) (by linarith : T + 1 ≤ 2 * T) 6
  nlinarith only [h]

lemma scale_rate_bound (ρ σ σh D K H T : ℝ) (hD : 0 < D) (hT : 1 ≤ T)
    (hH : 0 ≤ H) (hHl : H ≤ 1 + Real.log T) (hHt : H ≤ T)
    (hK : K ≤ (2 * ρ + σ / D ^ 2) ^ 2 * (36 + 20 * H) +
      18 * σ ^ 2 * (T + 1) ^ 6 / D ^ 4 + 8 * σh ^ 2 * T ^ 3 / D ^ 2) :
    K ≤ 448 * ρ ^ 2 * (1 + Real.log T) +
      1264 * σ ^ 2 * T ^ 6 / D ^ 4 + 8 * σh ^ 2 * T ^ 3 / D ^ 2 := by
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have h6 : T ≤ T ^ 6 := by
    calc
      T = T ^ 1 := by ring
      _ ≤ T ^ 6 := pow_le_pow_right₀ hT (by omega)
  have hinit := mul_le_mul_of_nonneg_right (initial_scale_square ρ σ D hD)
    (show 0 ≤ 36 + 20 * H by positivity)
  have hdet : 8 * ρ ^ 2 * (36 + 20 * H) ≤ 448 * ρ ^ 2 * (1 + Real.log T) := by
    have := mul_le_mul_of_nonneg_left hHl (sq_nonneg ρ)
    nlinarith [mul_nonneg (sq_nonneg ρ) hl]
  have hs : 2 * (36 + 20 * H) + 18 * (T + 1) ^ 6 ≤ 1264 * T ^ 6 := by
    nlinarith [successor_sixth T hT]
  have hnoise := mul_le_mul_of_nonneg_left hs (div_nonneg (sq_nonneg σ) (by positivity : 0 ≤ D ^ 4))
  simp only [div_eq_mul_inv] at hK hinit hnoise ⊢
  nlinarith only [hK, hinit, hdet, hnoise]

lemma budget_power_bound (T Q J B : ℝ) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (hB : 1 ≤ B) (hT : B * Q * J ^ 2 ≤ T) (m : ℕ) (hm : 1 ≤ m) :
    B * Q ^ m * J ^ 2 ≤ T ^ m := by
  have hQ0 : 0 ≤ Q := by linarith
  have hJ2 : 1 ≤ J ^ 2 := by nlinarith
  have hTQ : Q ≤ T := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) hQ0]
  have hpow := pow_le_pow_left₀ hQ0 hTQ (m - 1)
  have hmul := mul_le_mul hT hpow (pow_nonneg hQ0 _) (by linarith : 0 ≤ T)
  have hm' : m - 1 + 1 = m := by omega
  calc
    B * Q ^ m * J ^ 2 = (B * Q * J ^ 2) * Q ^ (m - 1) := by
      conv_lhs => rw [← hm', pow_succ]
      ring
    _ ≤ T * T ^ (m - 1) := hmul
    _ = T ^ m := by rw [← pow_succ', hm']

lemma scaled_term_bound (a ε T Q J B : ℝ) (_hε : 0 < ε) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (hB : 1 ≤ B) (hT : B * Q * J ^ 2 ≤ T)
    (m : ℕ) (hm : 1 ≤ m) (ha : a ≤ ε ^ 2 * Q ^ m) :
    a / T ^ m ≤ ε ^ 2 / (B * J ^ 2) := by
  have hp := budget_power_bound T Q J B hQ hJ hB hT m hm
  have hden : 0 < B * J ^ 2 := by positivity
  have ht : 0 < T := by
    have : 0 < B * Q * J ^ 2 := by positivity
    linarith
  apply (div_le_div_iff₀ (pow_pos ht _) hden).2
  have ha' := mul_le_mul_of_nonneg_right ha hden.le
  have hp' := mul_le_mul_of_nonneg_left hp (sq_nonneg ε)
  nlinarith only [ha', hp']

lemma accuracy_from_budget (gap ε ag ah ar T Q J JT : ℝ)
    (hε : 0 < ε) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (hT : 1000000000000000000 * Q * J ^ 2 ≤ T)
    (hg : ag ≤ ε ^ 2 * Q) (hh : ah ≤ ε ^ 2 * Q ^ 4)
    (hr : ar ≤ ε ^ 2 * Q ^ 7) (hJT : 0 ≤ JT) (hJTbound : JT ≤ 166 * J)
    (hgap : gap ^ 2 ≤ 4000000000000 * JT ^ 2 * (ag / T + ah / T ^ 4 + ar / T ^ 7)) :
    gap ≤ ε := by
  have hg' := scaled_term_bound ag ε T Q J 1000000000000000000 hε hQ hJ
    (by norm_num) hT 1 (by omega) (by simpa using hg)
  have hh' := scaled_term_bound ah ε T Q J 1000000000000000000 hε hQ hJ
    (by norm_num) hT 4 (by omega) hh
  have hr' := scaled_term_bound ar ε T Q J 1000000000000000000 hε hQ hJ
    (by norm_num) hT 7 (by omega) hr
  simp only [pow_one] at hg'
  have hs : ag / T + ah / T ^ 4 + ar / T ^ 7 ≤
      3 * (ε ^ 2 / (1000000000000000000 * J ^ 2)) := by linarith
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4000000000000 * JT ^ 2 by positivity)
  have hj := mul_self_le_mul_self hJT hJTbound
  have he := mul_le_mul_of_nonneg_right hj
    (show 0 ≤ 4000000000000 * (3 * (ε ^ 2 / (1000000000000000000 * J ^ 2))) by positivity)
  have hcancel : (166 * J) ^ 2 *
      (4000000000000 * (3 * (ε ^ 2 / (1000000000000000000 * J ^ 2)))) =
      (330672 / 1000000 : ℝ) * ε ^ 2 := by
    field_simp
    ring
  rw [← sq, ← sq, hcancel] at he
  nlinarith only [hgap, hb, he, sq_nonneg gap, hε]

lemma budget_log_bound (A Q J T : ℝ) (hA : 1 ≤ A) (hQ : 1 ≤ Q)
    (hJdef : J = 1 + Real.log (A * Q)) (hT : 0 < T)
    (hTupper : T ≤ 2 * 1000000000000000000 * Q * J ^ 2) :
    1 + Real.log (A * T) ≤ 166 * J := by
  have hAp : 0 < A := by linarith
  have hQp : 0 < Q := by linarith
  have hAQ : 1 ≤ A * Q := by nlinarith
  have hJ : 1 ≤ J := by rw [hJdef]; exact le_add_of_nonneg_right (Real.log_nonneg hAQ)
  have hJp : 0 < J := by linarith
  have hb := Real.log_le_log (mul_pos hAp hT)
    (mul_le_mul_of_nonneg_left hTupper hAp.le)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog10 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
  have hlogJ := Real.log_le_sub_one_of_pos hJp
  have hconst : Real.log (1000000000000000000 : ℝ) = 18 * Real.log 10 := by
    convert Real.log_pow (10 : ℝ) 18 using 1
    norm_num
  rw [Real.log_mul hAp.ne' (by positivity : (2 * 1000000000000000000 * Q * J ^ 2 : ℝ) ≠ 0),
    Real.log_mul (by positivity : (2 * 1000000000000000000 * Q : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (2 * 1000000000000000000 : ℝ) ≠ 0) hQp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (1000000000000000000 : ℝ) ≠ 0),
    Real.log_pow, hconst] at hb
  rw [Real.log_mul hAp.ne' hQp.ne'] at hJdef
  norm_num at hb hlog2 hlog10
  rw [Real.log_mul hAp.ne' hT.ne'] at hb ⊢
  linarith

lemma budget_ceil_bounds (Q J : ℝ) (hQ : 1 ≤ Q) (hJ : 1 ≤ J) :
    let T := ⌈1000000000000000000 * Q * J ^ 2⌉₊
    1 ≤ T ∧ 1000000000000000000 * Q * J ^ 2 ≤ (T : ℝ) ∧
      (T : ℝ) ≤ 2 * 1000000000000000000 * Q * J ^ 2 := by
  dsimp only
  have hlo := Nat.le_ceil (1000000000000000000 * Q * J ^ 2)
  have hbase : 1 ≤ 1000000000000000000 * Q * J ^ 2 := by
    have : 1 ≤ J ^ 2 := by nlinarith
    nlinarith
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 1000000000000000000 * Q * J ^ 2 by positivity)
  refine ⟨?_, hlo, ?_⟩
  · exact_mod_cast hbase.trans hlo
  · linarith

lemma complexity_shape (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let Q := 1 + a ^ 2 + Real.sqrt b + c ^ (2 / 7 : ℝ)
    1 ≤ Q ∧ a ^ 2 ≤ Q ∧ b ^ 2 ≤ Q ^ 4 ∧ c ^ 2 ≤ Q ^ 7 := by
  dsimp only
  have hs := Real.sqrt_nonneg b
  have hr := Real.rpow_nonneg hc (2 / 7 : ℝ)
  have hq : 1 ≤ 1 + a ^ 2 + Real.sqrt b + c ^ (2 / 7 : ℝ) := by nlinarith [sq_nonneg a]
  have hbq : Real.sqrt b ≤ 1 + a ^ 2 + Real.sqrt b + c ^ (2 / 7 : ℝ) := by nlinarith [sq_nonneg a]
  have hcq : c ^ (2 / 7 : ℝ) ≤ 1 + a ^ 2 + Real.sqrt b + c ^ (2 / 7 : ℝ) := by nlinarith [sq_nonneg a]
  have hb4 := pow_le_pow_left₀ hs hbq 4
  have hc7 := pow_le_pow_left₀ hr hcq 7
  have he4 : (Real.sqrt b) ^ 4 = b ^ 2 := by nlinarith [Real.sq_sqrt hb, sq_nonneg (Real.sqrt b ^ 2 - b)]
  have he7 : (c ^ (2 / 7 : ℝ)) ^ 7 = c ^ 2 := by
    rw [← Real.rpow_mul_natCast hc]
    norm_num
  rw [he4] at hb4
  rw [he7] at hc7
  exact ⟨hq, by linarith, hb4, hc7⟩

lemma squared_rate_algebra (gap D K C J T ag ah ar : ℝ)
    (hD : 0 < D) (hT : 0 < T) (hK : 0 ≤ K) (hJ : 1 ≤ J)
    (hg : 0 ≤ ag) (hh : 0 ≤ ah) (hr : 0 ≤ ar)
    (hC : C ≤ 9 * J)
    (hscale : D ^ 6 * K ≤ T ^ 7 * (448 * J * ar + 1264 * ag + 8 * ah))
    (hgap : gap ^ 2 * T ^ 7 ≤ 6600 ^ 2 * D ^ 6 * K * C) :
    gap ^ 2 ≤ 4000000000000 * J ^ 2 * (ag + ah + ar) := by
  have hc := mul_le_mul_of_nonneg_left hC
    (show 0 ≤ 6600 ^ 2 * D ^ 6 * K by positivity)
  have hs := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 6600 ^ 2 * (9 * J) by positivity)
  have hag : ag ≤ J * ag := by nlinarith
  have hah : ah ≤ J * ah := by nlinarith
  have hsum : 448 * J * ar + 1264 * ag + 8 * ah ≤ 1264 * J * (ag + ah + ar) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ J) hr]
  have hm := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 6600 ^ 2 * (9 * J) * T ^ 7 by positivity)
  have hnum : gap ^ 2 * T ^ 7 ≤ 495538560000 * J ^ 2 * (ag + ah + ar) * T ^ 7 := by
    nlinarith only [hgap, hc, hs, hm]
  have hb := (mul_le_mul_iff_left₀ (pow_pos hT 7)).mp hnum
  have hn : 0 ≤ J ^ 2 * (ag + ah + ar) := by positivity
  nlinarith only [hb, hn]

lemma scale_rate_rescale (D T K ρ σ σh J : ℝ) (hD : 0 < D) (hT : 0 < T)
    (hJ : 1 + Real.log T ≤ J)
    (hK : K ≤ 448 * ρ ^ 2 * (1 + Real.log T) +
      1264 * σ ^ 2 * T ^ 6 / D ^ 4 + 8 * σh ^ 2 * T ^ 3 / D ^ 2) :
    D ^ 6 * K ≤ T ^ 7 * (448 * J * (ρ ^ 2 * D ^ 6 / T ^ 7) +
      1264 * (σ ^ 2 * D ^ 2 / T) + 8 * (σh ^ 2 * D ^ 4 / T ^ 4)) := by
  have hj := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 448 * ρ ^ 2 by positivity)
  have hk' : K ≤ 448 * ρ ^ 2 * J +
      1264 * σ ^ 2 * T ^ 6 / D ^ 4 + 8 * σh ^ 2 * T ^ 3 / D ^ 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hk' (show 0 ≤ D ^ 6 by positivity)
  have he : D ^ 6 * (448 * ρ ^ 2 * J + 1264 * σ ^ 2 * T ^ 6 / D ^ 4 +
      8 * σh ^ 2 * T ^ 3 / D ^ 2) = T ^ 7 * (448 * J * (ρ ^ 2 * D ^ 6 / T ^ 7) +
      1264 * (σ ^ 2 * D ^ 2 / T) + 8 * (σh ^ 2 * D ^ 4 / T ^ 4)) := by
    field_simp
  rw [← he]
  exact hm

lemma normalized_scale_polynomial (S H T r : ℝ) (hT : 1 ≤ T) (hr : 0 ≤ r)
    (hH : H ≤ T) (hS : S ≤ 36 + 20 * H + 18 * (T + 1) ^ 6 + 2 * r ^ 2 * T ^ 3) :
    S ≤ 4096 * (1 + r) ^ 2 * T ^ 6 := by
  have hT6 : T ≤ T ^ 6 := by simpa using pow_le_pow_right₀ hT (show 1 ≤ 6 by omega)
  have hT36 := pow_le_pow_right₀ hT (show 3 ≤ 6 by omega)
  have h1 : 1 ≤ T ^ 6 := one_le_pow₀ hT
  have hrT := mul_le_mul_of_nonneg_left hT36 (show 0 ≤ 2 * r ^ 2 by positivity)
  have hp : S ≤ (1208 + 2 * r ^ 2) * T ^ 6 := by
    nlinarith [successor_sixth T hT]
  have hc : 1208 + 2 * r ^ 2 ≤ 4096 * (1 + r) ^ 2 := by nlinarith [sq_nonneg r]
  exact hp.trans (mul_le_mul_of_nonneg_right hc (by positivity))

lemma normalization_log_factor (S L H T r : ℝ) (hS : 0 < S) (hT : 1 ≤ T) (hr : 0 ≤ r)
    (hH : H ≤ 1 + Real.log T) (hL : L ≤ (1 / 2) * Real.log S)
    (hbound : S ≤ 4096 * (1 + r) ^ 2 * T ^ 6) :
    1 + L + H ≤ 9 * (1 + Real.log ((1 + r) * T)) := by
  have hTp : 0 < T := by linarith
  have hA : 0 < 1 + r := by positivity
  have hlT := Real.log_nonneg hT
  have hlA := Real.log_nonneg (show 1 ≤ 1 + r by linarith)
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hb := Real.log_le_log hS hbound
  have he : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 12 using 1
    norm_num
  rw [Real.log_mul (by positivity : (4096 * (1 + r) ^ 2 : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (4096 : ℝ) ≠ 0) (by positivity),
    Real.log_pow, Real.log_pow, he] at hb
  rw [Real.log_mul hA.ne' hTp.ne']
  norm_num at hb hl2
  linarith

lemma normalized_scale_ratio (κ K a b r H T : ℝ) (hκ : 0 < κ) (hT : 0 ≤ T)
    (ha : a ≤ κ ^ 2) (hb : b ≤ κ ^ 2 * r ^ 2 / 4)
    (hK : K ≤ κ ^ 2 * (36 + 20 * H) + 18 * a * (T + 1) ^ 6 + 8 * b * T ^ 3) :
    K / κ ^ 2 ≤ 36 + 20 * H + 18 * (T + 1) ^ 6 + 2 * r ^ 2 * T ^ 3 := by
  apply (div_le_iff₀ (sq_pos_of_pos hκ)).2
  have hag := mul_le_mul_of_nonneg_right ha (show 0 ≤ 18 * (T + 1) ^ 6 by positivity)
  have hbh := mul_le_mul_of_nonneg_right hb (show 0 ≤ 8 * T ^ 3 by positivity)
  nlinarith only [hK, hag, hbh]

lemma noise_scale_ratios (ρ σ σh D : ℝ) (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hD : 0 < D) :
    let κ := 2 * ρ + σ / D ^ 2
    σ ^ 2 / D ^ 4 ≤ κ ^ 2 ∧
      σh ^ 2 / D ^ 2 ≤ κ ^ 2 * (σh / (ρ * D)) ^ 2 / 4 := by
  dsimp only
  have hq : 0 ≤ σ / D ^ 2 := by positivity
  have hg := pow_le_pow_left₀ hq (show σ / D ^ 2 ≤ 2 * ρ + σ / D ^ 2 by linarith) 2
  have hh := pow_le_pow_left₀ (show 0 ≤ 2 * ρ by positivity)
    (show 2 * ρ ≤ 2 * ρ + σ / D ^ 2 by linarith) 2
  have hgEq : (σ / D ^ 2) ^ 2 = σ ^ 2 / D ^ 4 := by field_simp
  rw [hgEq] at hg
  refine ⟨hg, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (σh / (ρ * D)))
  have he : (2 * ρ) ^ 2 * (σh / (ρ * D)) ^ 2 = 4 * (σh ^ 2 / D ^ 2) := by
    field_simp
    ring
  rw [he] at hm
  linarith

lemma complexity_numerators (ρ σ σh D ε : ℝ) (hρ : 0 ≤ ρ) (hσh : 0 ≤ σh)
    (hD : 0 < D) (hε : 0 < ε) :
    let Q := 1 + (σ * D / ε) ^ 2 + Real.sqrt (σh * D ^ 2 / ε) +
      (ρ * D ^ 3 / ε) ^ (2 / 7 : ℝ)
    1 ≤ Q ∧ σ ^ 2 * D ^ 2 ≤ ε ^ 2 * Q ∧
      σh ^ 2 * D ^ 4 ≤ ε ^ 2 * Q ^ 4 ∧ ρ ^ 2 * D ^ 6 ≤ ε ^ 2 * Q ^ 7 := by
  dsimp only
  have hshape := complexity_shape (σ * D / ε) (σh * D ^ 2 / ε) (ρ * D ^ 3 / ε)
    (by positivity) (by positivity)
  refine ⟨hshape.1, ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hshape.2.1 (sq_nonneg ε)
    have he : ε ^ 2 * (σ * D / ε) ^ 2 = σ ^ 2 * D ^ 2 := by field_simp
    rwa [he] at h
  · have h := mul_le_mul_of_nonneg_left hshape.2.2.1 (sq_nonneg ε)
    have he : ε ^ 2 * (σh * D ^ 2 / ε) ^ 2 = σh ^ 2 * D ^ 4 := by field_simp
    rwa [he] at h
  · have h := mul_le_mul_of_nonneg_left hshape.2.2.2 (sq_nonneg ε)
    have he : ε ^ 2 * (ρ * D ^ 3 / ε) ^ 2 = ρ ^ 2 * D ^ 6 := by field_simp
    rwa [he] at h

lemma accuracy_at_shape_budget (ρ σ σh D ε gap : ℝ) (hρ : 0 < ρ) (hσh : 0 ≤ σh)
    (hD : 0 < D) (hε : 0 < ε) :
    let Q := 1 + (σ * D / ε) ^ 2 + Real.sqrt (σh * D ^ 2 / ε) +
      (ρ * D ^ 3 / ε) ^ (2 / 7 : ℝ)
    let J := 1 + Real.log ((1 + σh / (ρ * D)) * Q)
    let N := ⌈1000000000000000000 * Q * J ^ 2⌉₊
    1 ≤ N ∧ (gap ^ 2 ≤ 4000000000000 *
      (1 + Real.log ((1 + σh / (ρ * D)) * N)) ^ 2 *
        (σ ^ 2 * D ^ 2 / N + σh ^ 2 * D ^ 4 / (N : ℝ) ^ 4 +
          ρ ^ 2 * D ^ 6 / (N : ℝ) ^ 7) → gap ≤ ε) := by
  dsimp only
  let Q := 1 + (σ * D / ε) ^ 2 + Real.sqrt (σh * D ^ 2 / ε) + (ρ * D ^ 3 / ε) ^ (2 / 7 : ℝ)
  let A := 1 + σh / (ρ * D)
  let J := 1 + Real.log (A * Q)
  let N := ⌈1000000000000000000 * Q * J ^ 2⌉₊
  have hshape := complexity_numerators ρ σ σh D ε hρ.le hσh hD hε
  have hQ : 1 ≤ Q := hshape.1
  have hA : 1 ≤ A := by
    dsimp [A]
    have : 0 ≤ σh / (ρ * D) := by positivity
    linarith
  have hJ : 1 ≤ J := by
    dsimp [J]
    apply le_add_of_nonneg_right
    apply Real.log_nonneg
    nlinarith
  have hN := budget_ceil_bounds Q J hQ hJ
  refine ⟨hN.1, ?_⟩
  intro hgap
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN.1
  have hNp : 0 < (N : ℝ) := by linarith
  have hJT : 0 ≤ 1 + Real.log (A * N) := by
    have : 1 ≤ A * N := by nlinarith
    have := Real.log_nonneg this
    linarith
  exact accuracy_from_budget gap ε (σ ^ 2 * D ^ 2) (σh ^ 2 * D ^ 4) (ρ ^ 2 * D ^ 6)
    N Q J (1 + Real.log (A * N)) hε hQ hJ hN.2.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2
    hJT (budget_log_bound A Q J N hA hQ rfl hNp hN.2.2) hgap

end LongTails.Proofs.HessianAdaptiveCubicRate
