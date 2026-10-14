import LongTails.Proofs.AdaptiveEntropicTuning

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma geometry_le_joint_log (q : Public) : geometry q ≤ Real.log (2 * (q.d : ℝ)) := by
  have hd : (2 : ℝ) ≤ q.d := by exact_mod_cast q.hd
  have hd0 : 0 < (q.d : ℝ) := by linarith only [hd]
  have hlog : Real.log 2 ≤ Real.log (q.d : ℝ) := Real.log_le_log (by norm_num) hd
  have h2 := Real.log_two_gt_d9
  have he : Real.log (2 * (q.d : ℝ)) = Real.log 2 + Real.log (q.d : ℝ) :=
    Real.log_mul (by norm_num) hd0.ne'
  unfold geometry
  rw [he]
  apply max_le
  · linarith only [hlog, h2]
  · linarith only [h2]

lemma trimCount_upper (q : Public) (hH : 2 ≤ confidence q) :
    (trimCount q : ℝ) ≤ 128 * (Real.log (2 * (q.d : ℝ)) + confidence q) := by
  have hD := geometry_pos q
  have hDH := geometry_le_joint_log q
  have hJ : 1 ≤ Real.log (2 * (q.d : ℝ)) + confidence q := by
    have hD1 : 1 ≤ geometry q := le_max_left _ _
    linarith only [hDH, hD1, hH]
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 64 * (geometry q + confidence q) by linarith only [hD, hH])
  unfold trimCount
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith only [hJ]
  · linarith only [hceil, hDH, hJ]

lemma window_upper (q : Public) (hH : 2 ≤ confidence q) (T : ℕ) :
    (window q T : ℝ) ≤ 32 * (confidence q + Real.log ((T : ℝ) + 1)) := by
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 16 * (confidence q + Real.log ((T : ℝ) + 1)) by linarith only [hH, hlog])
  change (⌈16 * (confidence q + Real.log ((T : ℝ) + 1))⌉₊ : ℝ) ≤ _
  linarith only [hceil, hH, hlog]

lemma deterministic_rate_coarse (q : Public) (hL : 0 ≤ q.L)
    (hH : 2 ≤ confidence q) (T : ℕ) :
    16777216 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2) ≤
      68719476736 * q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) *
        (confidence q + Real.log ((T : ℝ) + 1)) / (T : ℝ) ^ 2 := by
  have hK := trimCount_upper q hH
  have hw := window_upper q hH T
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
  have hS : 0 ≤ confidence q + Real.log ((T : ℝ) + 1) := by linarith only [hH, hlog]
  have h1 := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ q.L * (trimCount q : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ 32 * q.L * (confidence q + Real.log ((T : ℝ) + 1)) by positivity)
  rw [show 16777216 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2) =
    (16777216 * (q.L * trimCount q * window q T)) / (T : ℝ) ^ 2 by ring]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (T : ℝ))
  nlinarith only [h1, h2]

lemma logarithmic_ratio_mono {S T H : ℝ} (hS : 1 ≤ S) (hST : S ≤ T) (hH : 1 ≤ H) :
    (H + Real.log (T + 1)) / T ^ 2 ≤ (H + Real.log (S + 1)) / S ^ 2 := by
  have hS0 : 0 < S := by linarith only [hS]
  have hT0 : 0 < T := hS0.trans_le hST
  have hSp : 0 < S + 1 := by positivity
  have hTp : 0 < T + 1 := by positivity
  have hlogST : Real.log (S + 1) ≤ Real.log (T + 1) :=
    Real.log_le_log hSp (by linarith only [hST])
  have hlogS : 0 ≤ Real.log (S + 1) := Real.log_nonneg (by linarith only [hS])
  have hR : 1 ≤ H + Real.log (S + 1) := by linarith only [hH, hlogS]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hTp hSp)
  rw [Real.log_div hTp.ne' hSp.ne'] at hlog
  have hlog' : (Real.log (T + 1) - Real.log (S + 1)) * (S + 1) ≤ T - S := by
    have he : (T + 1) / (S + 1) - 1 = (T - S) / (S + 1) := by field_simp; ring
    rw [he] at hlog
    exact (le_div_iff₀ hSp).mp hlog
  have hlog'' : (Real.log (T + 1) - Real.log (S + 1)) * S ≤ T - S := by
    nlinarith only [hlog', hlogST]
  have hdiff : T - S ≤ (H + Real.log (S + 1)) * (T - S) := by
    have hm := mul_le_mul_of_nonneg_right hR (show 0 ≤ T - S by linarith only [hST])
    simpa only [one_mul] using hm
  have hlinear : (H + Real.log (T + 1)) * S ≤ (H + Real.log (S + 1)) * T := by
    nlinarith only [hlog'', hdiff]
  have hsq : (H + Real.log (T + 1)) * S ^ 2 ≤ (H + Real.log (S + 1)) * T ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hlinear hS0.le
    have h2 := mul_le_mul_of_nonneg_left hST
      (show 0 ≤ (H + Real.log (S + 1)) * T by positivity)
    nlinarith only [h1, h2]
  exact (div_le_div_iff₀ (sq_pos_of_pos hT0) (sq_pos_of_pos hS0)).mpr hsq

lemma stochastic_accuracy_budget {T K σ ε p : ℝ} (hT : 0 < T) (hK : 0 < K)
    (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p)
    (hbudget : K * (33554432 * σ / ε) ^ (p / (p - 1)) ≤ T) :
    16777216 * σ * (K / T) ^ ((p - 1) / p) ≤ ε / 2 := by
  by_cases hσ0 : σ = 0
  · simp only [hσ0, mul_zero, zero_mul]
    positivity
  have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  have hp0 : 0 < p := by linarith only [hp]
  have hm : 0 < p - 1 := by linarith only [hp]
  let b := 33554432 * σ / ε
  have hb : 0 < b := by dsimp [b]; positivity
  have hbp : 0 < b ^ (p / (p - 1)) := Real.rpow_pos_of_pos hb _
  have hr : K / T ≤ 1 / b ^ (p / (p - 1)) := by
    apply (div_le_iff₀ hT).mpr
    have h := (le_div_iff₀ hbp).mpr hbudget
    convert h using 1; ring
  have hpow := Real.rpow_le_rpow (div_nonneg hK.le hT.le) hr (div_pos hm hp0).le
  have he : (1 / b ^ (p / (p - 1))) ^ ((p - 1) / p) = 1 / b := by
    rw [one_div, Real.inv_rpow (Real.rpow_nonneg hb.le _), ← Real.rpow_mul hb.le]
    have hq : p / (p - 1) * ((p - 1) / p) = 1 := by field_simp
    rw [hq, Real.rpow_one]
    simp only [one_div]
  rw [he] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 16777216 * σ by positivity)
  have hc : 16777216 * σ * (1 / b) = ε / 2 := by dsimp [b]; field_simp; ring
  exact h.trans_eq hc

lemma stochastic_budget_dominates {J K σ ε p : ℝ} (hJ : 0 ≤ J)
    (hK : K ≤ 128 * J) (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) :
    K * (33554432 * σ / ε) ^ (p / (p - 1)) ≤
      2 * J * (274877906944 * σ / ε) ^ (p / (p - 1)) := by
  have hm : 0 < p - 1 := by linarith only [hp]
  have hq : 1 ≤ p / (p - 1) := (le_div_iff₀ hm).mpr (by linarith)
  have hb : 0 ≤ 33554432 * σ / ε := by positivity
  have hscale : (8192 : ℝ) ≤ (8192 : ℝ) ^ (p / (p - 1)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8192) hq
  have hfactor : K ≤ 2 * J * (8192 : ℝ) ^ (p / (p - 1)) := by
    have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * J by positivity)
    nlinarith only [hK, h, hJ]
  have h := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hb (p / (p - 1)))
  have he : 274877906944 * σ / ε = 8192 * (33554432 * σ / ε) := by ring
  rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8192) hb]
  convert h using 1; ring

lemma deterministic_reference_log {s H : ℝ} (hs : 0 ≤ s) (hH : 2 ≤ H) :
    H + Real.log (max 1 (33554432 * Real.sqrt (s * (H + Real.log (2 + s)))) + 1) ≤
      16 * (H + Real.log (2 + s)) := by
  let B := H + Real.log (2 + s)
  let M := (2 + s) * B
  have hlog : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith only [hs])
  have hB : 2 ≤ B := by dsimp [B]; linarith only [hH, hlog]
  have hB0 : 0 < B := by linarith only [hB]
  have hM : 2 ≤ M := by dsimp [M]; nlinarith only [hs, hB]
  have hsq : s * B ≤ M ^ 2 := by
    have h1 : s ≤ (2 + s) ^ 2 := by nlinarith only [hs]
    have h2 : B ≤ B ^ 2 := by nlinarith only [hB]
    have h3 := mul_le_mul_of_nonneg_right h1 hB0.le
    have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (2 + s))
    dsimp [M]
    nlinarith only [h3, h4]
  have hr : Real.sqrt (s * B) ≤ M := Real.sqrt_le_iff.mpr ⟨by linarith only [hM], hsq⟩
  have hupper : max 1 (33554432 * Real.sqrt (s * B)) + 1 ≤ 67108864 * M := by
    rcases le_total (33554432 * Real.sqrt (s * B)) 1 with h | h
    · rw [max_eq_left h]
      linarith only [hM]
    · rw [max_eq_right h]
      linarith only [hr, hM]
  have hl := Real.log_le_log
    (show 0 < max 1 (33554432 * Real.sqrt (s * B)) + 1 by positivity) hupper
  have he : Real.log (67108864 * M) = 26 * Real.log 2 + Real.log (2 + s) + Real.log B := by
    dsimp [M]
    rw [Real.log_mul (by norm_num) (by positivity : (2 + s) * B ≠ 0),
      Real.log_mul (by positivity : 2 + s ≠ 0) hB0.ne',
      show (67108864 : ℝ) = (2 : ℝ) ^ 26 by norm_num, Real.log_pow]
    ring
  rw [he] at hl
  have hlB := Real.log_le_sub_one_of_pos hB0
  have h2 := Real.log_two_lt_d9
  change H + Real.log (max 1 (33554432 * Real.sqrt (s * B)) + 1) ≤ 16 * B
  have hBeq : B = H + Real.log (2 + s) := rfl
  linarith only [hl, hlB, h2, hB, hH, hBeq]

lemma deterministic_sqrt_budget {s H T : ℝ} (hs : 0 ≤ s) (hH : 2 ≤ H)
    (hbudget : max 1 (33554432 * Real.sqrt (s * (H + Real.log (2 + s)))) ≤ T) :
    68719476736 * s * (H + Real.log (T + 1)) / T ^ 2 ≤ 1 / 2 := by
  let B := H + Real.log (2 + s)
  let S := max 1 (33554432 * Real.sqrt (s * B))
  have hlog : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith only [hs])
  have hB : 0 ≤ B := by dsimp [B]; linarith only [hH, hlog]
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 < S := by linarith only [hS]
  have hr : 0 ≤ 33554432 * Real.sqrt (s * B) := by positivity
  have hsq := pow_le_pow_left₀ hr (show 33554432 * Real.sqrt (s * B) ≤ S from le_max_right _ _) 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hs hB)] at hsq
  norm_num at hsq
  have hmass : 1125899906842624 * s * B ≤ S ^ 2 := by nlinarith only [hsq]
  have hl := deterministic_reference_log hs hH
  change H + Real.log (S + 1) ≤ 16 * B at hl
  have hn := mul_le_mul_of_nonneg_left hl (show 0 ≤ 68719476736 * s by positivity)
  have hnum : 68719476736 * s * (H + Real.log (S + 1)) ≤ S ^ 2 / 2 := by
    nlinarith only [hn, hmass, mul_nonneg hs hB]
  have hratio : 68719476736 * s * ((H + Real.log (S + 1)) / S ^ 2) ≤ 1 / 2 := by
    rw [show 68719476736 * s * ((H + Real.log (S + 1)) / S ^ 2) =
      (68719476736 * s * (H + Real.log (S + 1))) / S ^ 2 by ring]
    exact (div_le_iff₀ (sq_pos_of_pos hS0)).mpr (by linarith only [hnum])
  have hm := logarithmic_ratio_mono hS hbudget (by linarith : 1 ≤ H)
  have hf := mul_le_mul_of_nonneg_left hm (show 0 ≤ 68719476736 * s by positivity)
  calc
    _ = 68719476736 * s * ((H + Real.log (T + 1)) / T ^ 2) := by ring
    _ ≤ _ := hf
    _ ≤ _ := hratio

lemma deterministic_accuracy_budget (q : Public) (hL : 0 ≤ q.L) (hH : 2 ≤ confidence q)
    {ε T : ℝ} (hε : 0 < ε) (N : ℕ) (hT : T = (N : ℝ))
    (hbudget : max 1 (33554432 * Real.sqrt
      ((q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε) *
        (confidence q + Real.log (2 + q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε)))) ≤ T) :
    16777216 * (q.L * trimCount q * window q N / T ^ 2) ≤ ε / 2 := by
  let J := Real.log (2 * (q.d : ℝ)) + confidence q
  let s := q.L * J / ε
  have hJ : 0 ≤ J := by
    have hgeom := geometry_le_joint_log q
    have hD := geometry_pos q
    dsimp [J]
    linarith only [hgeom, hD, hH]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have h := deterministic_sqrt_budget hs hH hbudget
  have hh := mul_le_mul_of_nonneg_left h hε.le
  have hc := deterministic_rate_coarse q hL hH N
  rw [← hT] at hc
  calc
    _ ≤ _ := hc
    _ = ε * (68719476736 * s * (confidence q + Real.log (T + 1)) / T ^ 2) := by
      dsimp [s, J]
      field_simp
    _ ≤ ε * (1 / 2) := hh
    _ = _ := by ring

lemma rounded_call_budget {H u v : ℝ} (hH : 2 ≤ H) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (m N : ℕ) (hm : (m : ℝ) ≤ 64 * H + 1)
    (hN : 256 * H + 2 * u + 2 * v ≤ (N : ℝ)) :
    1 ≤ (N - m) / 2 ∧ u ≤ (((N - m) / 2 : ℕ) : ℝ) ∧
      v ≤ (((N - m) / 2 : ℕ) : ℝ) := by
  have hmN : m ≤ N := by
    have h : (m : ℝ) ≤ N := by linarith only [hm, hN, hH, hu, hv]
    exact_mod_cast h
  have hdiv : N ≤ m + 2 * ((N - m) / 2) + 1 := by omega
  have hdivR : (N : ℝ) ≤ m + 2 * (((N - m) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdiv
  constructor
  · have h : (1 : ℝ) ≤ (((N - m) / 2 : ℕ) : ℝ) := by
      linarith only [hm, hN, hH, hu, hv, hdivR]
    exact_mod_cast h
  constructor <;> linarith only [hm, hN, hH, hu, hv, hdivR]

lemma budget_accuracy (q : Public) (hL : 0 < q.L) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    {σ ε p : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (N : ℕ)
    (hN : 256 * confidence q + 67108864 * Real.sqrt
      ((q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε) *
        (confidence q + Real.log (2 + q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε))) +
      4 * (Real.log (2 * (q.d : ℝ)) + confidence q) *
        (274877906944 * σ / ε) ^ (p / (p - 1)) ≤ (N : ℝ)) :
    let T := (N - preload q) / 2
    0 < T ∧ 16777216 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2 +
      σ * ((trimCount q : ℝ) / T) ^ ((p - 1) / p)) ≤ ε := by
  intro T
  have hH := confidence_ge_two q hδ hδ1
  let J := Real.log (2 * (q.d : ℝ)) + confidence q
  let s := q.L * J / ε
  let u := 33554432 * Real.sqrt (s * (confidence q + Real.log (2 + s)))
  let v := 2 * J * (274877906944 * σ / ε) ^ (p / (p - 1))
  have hJ : 0 ≤ J := by
    have hd := geometry_le_joint_log q
    have hD := geometry_pos q
    dsimp [J]
    linarith only [hd, hD, hH]
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpre : (preload q : ℝ) ≤ 64 * confidence q + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 64 * confidence q by linarith only [hH])).le
  have hn : 256 * confidence q + 2 * u + 2 * v ≤ (N : ℝ) := by
    convert hN using 1; dsimp [u, v, s, J]; ring
  have ht := rounded_call_budget hH hu hv (preload q) N hpre hn
  have hT : 0 < T := by dsimp [T]; omega
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast ht.1
  have hTu : max 1 u ≤ (T : ℝ) := max_le hTone ht.2.1
  have hdet := deterministic_accuracy_budget q hL.le hH hε T rfl hTu
  have hK : 0 < (trimCount q : ℝ) := by
    have hk : 1 ≤ trimCount q := le_max_left _ _
    exact_mod_cast (show 0 < trimCount q by omega)
  have hdom := stochastic_budget_dominates hJ (trimCount_upper q hH) hσ hε hp
  have hnoise := stochastic_accuracy_budget hTr hK hσ hε hp (hdom.trans ht.2.2)
  constructor
  · exact hT
  · nlinarith only [hdet, hnoise]

end OracleTemplate.AdaptiveHeavyTailSimplex
