import LongTails.Proofs.ClippedExtragradientTuning

open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

lemma dyadic_count_upper {u : ℝ} (hu : 0 ≤ u) :
    (⌈Real.log (1 + 32 * u) / Real.log 2⌉₊ : ℝ) + 1 ≤
      8 * (1 + Real.log (2 + u)) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2p : 0 < Real.log 2 := by linarith
  have hlog : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    have he : (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  have hb : Real.log (1 + 32 * u) ≤ 5 * Real.log 2 + Real.log (2 + u) := by
    have hh := Real.log_le_log (show 0 < 1 + 32 * u by positivity)
      (show 1 + 32 * u ≤ 32 * (2 + u) by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), h32] at hh
    exact hh
  have hq : Real.log (1 + 32 * u) / Real.log 2 ≤ 5 + 2 * Real.log (2 + u) := by
    rw [div_le_iff₀ h2p]
    nlinarith
  have hn := (Nat.ceil_lt_add_one (div_nonneg
    (Real.log_nonneg (by linarith : 1 ≤ 1 + 32 * u)) h2p.le)).le
  linarith

lemma stageCount_upper (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 ≤ p.R) (hε : 0 < p.ε) :
    (stageCount p : ℝ) ≤ 8 * (1 + Real.log (2 + p.L0 * p.R / p.ε + p.L1 * p.R)) := by
  have hh := dyadic_count_upper (show 0 ≤ p.L0 * p.R / p.ε + p.L1 * p.R by positivity)
  unfold stageCount
  push_cast
  simpa only [add_assoc] using hh

lemma dyadic_count_covers {u : ℝ} (hu : 0 ≤ u) :
    1 + 32 * u ≤ (2 : ℝ) ^ ⌈Real.log (1 + 32 * u) / Real.log 2⌉₊ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ h2).mp (Nat.le_ceil (Real.log (1 + 32 * u) / Real.log 2))
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log (by positivity : 0 < 1 + 32 * u),
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact he

lemma final_radius_scale (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) :
    (p.L0 + p.L1 * p.ε) * radius p (stageCount p - 1) ≤ p.ε / 32 := by
  have hh := dyadic_count_covers (show 0 ≤ p.L0 * p.R / p.ε + p.L1 * p.R by positivity)
  have hs : stageCount p - 1 = ⌈Real.log (1 + 32 * (p.L0 * p.R / p.ε + p.L1 * p.R)) / Real.log 2⌉₊ := by
    unfold stageCount
    omega
  unfold radius
  rw [hs]
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_left hh hε.le
  have he : p.ε * (1 + 32 * (p.L0 * p.R / p.ε + p.L1 * p.R)) =
      p.ε + 32 * ((p.L0 + p.L1 * p.ε) * p.R) := by field_simp
  rw [he] at hm
  linarith

lemma repetitions_confidence (p : Tuning) (hδ : 0 < p.δ) :
    (1 / 2 : ℝ) ^ repetitions p ≤ p.δ / stageCount p := by
  have ht : (0 : ℝ) < stageCount p := Nat.cast_pos.mpr (stageCount_pos p)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log ((stageCount p : ℝ) / p.δ) / Real.log 2)
  have hb : Real.log ((stageCount p : ℝ) / p.δ) / Real.log 2 ≤ (repetitions p : ℝ) := by
    unfold repetitions
    push_cast
    linarith
  have hh := (div_le_iff₀ h2).mp hb
  apply (Real.log_le_log_iff (by positivity) (by positivity : 0 < p.δ / stageCount p)).mp
  rw [Real.log_pow, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one, Real.log_div hδ.ne' ht.ne']
  rw [Real.log_div ht.ne' hδ.ne'] at hh
  linarith

lemma repetitions_upper (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 ≤ p.R) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) :
    (repetitions p : ℝ) ≤
      8 * (1 + Real.log ((2 + p.L0 * p.R / p.ε + p.L1 * p.R) / p.δ)) := by
  let z := 2 + p.L0 * p.R / p.ε + p.L1 * p.R
  have hz : 2 ≤ z := by
    have ha : 0 ≤ p.L0 * p.R / p.ε := by positivity
    have hb : 0 ≤ p.L1 * p.R := by positivity
    dsimp [z]
    linarith
  have hz0 : 0 < z := by linarith
  have ht : (1 : ℝ) ≤ stageCount p := by exact_mod_cast (Nat.succ_le_of_lt (stageCount_pos p))
  have ht0 : (0 : ℝ) < stageCount p := by linarith
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2p : 0 < Real.log 2 := by linarith
  have hlog : 0 ≤ Real.log (z / p.δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hTz : (stageCount p : ℝ) ≤ 8 * z := by
    have hh := stageCount_upper p h0 h1 hR hε
    have hl := Real.log_le_sub_one_of_pos hz0
    change (stageCount p : ℝ) ≤ 8 * (1 + Real.log z) at hh
    linarith
  have hlogT : Real.log ((stageCount p : ℝ) / p.δ) ≤
      3 * Real.log 2 + Real.log (z / p.δ) := by
    have hh := Real.log_le_log (div_pos ht0 hδ)
      (div_le_div_of_nonneg_right hTz hδ.le)
    have he : 8 * z / p.δ = 8 * (z / p.δ) := by ring
    rw [he, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity)] at hh
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      have he : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      rw [he, Real.log_pow]
      norm_num
    rw [h8] at hh
    exact hh
  have hq : Real.log ((stageCount p : ℝ) / p.δ) / Real.log 2 ≤
      3 + 2 * Real.log (z / p.δ) := by
    rw [div_le_iff₀ h2p]
    nlinarith
  have hq0 : 0 ≤ Real.log ((stageCount p : ℝ) / p.δ) / Real.log 2 := by
    apply div_nonneg _ h2p.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hceil := (Nat.ceil_lt_add_one hq0).le
  unfold repetitions
  push_cast
  change _ ≤ 8 * (1 + Real.log (z / p.δ))
  linarith

lemma remainingCalls_upper (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s k : ℕ) :
    (remainingCalls p s k : ℝ) ≤ (k : ℝ) * 2 ^ 46 * (repetitions p : ℝ) *
      (stageCount p : ℝ) ^ 2 *
      (1 + p.L0 * p.R / p.ε + (p.L1 * p.R) ^ 2 + p.σ ^ 2 / p.ε ^ 2) := by
  induction k generalizing s with
  | zero => simp [remainingCalls]
  | succ k ih =>
      have hs := stageCalls_upper p h0 h1 hR hε s
      have hr := stage_ratio_uniform p h0 h1 hR hε s
      have hm := mul_le_mul_of_nonneg_left hr
        (show 0 ≤ 2 ^ 39 * (repetitions p : ℝ) by positivity)
      have hi := ih (s + 1)
      rw [remainingCalls]
      push_cast
      nlinarith

lemma total_calls_bound (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) :
    (remainingCalls p 0 (stageCount p) : ℝ) ≤
      2 ^ 60 * (1 + p.L0 * p.R / p.ε + (p.L1 * p.R) ^ 2 + p.σ ^ 2 / p.ε ^ 2) *
        (1 + Real.log (2 + p.L0 * p.R / p.ε + p.L1 * p.R)) ^ 3 *
        (1 + Real.log ((2 + p.L0 * p.R / p.ε + p.L1 * p.R) / p.δ)) := by
  let Q := 1 + p.L0 * p.R / p.ε + (p.L1 * p.R) ^ 2 + p.σ ^ 2 / p.ε ^ 2
  let l := 1 + Real.log (2 + p.L0 * p.R / p.ε + p.L1 * p.R)
  let b := 1 + Real.log ((2 + p.L0 * p.R / p.ε + p.L1 * p.R) / p.δ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have ha : 0 ≤ p.L0 * p.R / p.ε := by positivity
  have hq : 0 ≤ p.L1 * p.R := by positivity
  have hl : 0 ≤ l := by
    have hh := Real.log_nonneg (show 1 ≤ 2 + p.L0 * p.R / p.ε + p.L1 * p.R by linarith)
    dsimp [l]
    linarith
  have hb : 0 ≤ b := by
    have hh := Real.log_nonneg (show 1 ≤ (2 + p.L0 * p.R / p.ε + p.L1 * p.R) / p.δ by
      rw [le_div_iff₀ hδ]
      linarith)
    dsimp [b]
    linarith
  have hT := stageCount_upper p h0 h1 hR.le hε
  have hB := repetitions_upper p h0 h1 hR.le hε hδ hδ1
  have hT3 := pow_le_pow_left₀ (Nat.cast_nonneg (stageCount p)) hT 3
  have hprod := mul_le_mul hB hT3 (pow_nonneg (Nat.cast_nonneg (stageCount p)) 3)
    (show 0 ≤ 8 * b by positivity)
  change (repetitions p : ℝ) * (stageCount p : ℝ) ^ 3 ≤ (8 * b) * (8 * l) ^ 3 at hprod
  have hm := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 2 ^ 46 * Q by positivity)
  have hcost := remainingCalls_upper p h0 h1 hR hε 0 (stageCount p)
  change (remainingCalls p 0 (stageCount p) : ℝ) ≤
    (stageCount p : ℝ) * 2 ^ 46 * (repetitions p : ℝ) * (stageCount p : ℝ) ^ 2 * Q at hcost
  change _ ≤ 2 ^ 60 * Q * l ^ 3 * b
  have hn : 0 ≤ Q * l ^ 3 * b := by positivity
  nlinarith

end OracleTemplate.ClippedExtragradient
