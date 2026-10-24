import LongTails.Proofs.ProjectedClippedTuning
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

lemma innerSteps_upper (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    (innerSteps t s : ℝ) ≤ 2 ^ 17 * localScale t s / regularization t s := by
  have hr := regularization_pos t hR hε s
  have hS := localScale_lower t hC h1 hR hε s
  have hS0 : 0 < localScale t s := hr.trans_le hS
  have hratio : 1 ≤ localScale t s / regularization t s := (le_div_iff₀ hr).mpr (by simpa using hS)
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 ^ 16 * localScale t s / regularization t s)).le
  change (⌈2 ^ 16 * localScale t s / regularization t s⌉₊ : ℝ) ≤ _
  simp only [mul_div_assoc] at hc ⊢
  nlinarith

lemma batchSize_upper (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    (batchSize t s : ℝ) ≤ 1 + 2 ^ 23 * t.σ ^ 2 /
      (regularization t s * localScale t s * radius t s ^ 2) := by
  have hr := regularization_pos t hR hε s
  have hS := hr.trans_le (localScale_lower t hC h1 hR hε s)
  have hd := radius_pos t hR s
  have hx : 0 ≤ 2 ^ 23 * t.σ ^ 2 / (regularization t s * localScale t s * radius t s ^ 2) := by positivity
  unfold batchSize
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith [(Nat.ceil_lt_add_one hx).le])

lemma finalBatchSize_upper (t : Tuning) (hε : 0 < t.ε) :
    (finalBatchSize t : ℝ) ≤ 1 + 2 ^ 20 * t.σ ^ 2 / t.ε ^ 2 := by
  have hx : 0 ≤ 2 ^ 20 * t.σ ^ 2 / t.ε ^ 2 := by positivity
  unfold finalBatchSize
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith [(Nat.ceil_lt_add_one hx).le])

lemma regularization_lower (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    t.ε / (2 ^ 20 * stageCount t * t.R) ≤ regularization t s := by
  have hN : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hp : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  unfold regularization
  gcongr
  nlinarith

lemma stageCalls_upper (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    (stageCalls t s : ℝ) ≤ (repetitions t : ℝ) *
      (2 ^ 19 * localScale t s / regularization t s +
        2 ^ 41 * t.σ ^ 2 / (regularization t s ^ 2 * radius t s ^ 2)) := by
  have hr := regularization_pos t hR hε s
  have hS := hr.trans_le (localScale_lower t hC h1 hR hε s)
  have hd := radius_pos t hR s
  have hm := batchSize_upper t hC h1 hR hε s
  have hT := innerSteps_upper t hC h1 hR hε s
  have hprod := mul_le_mul hT (show 2 * ((batchSize t s : ℝ) + 1) ≤
      2 * (2 + 2 ^ 23 * t.σ ^ 2 / (regularization t s * localScale t s * radius t s ^ 2)) by linarith)
      (by positivity) (by positivity : 0 ≤ 2 ^ 17 * localScale t s / regularization t s)
  have he : (2 ^ 17 * localScale t s / regularization t s) *
      (2 * (2 + 2 ^ 23 * t.σ ^ 2 / (regularization t s * localScale t s * radius t s ^ 2))) =
      2 ^ 19 * localScale t s / regularization t s +
        2 ^ 41 * t.σ ^ 2 / (regularization t s ^ 2 * radius t s ^ 2) := by field_simp
  rw [he] at hprod
  have hh := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (repetitions t) : (0 : ℝ) ≤ repetitions t)
  unfold stageCalls
  push_cast
  nlinarith only [hh]

noncomputable def deterministicWork (t : Tuning) : ℝ :=
  (t.L0 + t.L1 * t.G) * (1 + t.L1 * t.R) ^ 2 * t.R / t.ε + (1 + t.L1 * t.R) ^ 4

lemma curvature_work (t : Tuning) (h1 : 0 ≤ t.L1)
    (hR : 0 ≤ t.R) (hε : 0 < t.ε) :
    curvature t * t.R / t.ε * (1 + t.L1 * t.R) ≤ deterministicWork t := by
  have hq := mul_nonneg h1 hR
  have hpoly : (t.L1 * t.R) * (1 + t.L1 * t.R) ^ 2 ≤ (1 + t.L1 * t.R) ^ 4 := by
    nlinarith [sq_nonneg (t.L1 * t.R), mul_nonneg hq (sq_nonneg (t.L1 * t.R)),
      sq_nonneg ((t.L1 * t.R) ^ 2)]
  have he : curvature t * t.R / t.ε * (1 + t.L1 * t.R) =
      (t.L0 + t.L1 * t.G) * (1 + t.L1 * t.R) ^ 2 * t.R / t.ε +
        (t.L1 * t.R) * (1 + t.L1 * t.R) ^ 2 := by unfold curvature; field_simp
  rw [he, deterministicWork]
  linarith

lemma deterministicWork_one (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 ≤ t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) : 1 ≤ deterministicWork t := by
  have hq := mul_nonneg h1 hR
  have hp : (1 : ℝ) ≤ (1 + t.L1 * t.R) ^ 4 := one_le_pow₀ (by linarith)
  unfold deterministicWork
  have hh : 0 ≤ (t.L0 + t.L1 * t.G) * (1 + t.L1 * t.R) ^ 2 * t.R / t.ε := by positivity
  linarith

lemma localScale_ratio_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    localScale t s / regularization t s ≤ 2 ^ 41 * stageCount t * deterministicWork t := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hC := curvature_pos t h0 h1 hR.le hG hε.le
  have hN : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hN1 : (1 : ℝ) ≤ stageCount t := by exact_mod_cast stageCount_pos t
  have hD := deterministicWork_one t h0.le h1 hR.le hG hε
  have hdR := mul_le_mul_of_nonneg_left (radius_le t hR.le s) h1
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < t.ε / (2 ^ 20 * stageCount t * t.R))
    (regularization_lower t hR hε s)
  have heinv : 1 / (t.ε / (2 ^ 20 * stageCount t * t.R)) = 2 ^ 20 * stageCount t * t.R / t.ε := by field_simp
  rw [heinv] at hinv
  have hfirst : curvature t * (1 + t.L1 * radius t s) / regularization t s ≤
      2 ^ 20 * stageCount t * deterministicWork t := by
    calc
      _ = curvature t * (1 + t.L1 * radius t s) * (1 / regularization t s) := by ring
      _ ≤ curvature t * (1 + t.L1 * t.R) * (2 ^ 20 * stageCount t * t.R / t.ε) := by
        gcongr
      _ = 2 ^ 20 * stageCount t * (curvature t * t.R / t.ε * (1 + t.L1 * t.R)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (curvature_work t h1 hR.le hε) (by positivity)
  have hfourth : (1 + t.L1 * radius t s) ^ 4 ≤ deterministicWork t := by
    have hp : (1 + t.L1 * radius t s) ^ 4 ≤ (1 + t.L1 * t.R) ^ 4 := by gcongr
    have hh : 0 ≤ (t.L0 + t.L1 * t.G) * (1 + t.L1 * t.R) ^ 2 * t.R / t.ε := by positivity
    unfold deterministicWork
    linarith
  have he : localScale t s / regularization t s =
      2 ^ 20 * (curvature t * (1 + t.L1 * radius t s) / regularization t s +
        (1 + t.L1 * radius t s) ^ 4) := by unfold localScale; field_simp
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hN1 (by linarith : 0 ≤ deterministicWork t)
  nlinarith

noncomputable def logScale (t : Tuning) : ℝ := 1 + Real.log (2 + curvature t * t.R / t.ε)

noncomputable def confidenceScale (t : Tuning) : ℝ :=
  1 + Real.log ((2 + curvature t * t.R / t.ε) / t.δ)

lemma large_dyadic_upper {u : ℝ} (hu : 0 ≤ u) :
    (⌈Real.log (2 + 2 ^ 20 * u) / Real.log 2⌉₊ : ℝ) + 1 ≤ 64 * (1 + Real.log (2 + u)) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2p : 0 < Real.log 2 := by linarith
  have hl : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hb : Real.log (2 + 2 ^ 20 * u) ≤ 20 * Real.log 2 + Real.log (2 + u) := by
    have hh := Real.log_le_log (by positivity : 0 < 2 + 2 ^ 20 * u)
      (show 2 + 2 ^ 20 * u ≤ 2 ^ 20 * (2 + u) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ^ 20 ≠ 0) (by positivity), Real.log_pow] at hh
    exact hh
  have hq : Real.log (2 + 2 ^ 20 * u) / Real.log 2 ≤ 20 + 2 * Real.log (2 + u) := by
    rw [div_le_iff₀ h2p]
    nlinarith
  have hn := (Nat.ceil_lt_add_one (div_nonneg
    (Real.log_nonneg (by linarith : 1 ≤ 2 + 2 ^ 20 * u)) h2p.le)).le
  linarith

lemma stageCount_log_upper (t : Tuning) (hC : 0 ≤ curvature t) (hR : 0 ≤ t.R) (hε : 0 < t.ε) :
    (stageCount t : ℝ) ≤ 64 * logScale t := by
  have hh := large_dyadic_upper (by positivity : 0 ≤ curvature t * t.R / t.ε)
  simpa only [stageCount, logScale, Nat.cast_add, Nat.cast_one, mul_div_assoc, mul_assoc] using hh

lemma repetitions_log_upper (t : Tuning) (hC : 0 ≤ curvature t) (hR : 0 ≤ t.R)
    (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (repetitions t : ℝ) ≤ 64 * confidenceScale t := by
  let z := 2 + curvature t * t.R / t.ε
  have hz : 2 ≤ z := by dsimp [z]; linarith [show 0 ≤ curvature t * t.R / t.ε by positivity]
  have hz0 : 0 < z := by linarith
  have hN := stageCount_log_upper t hC hR hε
  have hlog := Real.log_le_sub_one_of_pos hz0
  have hNz : (stageCount t : ℝ) ≤ 64 * z := by dsimp [logScale] at hN; dsimp [z] at hlog; linarith
  have hN1 : (1 : ℝ) ≤ stageCount t := by exact_mod_cast stageCount_pos t
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2p : 0 < Real.log 2 := by linarith
  have hzδ : 1 ≤ z / t.δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl : 0 ≤ Real.log (z / t.δ) := Real.log_nonneg hzδ
  have hb : Real.log (2 * stageCount t / t.δ) ≤ 7 * Real.log 2 + Real.log (z / t.δ) := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (stageCount t : ℝ) / t.δ)
      (show 2 * (stageCount t : ℝ) / t.δ ≤ 2 ^ 7 * (z / t.δ) by
        rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ]; nlinarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ^ 7 ≠ 0) (by positivity), Real.log_pow] at hh
    exact hh
  have hq : Real.log (2 * stageCount t / t.δ) / Real.log 2 ≤ 7 + 2 * Real.log (z / t.δ) := by
    rw [div_le_iff₀ h2p]
    nlinarith
  have hn := (Nat.ceil_lt_add_one (div_nonneg
    (Real.log_nonneg (show 1 ≤ 2 * (stageCount t : ℝ) / t.δ from
      (le_div_iff₀ hδ).mpr (by linarith))) h2p.le)).le
  unfold repetitions confidenceScale
  push_cast
  change _ ≤ 64 * (1 + Real.log (z / t.δ))
  linarith

lemma stageCalls_uniform (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    (stageCalls t s : ℝ) ≤ repetitions t *
      (2 ^ 60 * stageCount t * deterministicWork t +
        2 ^ 81 * (stageCount t : ℝ) ^ 2 * (t.σ ^ 2 / t.ε ^ 2)) := by
  have hC := curvature_pos t h0 h1 hR.le hG hε.le
  have hb := stageCalls_upper t hC.le h1 hR hε s
  have hr := regularization_radius t hR s
  have hN : (stageCount t : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (stageCount_pos t))
  have he : 2 ^ 41 * t.σ ^ 2 / (regularization t s ^ 2 * radius t s ^ 2) =
      2 ^ 81 * (stageCount t : ℝ) ^ 2 * (t.σ ^ 2 / t.ε ^ 2) := by
    rw [← mul_pow, hr]
    field_simp
  rw [he] at hb
  apply hb.trans
  gcongr
  have hh := mul_le_mul_of_nonneg_left (localScale_ratio_upper t h0 h1 hR hG hε s)
    (by norm_num : (0 : ℝ) ≤ 2 ^ 19)
  simpa only [mul_div_assoc] using (show 2 ^ 19 * (localScale t s / regularization t s) ≤
    2 ^ 60 * (stageCount t : ℝ) * deterministicWork t by nlinarith only [hh])

lemma runCalls_uniform (t : Tuning) (U : ℝ) (hU : ∀ s, (stageCalls t s : ℝ) ≤ U)
    (s n : ℕ) :
    (runCalls t s n : ℝ) ≤ 1 + (finalBatchSize t : ℝ) * repetitions t + n * U := by
  induction n generalizing s with
  | zero => simp [runCalls]
  | succ n ih =>
    simp only [runCalls, Nat.cast_add, Nat.cast_one]
    linarith [ih (s + 1), hU s]

lemma runCalls_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) :
    (runCalls t 0 (stageCount t) : ℝ) ≤ 2 ^ 84 * (repetitions t : ℝ) *
      (stageCount t : ℝ) ^ 3 * (deterministicWork t + t.σ ^ 2 / t.ε ^ 2) := by
  have hh := runCalls_uniform t _ (stageCalls_uniform t h0 h1 hR hG hε) 0 (stageCount t)
  have hm := finalBatchSize_upper t hε
  have hN : (1 : ℝ) ≤ stageCount t := by exact_mod_cast stageCount_pos t
  have hk : (1 : ℝ) ≤ repetitions t := by unfold repetitions; push_cast; linarith [Nat.cast_nonneg ⌈Real.log (2 * stageCount t / t.δ) / Real.log 2⌉₊ (α := ℝ)]
  have hD := deterministicWork_one t h0.le h1 hR.le hG hε
  have hv : 0 ≤ t.σ ^ 2 / t.ε ^ 2 := by positivity
  have hN2 : (stageCount t : ℝ) ≤ (stageCount t : ℝ) ^ 2 := by nlinarith
  have hN3 : (stageCount t : ℝ) ^ 2 ≤ (stageCount t : ℝ) ^ 3 := by nlinarith
  have hbase : 1 ≤ (repetitions t : ℝ) * (stageCount t : ℝ) ^ 3 * deterministicWork t := by
    have : 1 ≤ (stageCount t : ℝ) ^ 3 := by nlinarith
    nlinarith [mul_le_mul hk this (by norm_num : (0 : ℝ) ≤ 1) (by linarith)]
  have hdet := mul_le_mul_of_nonneg_left hN3
    (show 0 ≤ (repetitions t : ℝ) * deterministicWork t by positivity)
  have hfin := mul_le_mul_of_nonneg_left (show 1 ≤ (stageCount t : ℝ) ^ 3 by nlinarith)
    (show 0 ≤ (repetitions t : ℝ) * (2 + 2 ^ 20 * (t.σ ^ 2 / t.ε ^ 2)) by positivity)
  have hm' := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (repetitions t) : (0 : ℝ) ≤ repetitions t)
  have hv' : 0 ≤ (repetitions t : ℝ) * (stageCount t : ℝ) ^ 3 * (t.σ ^ 2 / t.ε ^ 2) := by positivity
  have hDmul := mul_le_mul_of_nonneg_left hD
    (show 0 ≤ (repetitions t : ℝ) * (stageCount t : ℝ) ^ 3 by positivity)
  simp only [mul_div_assoc] at hm'
  nlinarith only [hh, hm', hbase, hdet, hfin, hv', hDmul, hk]

lemma total_calls_bound (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (runCalls t 0 (stageCount t) : ℝ) ≤ 2 ^ 128 *
      (deterministicWork t + t.σ ^ 2 / t.ε ^ 2) * logScale t ^ 3 * confidenceScale t := by
  have hC := curvature_pos t h0 h1 hR.le hG hε.le
  have hN := stageCount_log_upper t hC.le hR.le hε
  have hk := repetitions_log_upper t hC.le hR.le hε hδ hδ1
  have hD := deterministicWork_one t h0.le h1 hR.le hG hε
  have hL : 0 ≤ logScale t := by
    unfold logScale
    have := Real.log_nonneg (show 1 ≤ 2 + curvature t * t.R / t.ε by linarith [show 0 ≤ curvature t * t.R / t.ε by positivity])
    linarith
  have hδL : 0 ≤ confidenceScale t := by
    have : (0 : ℝ) ≤ repetitions t := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ 2 ^ 84 * (repetitions t : ℝ) * (stageCount t : ℝ) ^ 3 *
        (deterministicWork t + t.σ ^ 2 / t.ε ^ 2) := runCalls_work_upper t h0 h1 hR hG hε
    _ ≤ 2 ^ 84 * (64 * confidenceScale t) * (64 * logScale t) ^ 3 *
        (deterministicWork t + t.σ ^ 2 / t.ε ^ 2) := by gcongr
    _ ≤ _ := by
      have hh : 0 ≤ (deterministicWork t + t.σ ^ 2 / t.ε ^ 2) * logScale t ^ 3 * confidenceScale t := by positivity
      nlinarith only [hh]

end OracleTemplate.ProjectedClippedExtragradient
