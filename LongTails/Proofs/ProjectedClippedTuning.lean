import LongTails.Algorithms.ProjectedClippedExtragradient
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

lemma stageCount_pos (t : Tuning) : 0 < stageCount t := by
  unfold stageCount
  omega

lemma radius_pos (t : Tuning) (hR : 0 < t.R) (s : ℕ) : 0 < radius t s := by
  unfold radius
  positivity

lemma regularization_pos (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    0 < regularization t s := by
  unfold regularization
  have : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  positivity

lemma curvature_pos (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 ≤ t.R) (hG : 0 ≤ t.G) (hε : 0 ≤ t.ε) : 0 < curvature t := by
  unfold curvature
  positivity

lemma curvature_lower (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 ≤ t.R) (hG : 0 ≤ t.G) (hε : 0 ≤ t.ε) :
    t.L0 + t.L1 * t.ε ≤ curvature t := by
  unfold curvature
  have hprod := mul_nonneg (by positivity : 0 ≤ t.L0 + t.L1 * t.G + t.L1 * t.ε)
    (mul_nonneg h1 hR)
  nlinarith [mul_nonneg h1 hG]

lemma rootBound_curvature (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 ≤ t.R) (hG : 0 ≤ t.G) (hε : 0 ≤ t.ε) :
    t.L0 + t.L1 * rootBound t + t.L1 * t.ε ≤ 16 * curvature t := by
  rw [← sub_nonneg]
  have he : 16 * curvature t - (t.L0 + t.L1 * rootBound t + t.L1 * t.ε) =
      15 * (t.L0 + t.L1 * t.G) + 14 * t.L1 * t.ε + 8 * t.L1 ^ 2 * t.ε * t.R := by
    unfold curvature rootBound
    ring
  rw [he]
  positivity

lemma scale_component_bounds (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    2 ^ 20 * curvature t * (1 + t.L1 * radius t s) ≤ localScale t s ∧
      2 ^ 20 * regularization t s * (1 + t.L1 * radius t s) ^ 4 ≤ localScale t s := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  unfold localScale
  constructor <;> nlinarith [mul_nonneg hC (by positivity : 0 ≤ 1 + t.L1 * radius t s),
    mul_nonneg hr.le (pow_nonneg (by positivity : 0 ≤ 1 + t.L1 * radius t s) 4)]

lemma localScale_lower (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) : regularization t s ≤ localScale t s := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hs := (scale_component_bounds t hC h1 hR hε s).2
  have hq : (1 : ℝ) ≤ 1 + t.L1 * radius t s := by nlinarith [mul_nonneg h1 hd.le]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) hq 4
  norm_num at hpow
  have hm := mul_le_mul_of_nonneg_left hpow hr.le
  nlinarith

lemma probe_properties {b d : ℝ} (hb : 0 ≤ b) (hd : 0 < d) :
    0 < 3 * d / (1 + 6 * b * d) ∧ 3 * d / (1 + 6 * b * d) ≤ 3 * d ∧
      b * (3 * d / (1 + 6 * b * d)) ≤ 1 / 2 := by
  have hden : 0 < 1 + 6 * b * d := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hb (sq_nonneg d)]
  · rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith

lemma fourth_power_scale {q : ℝ} (hq : 0 ≤ q) :
    (1 + 6 * q) ^ 2 * (1 + 48 * q) ^ 2 ≤ 2 ^ 20 * (1 + q) ^ 4 := by
  calc
    _ ≤ (6 * (1 + q)) ^ 2 * (48 * (1 + q)) ^ 2 := by gcongr <;> nlinarith
    _ = 82944 * (1 + q) ^ 4 := by ring
    _ ≤ _ := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + q) 4]

lemma tuned_saturation_scale (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    regularization t s * (3 * radius t s) ^ 2 * (1 + 16 * t.L1 * (3 * radius t s)) ^ 2 ≤
      localScale t s * (3 * radius t s / (1 + 6 * t.L1 * radius t s)) ^ 2 := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hden : 0 < 1 + 6 * t.L1 * radius t s := by positivity
  have hs := (scale_component_bounds t hC h1 hR hε s).2
  have ht := mul_le_mul_of_nonneg_left (fourth_power_scale (mul_nonneg h1 hd.le)) hr.le
  have hbase : regularization t s * (1 + 6 * t.L1 * radius t s) ^ 2 *
      (1 + 48 * t.L1 * radius t s) ^ 2 ≤ localScale t s := by nlinarith
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hden)]
  have hmul := mul_le_mul_of_nonneg_right hbase (sq_nonneg (3 * radius t s))
  nlinarith

lemma batchSize_pos (t : Tuning) (s : ℕ) : 0 < batchSize t s := by
  unfold batchSize
  omega

lemma innerSteps_lower (t : Tuning) (s : ℕ) :
    2 ^ 16 * localScale t s / regularization t s ≤ (innerSteps t s : ℝ) := Nat.le_ceil _

lemma batchSize_variance (t : Tuning) (hC : 0 ≤ curvature t) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    8 * (t.σ ^ 2 / batchSize t s) ≤ regularization t s * localScale t s * radius t s ^ 2 / 2 ^ 20 := by
  have hr := regularization_pos t hR hε s
  have hS := hr.trans_le (localScale_lower t hC h1 hR hε s)
  have hd := radius_pos t hR s
  have hn : (0 : ℝ) < batchSize t s := Nat.cast_pos.mpr (batchSize_pos t s)
  have hceil : 2 ^ 23 * t.σ ^ 2 / (regularization t s * localScale t s * radius t s ^ 2) ≤
      (batchSize t s : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hmul := (div_le_iff₀ (by positivity : 0 < regularization t s * localScale t s * radius t s ^ 2)).mp hceil
  rw [← mul_div_assoc, div_le_iff₀ hn]
  nlinarith

lemma localScale_coercivity (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    4 * t.L1 * (rootBound t + t.ε + 3 * regularization t s * radius t s +
      12 * (t.L0 + t.L1 * rootBound t) * radius t s) ≤ localScale t s := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hC : 0 ≤ curvature t := by unfold curvature; positivity
  have hM : 0 ≤ rootBound t := by unfold rootBound; positivity
  have hc := rootBound_curvature t h0 h1 hR.le hG hε.le
  have hq := mul_nonneg h1 hd.le
  have hpow : 1 + t.L1 * radius t s ≤ (1 + t.L1 * radius t s) ^ 4 := by
    nlinarith [sq_nonneg (t.L1 * radius t s),
      mul_nonneg hq (sq_nonneg (t.L1 * radius t s)),
      sq_nonneg ((t.L1 * radius t s) ^ 2)]
  have hm := mul_le_mul_of_nonneg_right hc hq
  have hp := mul_le_mul_of_nonneg_left hpow hr.le
  unfold localScale
  nlinarith [mul_nonneg hC hq, mul_nonneg hr.le hq,
    mul_nonneg (mul_nonneg h1 hε.le) hq]

lemma localScale_smoothness (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    t.L0 + regularization t s + t.L1 * t.ε +
      3 * t.L1 * regularization t s * radius t s ≤ localScale t s := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hC : 0 ≤ curvature t := by unfold curvature; positivity
  have hc := curvature_lower t h0 h1 hR.le hG hε.le
  have hq := mul_nonneg h1 hd.le
  have hpow : 1 + t.L1 * radius t s ≤ (1 + t.L1 * radius t s) ^ 4 := by
    nlinarith [sq_nonneg (t.L1 * radius t s),
      mul_nonneg hq (sq_nonneg (t.L1 * radius t s)),
      sq_nonneg ((t.L1 * radius t s) ^ 2)]
  have hp := mul_le_mul_of_nonneg_left hpow hr.le
  unfold localScale
  nlinarith [mul_nonneg hC hq, mul_nonneg hr.le hq]

lemma regularization_radius (t : Tuning) (hR : 0 < t.R) (s : ℕ) :
    regularization t s * radius t s = t.ε / (2 ^ 20 * stageCount t) := by
  unfold regularization radius
  have hN : (stageCount t : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (stageCount_pos t))
  field_simp

lemma regularization_succ (t : Tuning) (s : ℕ) :
    regularization t (s + 1) = 2 * regularization t s := by
  unfold regularization
  rw [pow_succ]
  ring

lemma radius_succ (t : Tuning) (s : ℕ) : radius t (s + 1) = radius t s / 2 := by
  unfold radius
  rw [pow_succ, div_mul_eq_div_div]

lemma radius_le (t : Tuning) (hR : 0 ≤ t.R) (s : ℕ) : radius t s ≤ t.R := by
  unfold radius
  exact div_le_self hR (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

lemma radius_geometric_sum (t : Tuning) (n : ℕ) :
    ∑ s ∈ Finset.range n, radius t s = 2 * t.R * (1 - (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, radius, pow_succ]
    rw [one_div_pow]
    ring

lemma dyadic_cover {u : ℝ} (hu : 0 < u) :
    u ≤ (2 : ℝ) ^ ⌈Real.log u / Real.log 2⌉₊ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ h2).mp (Nat.le_ceil (Real.log u / Real.log 2))
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hu, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact he

lemma last_radius_curvature (t : Tuning) (hC : 0 ≤ curvature t)
    (hR : 0 < t.R) (hε : 0 < t.ε) :
    curvature t * radius t (stageCount t - 1) ≤ t.ε / 2 ^ 20 := by
  have hh := dyadic_cover (by positivity : 0 < 2 + 2 ^ 20 * curvature t * t.R / t.ε)
  have hs : stageCount t - 1 = ⌈Real.log (2 + 2 ^ 20 * curvature t * t.R / t.ε) / Real.log 2⌉₊ := by
    unfold stageCount
    omega
  unfold radius
  rw [hs, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_left hh hε.le
  have he : t.ε * (2 + 2 ^ 20 * curvature t * t.R / t.ε) =
      2 * t.ε + 2 ^ 20 * curvature t * t.R := by field_simp
  rw [he] at hm
  nlinarith

lemma repetitions_confidence (t : Tuning) (hδ : 0 < t.δ) :
    (1 / 2 : ℝ) ^ repetitions t ≤ t.δ / (2 * stageCount t) := by
  have ht : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log ((2 : ℝ) * stageCount t / t.δ) / Real.log 2)
  have hb : Real.log ((2 : ℝ) * stageCount t / t.δ) / Real.log 2 ≤ (repetitions t : ℝ) := by
    unfold repetitions
    push_cast
    linarith
  have hh := (div_le_iff₀ h2).mp hb
  apply (Real.log_le_log_iff (by positivity) (by positivity : 0 < t.δ / (2 * stageCount t))).mp
  rw [Real.log_pow, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one, Real.log_div hδ.ne' (by positivity : (2 : ℝ) * stageCount t ≠ 0)]
  rw [Real.log_div (by positivity : (2 : ℝ) * stageCount t ≠ 0) hδ.ne'] at hh
  linarith

lemma last_radius_certificate (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) :
    radius t (stageCount t - 1) / 2 ≤ finalStepSize t * t.ε / 32 := by
  have hC := curvature_pos t h0 h1 hR.le hG hε.le
  have hd := radius_pos t hR (stageCount t - 1)
  have hr := regularization_pos t hR hε (stageCount t - 1)
  have hM : 0 ≤ rootBound t := by unfold rootBound; positivity
  have hs : 0 < t.L0 + t.L1 * rootBound t + t.L1 * t.ε + regularization t (stageCount t - 1) := by positivity
  have hrc := last_radius_curvature t hC.le hR hε
  have hrd := regularization_radius t hR (stageCount t - 1)
  have hN : (1 : ℝ) ≤ stageCount t := by exact_mod_cast stageCount_pos t
  have he : t.ε / (2 ^ 20 * stageCount t) ≤ t.ε / 2 ^ 20 :=
    div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
  have hm := mul_le_mul_of_nonneg_right (rootBound_curvature t h0.le h1 hR.le hG hε.le) hd.le
  unfold finalStepSize
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
  rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

lemma finalBatchSize_pos (t : Tuning) : 0 < finalBatchSize t := by
  unfold finalBatchSize
  omega

lemma finalBatchSize_variance (t : Tuning) (hε : 0 < t.ε) :
    t.σ ^ 2 / finalBatchSize t ≤ t.ε ^ 2 / 2 ^ 20 := by
  have hm : (0 : ℝ) < finalBatchSize t := Nat.cast_pos.mpr (finalBatchSize_pos t)
  have hc : 2 ^ 20 * t.σ ^ 2 / t.ε ^ 2 ≤ (finalBatchSize t : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  rw [div_le_iff₀ hm]
  nlinarith

lemma finalBatchSize_tail (t : Tuning) (hε : 0 < t.ε) :
    (t.σ ^ 2 / finalBatchSize t) / ((t.ε / 16) / 6) ^ 2 ≤ 1 / 16 := by
  have hh := finalBatchSize_variance t hε
  rw [div_le_iff₀ (by positivity : 0 < ((t.ε / 16) / 6) ^ 2)]
  nlinarith [sq_nonneg t.ε]

end OracleTemplate.ProjectedClippedExtragradient
