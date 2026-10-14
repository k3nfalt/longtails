import LongTails.Algorithms.LocalizedClippedExtragradient
import LongTails.Proofs.TwoSidedPLBudget

open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

lemma stage_decay {μ S : ℝ} (hμ : 0 < μ) (hμS : μ ≤ S)
    {n : ℕ} (hn : 2 ^ 16 * S / μ ≤ (n : ℝ)) :
    (1 - μ / (4608 * S)) ^ n ≤ 1 / 8192 := by
  have hS : 0 < S := hμ.trans_le hμS
  let C := 4608 * S / μ
  have hC : 1 ≤ C := by dsimp [C]; rw [le_div_iff₀ hμ]; nlinarith
  have hCe : 1 / C = μ / (4608 * S) := by dsimp [C]; field_simp
  have hpow := TwoSidedPL.pow_le_exp_window hC n
  rw [hCe] at hpow
  have hnC : 14 ≤ (n : ℝ) / C := by
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one hC)]
    dsimp [C]
    have hh : 14 * (4608 * S / μ) ≤ 2 ^ 16 * S / μ := by
      have hnon : 0 ≤ S / μ := by positivity
      calc
        _ = 64512 * (S / μ) := by ring
        _ ≤ 65536 * (S / μ) := by nlinarith
        _ = _ := by norm_num; ring
    exact hh.trans hn
  have he : Real.exp (-((n : ℝ) / C)) ≤ Real.exp (-2) ^ 7 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hsmall := pow_le_pow_left₀ (Real.exp_pos (-2)).le TwoSidedPL.exp_neg_two_le 7
  norm_num at hsmall
  exact hpow.trans (he.trans (hsmall.trans (by norm_num)))

lemma geometric_drift_sum {μ S : ℝ} (hμ : 0 < μ) (hμS : μ ≤ S) (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 - μ / (4608 * S)) ^ j ≤ 4608 * S / μ := by
  have hS : 0 < S := hμ.trans_le hμS
  have hq : 0 ≤ 1 - μ / (4608 * S) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hκ : 0 < μ / (4608 * S) := by positivity
  have hgeom : μ / (4608 * S) *
      (∑ j ∈ Finset.range n, (1 - μ / (4608 * S)) ^ j) =
      1 - (1 - μ / (4608 * S)) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  apply (le_div_iff₀ hμ).mpr
  have hh : μ / (4608 * S) *
      (∑ j ∈ Finset.range n, (1 - μ / (4608 * S)) ^ j) ≤ 1 := by
    rw [hgeom]
    linarith [pow_nonneg hq n]
  have hh' := (div_le_iff₀ (show 0 < 4608 * S by positivity)).mp
    (show (μ * (∑ j ∈ Finset.range n, (1 - μ / (4608 * S)) ^ j)) /
      (4608 * S) ≤ 1 by simpa only [div_mul_eq_mul_div] using hh)
  nlinarith

lemma stage_moment_bound {μ S d v : ℝ} (hμ : 0 < μ) (hμS : μ ≤ S)
    (hv : 0 ≤ v) (hnoise : v ≤ μ * S * d ^ 2 / 2 ^ 20)
    {n : ℕ} (hn : 2 ^ 16 * S / μ ≤ (n : ℝ)) :
    (1 - μ / (4608 * S)) ^ n * d ^ 2 +
      v / (64 * S ^ 2) * ∑ j ∈ Finset.range n, (1 - μ / (4608 * S)) ^ j ≤
      d ^ 2 / 4096 := by
  have hS : 0 < S := hμ.trans_le hμS
  have h1 := mul_le_mul_of_nonneg_right (stage_decay hμ hμS hn) (sq_nonneg d)
  have h2 := mul_le_mul_of_nonneg_left (geometric_drift_sum hμ hμS n)
    (show 0 ≤ v / (64 * S ^ 2) by positivity)
  have he : v / (64 * S ^ 2) * (4608 * S / μ) = 72 * v / (μ * S) := by
    field_simp; ring
  rw [he] at h2
  have h3 : 72 * v / (μ * S) ≤ d ^ 2 / 8192 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg d]
  linarith

lemma stageCount_pos (p : Tuning) : 0 < stageCount p := by
  unfold stageCount
  omega

lemma regularization_pos (p : Tuning) (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    0 < regularization p s := by
  unfold regularization
  have ht : (0 : ℝ) < stageCount p := Nat.cast_pos.mpr (stageCount_pos p)
  positivity

lemma radius_pos (p : Tuning) (hR : 0 < p.R) (s : ℕ) : 0 < radius p s := by
  unfold radius
  positivity

lemma localScale_lower (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    regularization p s ≤ localScale p s := by
  have hr := regularization_pos p hR hε s
  have hd := radius_pos p hR s
  unfold localScale
  have hh : 0 ≤ p.L1 * radius p s := mul_nonneg h1 hd.le
  have hprod := mul_nonneg hr.le (sq_nonneg (p.L1 * radius p s))
  nlinarith [mul_nonneg h1 hε.le, mul_nonneg hr.le hh]

lemma batchSize_pos (p : Tuning) (s : ℕ) : 0 < batchSize p s := by
  unfold batchSize
  omega

lemma batchSize_variance (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    p.σ ^ 2 / batchSize p s ≤ regularization p s * localScale p s * radius p s ^ 2 / 2 ^ 20 := by
  have hr := regularization_pos p hR hε s
  have hS := hr.trans_le (localScale_lower p h0 h1 hR hε s)
  have hd := radius_pos p hR s
  have hm : (0 : ℝ) < batchSize p s := Nat.cast_pos.mpr (batchSize_pos p s)
  have hc := Nat.le_ceil (2 ^ 20 * p.σ ^ 2 /
    (regularization p s * localScale p s * radius p s ^ 2))
  have hmax : (⌈2 ^ 20 * p.σ ^ 2 /
      (regularization p s * localScale p s * radius p s ^ 2)⌉₊ : ℝ) ≤ batchSize p s := by
    unfold batchSize
    exact Nat.cast_le.mpr (le_max_right 1 _)
  have hh := (div_le_iff₀ (show 0 < regularization p s * localScale p s * radius p s ^ 2 by positivity)).mp
    (hc.trans hmax)
  rw [div_le_iff₀ hm]
  nlinarith

lemma regularization_radius (p : Tuning) (hR : p.R ≠ 0) (s : ℕ) :
    regularization p s * radius p s = p.ε / (8 * stageCount p) := by
  unfold regularization radius
  have htwo : (2 : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

lemma radius_succ (p : Tuning) (s : ℕ) : radius p (s + 1) = radius p s / 2 := by
  unfold radius
  rw [pow_succ]
  ring

lemma regularization_succ (p : Tuning) (s : ℕ) :
    regularization p (s + 1) = 2 * regularization p s := by
  unfold regularization
  rw [pow_succ]
  ring

lemma innerSteps_lower (p : Tuning) (s : ℕ) :
    2 ^ 16 * localScale p s / regularization p s ≤ (innerSteps p s : ℝ) :=
  Nat.le_ceil _

lemma clippingScale_pos (p : Tuning) (h1 : 0 ≤ p.L1) (hR : 0 < p.R) (s : ℕ) :
    0 < clippingScale p s := by
  have hd := radius_pos p hR s
  unfold clippingScale
  positivity

lemma localScale_controls (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    p.L0 + regularization p s + p.L1 * (p.ε + 4 * regularization p s * radius p s) ≤ localScale p s ∧
    regularization p s * clippingScale p s ^ 2 * radius p s ^ 2 ≤ localScale p s := by
  have hr := regularization_pos p hR hε s
  have hd := radius_pos p hR s
  have he : clippingScale p s ^ 2 * radius p s ^ 2 = (p.L1 * radius p s + 1) ^ 2 := by
    unfold clippingScale
    field_simp

  rw [mul_assoc (regularization p s), he]
  unfold localScale
  have hh := mul_nonneg hr.le (mul_nonneg h1 hd.le)
  have hs := mul_nonneg hr.le (sq_nonneg (p.L1 * radius p s))
  constructor <;> nlinarith [mul_nonneg h1 hε.le]

lemma rounded_stage_cost {r S d σ : ℝ} (hr : 0 < r) (hrS : r ≤ S) (hd : 0 < d) :
    (2 : ℝ) * ⌈2 ^ 16 * S / r⌉₊ * max (1 : ℝ) (⌈2 ^ 20 * σ ^ 2 / (r * S * d ^ 2)⌉₊ : ℝ) ≤
      2 ^ 39 * (S / r + σ ^ 2 / (r ^ 2 * d ^ 2)) := by
  have hS : 0 < S := hr.trans_le hrS
  have hratio : 1 ≤ S / r := (le_div_iff₀ hr).mpr (by simpa using hrS)
  have hn := (Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 16 * S / r by positivity)).le
  have hm := (Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 20 * σ ^ 2 / (r * S * d ^ 2) by positivity)).le
  have hn' : (⌈2 ^ 16 * S / r⌉₊ : ℝ) ≤ 65537 * (S / r) := by
    have he : 2 ^ 16 * S / r = 65536 * (S / r) := by norm_num; ring
    rw [he] at hn ⊢
    linarith
  have hm' : max (1 : ℝ) (⌈2 ^ 20 * σ ^ 2 / (r * S * d ^ 2)⌉₊ : ℝ) ≤
      1 + 2 ^ 20 * σ ^ 2 / (r * S * d ^ 2) := by
    apply max_le
    · have hh : 0 ≤ 2 ^ 20 * σ ^ 2 / (r * S * d ^ 2) := by positivity
      linarith
    · linarith
  have hprod := mul_le_mul hn' hm' (by positivity)
    (show 0 ≤ 65537 * (S / r) by positivity)
  have he : 65537 * (S / r) * (1 + 2 ^ 20 * σ ^ 2 / (r * S * d ^ 2)) =
      65537 * (S / r) + 68720525312 * (σ ^ 2 / (r ^ 2 * d ^ 2)) := by
    field_simp; ring
  rw [he] at hprod
  have hnoise : 0 ≤ σ ^ 2 / (r ^ 2 * d ^ 2) := by positivity
  norm_num
  nlinarith

lemma stageCalls_upper (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    (stageCalls p s : ℝ) ≤ 2 ^ 39 * (repetitions p : ℝ) *
      (localScale p s / regularization p s +
        p.σ ^ 2 / (regularization p s ^ 2 * radius p s ^ 2)) := by
  have hh := rounded_stage_cost (σ := p.σ) (regularization_pos p hR hε s)
    (localScale_lower p h0 h1 hR hε s) (radius_pos p hR s)
  have he : (stageCalls p s : ℝ) =
      (2 * (innerSteps p s : ℝ) * (batchSize p s : ℝ)) * (repetitions p : ℝ) := by
    unfold stageCalls
    push_cast
    ring
  rw [he]
  have hcast : (batchSize p s : ℝ) =
      max 1 (⌈2 ^ 20 * p.σ ^ 2 / (regularization p s * localScale p s * radius p s ^ 2)⌉₊ : ℝ) := by
    unfold batchSize
    norm_cast
  rw [hcast]
  unfold innerSteps
  have hmul := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (repetitions p))
  nlinarith

lemma stage_ratio_uniform (p : Tuning) (h0 : 0 ≤ p.L0) (h1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (s : ℕ) :
    localScale p s / regularization p s +
      p.σ ^ 2 / (regularization p s ^ 2 * radius p s ^ 2) ≤
      128 * (stageCount p : ℝ) ^ 2 *
        (1 + p.L0 * p.R / p.ε + (p.L1 * p.R) ^ 2 + p.σ ^ 2 / p.ε ^ 2) := by
  let T : ℝ := stageCount p
  let A := p.L0 * p.R / p.ε
  let q := p.L1 * p.R
  let V := p.σ ^ 2 / p.ε ^ 2
  let Q := 1 + A + q ^ 2 + V
  have hT : 1 ≤ T := by
    dsimp [T]
    exact_mod_cast (Nat.succ_le_of_lt (stageCount_pos p))
  have hT0 : 0 < T := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg q]
  have hAQ : A ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg q]
  have hqQ : q ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg (q - 1 / 2)]
  have hq2Q : q ^ 2 ≤ Q := by dsimp [Q]; linarith
  have hVQ : V ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg q]
  have hp2 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hd := radius_pos p hR s
  have hr := regularization_pos p hR hε s
  have hdR : radius p s ≤ p.R := by
    unfold radius
    exact div_le_self hR.le hp2
  have hqstage : p.L1 * radius p s ≤ q := mul_le_mul_of_nonneg_left hdR h1
  have hrbound : p.ε / (8 * T * p.R) ≤ regularization p s := by
    unfold regularization
    dsimp [T]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have he : (p.L0 + p.L1 * p.ε) / (p.ε / (8 * T * p.R)) = 8 * T * (A + q) := by
    dsimp [A, q]
    field_simp

  have hratio : (p.L0 + p.L1 * p.ε) / regularization p s ≤ 8 * T * (A + q) := by
    rw [← he]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hrbound
  have hscale : localScale p s / regularization p s ≤
      8 * T * (A + q) + 2 + 6 * q + q ^ 2 := by
    have hsq := pow_le_pow_left₀ (mul_nonneg h1 hd.le) hqstage 2
    have he : localScale p s / regularization p s =
        (p.L0 + p.L1 * p.ε) / regularization p s +
          2 + 6 * p.L1 * radius p s + (p.L1 * radius p s) ^ 2 := by
      unfold localScale
      field_simp; ring
    rw [he]
    nlinarith
  have hnoise : p.σ ^ 2 / (regularization p s ^ 2 * radius p s ^ 2) = 64 * T ^ 2 * V := by
    rw [← mul_pow, regularization_radius p hR.ne' s]
    dsimp [V, T]
    field_simp; ring
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left (show A + q ≤ 2 * Q by linarith)
    (show 0 ≤ 8 * T by positivity)
  have hmul2 := mul_le_mul_of_nonneg_right hT2 (show 0 ≤ 16 * Q by linarith)
  have hmul3 := mul_le_mul_of_nonneg_right (show 1 ≤ T ^ 2 by nlinarith)
    (show 0 ≤ 9 * Q by linarith)
  have hmul4 := mul_le_mul_of_nonneg_left hVQ (show 0 ≤ 64 * T ^ 2 by positivity)
  rw [hnoise]
  change _ ≤ 128 * T ^ 2 * Q
  nlinarith

end OracleTemplate.ClippedExtragradient
