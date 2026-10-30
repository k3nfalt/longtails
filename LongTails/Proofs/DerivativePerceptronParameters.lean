import LongTails.Proofs.DerivativePerceptronCounting

namespace LongTails.Proofs.DerivativePerceptronParameters

structure Tuning where
  κ : ℝ
  r : ℝ
  x : ℝ
  margin_pos : 0 < κ
  margin_le : κ ≤ 1
  ratio_pos : 0 < r
  ratio_le : r ≤ 1
  contrast_pos : 0 < x
  contrast_le : x ≤ κ ^ 20 * r ^ 24 / 2 ^ 400

namespace Tuning

noncomputable def stepScale (t : Tuning) : ℝ := t.κ ^ 2 * t.r ^ 2 / 2 ^ 40
noncomputable def backgroundScale (t : Tuning) : ℝ := t.r * t.stepScale
noncomputable def residualScale (t : Tuning) : ℝ := t.stepScale ^ 2 * t.x ^ 2
noncomputable def logarithm (t : Tuning) : ℝ := 1 + Real.log (1 / t.x)
noncomputable def warmup (t : Tuning) : ℕ :=
  2 * ⌈8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale)⌉₊
noncomputable def iterations (t : Tuning) : ℕ :=
  ⌈2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm⌉₊

lemma stepScale_pos (t : Tuning) : 0 < t.stepScale := by
  unfold stepScale
  exact div_pos (mul_pos (sq_pos_of_pos t.margin_pos) (sq_pos_of_pos t.ratio_pos)) (by norm_num)

lemma stepScale_le (t : Tuning) : t.stepScale ≤ 1 / 2 ^ 40 := by
  have hκ : t.κ ^ 2 ≤ 1 := by nlinarith [t.margin_pos, t.margin_le]
  have hr : t.r ^ 2 ≤ 1 := by nlinarith [t.ratio_pos, t.ratio_le]
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg t.κ)
  unfold stepScale
  apply div_le_div_of_nonneg_right _ (by norm_num)
  nlinarith only [hm, hκ]

lemma stepScale_margin (t : Tuning) : t.stepScale ≤ t.κ / 4 := by
  have hκ : t.κ ^ 2 ≤ t.κ := by nlinarith [t.margin_pos, t.margin_le]
  have hr : t.r ^ 2 ≤ 1 := by nlinarith [t.ratio_pos, t.ratio_le]
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg t.κ)
  unfold stepScale
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 40)).mpr
  nlinarith only [hm, hκ, t.margin_pos]

lemma backgroundScale_pos (t : Tuning) : 0 < t.backgroundScale :=
  mul_pos t.ratio_pos t.stepScale_pos

lemma backgroundScale_le (t : Tuning) : t.backgroundScale ≤ t.stepScale := by
  have hm := mul_le_mul_of_nonneg_right t.ratio_le t.stepScale_pos.le
  simpa [backgroundScale] using hm

lemma residualScale_pos (t : Tuning) : 0 < t.residualScale := by
  unfold residualScale
  exact mul_pos (sq_pos_of_pos t.stepScale_pos) (sq_pos_of_pos t.contrast_pos)

lemma contrast_bound (t : Tuning) : t.x ≤ 1 / 2 ^ 400 := by
  have hκ : t.κ ^ 20 ≤ 1 := by simpa using pow_le_pow_left₀ t.margin_pos.le t.margin_le 20
  have hr : t.r ^ 24 ≤ 1 := by simpa using pow_le_pow_left₀ t.ratio_pos.le t.ratio_le 24
  have hm := mul_le_mul_of_nonneg_left hr (pow_nonneg t.margin_pos.le 20)
  apply t.contrast_le.trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  nlinarith only [hm, hκ]

lemma contrast_lt_one (t : Tuning) : t.x < 1 := by
  have hp : (1 : ℝ) < 2 ^ (400 : ℕ) := one_lt_pow₀ (by norm_num) (by norm_num)
  have hd : (1 : ℝ) / 2 ^ 400 < 1 := (div_lt_one (by positivity)).mpr hp
  exact t.contrast_bound.trans_lt hd

lemma logarithm_ge_one (t : Tuning) : 1 ≤ t.logarithm := by
  have hd : 1 ≤ 1 / t.x := (one_le_div t.contrast_pos).mpr t.contrast_lt_one.le
  have hl := Real.log_nonneg hd
  unfold logarithm
  linarith only [hl]

lemma leakage_small (t : Tuning) :
    1024 * DerivativePerceptronCounting.leakage t.stepScale t.stepScale t.backgroundScale ≤ t.κ ^ 2 := by
  have hh : t.stepScale ≤ 1 / 4096 := t.stepScale_le.trans (by norm_num)
  have hl := DerivativePerceptronCounting.leakage_bound t.stepScale t.r
    t.stepScale_pos t.ratio_pos hh t.ratio_le
  have hid : 128 * t.stepScale / t.r ^ 2 = t.κ ^ 2 / 2 ^ 33 := by
    unfold stepScale
    field_simp [ne_of_gt t.ratio_pos]
    ring
  rw [hid] at hl
  change 1024 * DerivativePerceptronCounting.leakage t.stepScale t.stepScale (t.r * t.stepScale) ≤ _
  nlinarith only [hl, sq_nonneg t.κ]

lemma logarithmic_contrast (t : Tuning) :
    400 * Real.log 2 + 20 * Real.log (1 / t.κ) + 24 * Real.log (1 / t.r) ≤
      Real.log (1 / t.x) := by
  have hl := Real.log_le_log t.contrast_pos t.contrast_le
  rw [Real.log_div (mul_ne_zero (pow_ne_zero 20 (ne_of_gt t.margin_pos))
      (pow_ne_zero 24 (ne_of_gt t.ratio_pos))) (pow_ne_zero 400 (by norm_num)),
    Real.log_mul (pow_ne_zero 20 (ne_of_gt t.margin_pos))
      (pow_ne_zero 24 (ne_of_gt t.ratio_pos))] at hl
  simp only [Real.log_pow, Nat.cast_ofNat] at hl
  simp only [one_div, Real.log_inv]
  linarith only [hl]

lemma log_stepScale (t : Tuning) : Real.log t.stepScale =
    2 * Real.log t.κ + 2 * Real.log t.r - 40 * Real.log 2 := by
  unfold stepScale
  rw [Real.log_div (mul_ne_zero (pow_ne_zero 2 (ne_of_gt t.margin_pos))
      (pow_ne_zero 2 (ne_of_gt t.ratio_pos))) (pow_ne_zero 40 (by norm_num)),
    Real.log_mul (pow_ne_zero 2 (ne_of_gt t.margin_pos))
      (pow_ne_zero 2 (ne_of_gt t.ratio_pos))]
  simp only [Real.log_pow, Nat.cast_ofNat]

lemma log_residual_inverse (t : Tuning) : Real.log (1 / t.residualScale) =
    80 * Real.log 2 + 4 * Real.log (1 / t.κ) + 4 * Real.log (1 / t.r) +
      2 * Real.log (1 / t.x) := by
  simp only [one_div, Real.log_inv]
  unfold residualScale
  rw [Real.log_mul (pow_ne_zero 2 (ne_of_gt t.stepScale_pos))
    (pow_ne_zero 2 (ne_of_gt t.contrast_pos))]
  simp only [Real.log_pow, Nat.cast_ofNat, t.log_stepScale]
  ring

lemma log_residual_bounds (t : Tuning) :
    1 ≤ Real.log (1 / t.residualScale) ∧ Real.log (1 / t.residualScale) ≤ 3 * t.logarithm := by
  have hκ := Real.log_nonneg ((one_le_div t.margin_pos).mpr t.margin_le)
  have hr := Real.log_nonneg ((one_le_div t.ratio_pos).mpr t.ratio_le)
  have hx := Real.log_nonneg ((one_le_div t.contrast_pos).mpr t.contrast_lt_one.le)
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  have hc := t.logarithmic_contrast
  rw [t.log_residual_inverse]
  unfold logarithm
  constructor <;> linarith only [hκ, hr, hx, htwo, hc]

lemma backgroundScale_le_one (t : Tuning) : t.backgroundScale ≤ 1 :=
  t.backgroundScale_le.trans (t.stepScale_le.trans (by norm_num))

lemma warmup_log_threshold (t : Tuning) : Real.log (1 / t.residualScale) ≤
    (t.backgroundScale ^ 2 / 8) *
      (⌈8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale)⌉₊ : ℝ) := by
  have hc := Nat.le_ceil (8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale))
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ t.backgroundScale ^ 2 / 8 by positivity)
  have hid : (t.backgroundScale ^ 2 / 8) *
      (8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale)) =
        Real.log (1 / t.residualScale) := by
    field_simp [ne_of_gt t.backgroundScale_pos]
  rwa [hid] at hm

lemma warmup_size (t : Tuning) : 1 ≤ t.backgroundScale ^ 2 * (t.warmup : ℝ) := by
  have hc := t.warmup_log_threshold
  have hl := t.log_residual_bounds.1
  simp only [warmup, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hc, hl]

lemma warmup_pos (t : Tuning) : 1 ≤ t.warmup := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hz
  have hh := t.warmup_size
  norm_num [hz] at hh

lemma warmup_upper (t : Tuning) : (t.warmup : ℝ) ≤
    50 * t.logarithm / t.backgroundScale ^ 2 := by
  have hlog := t.log_residual_bounds
  have hL := t.logarithm_ge_one
  have hρ := t.backgroundScale_pos
  have hρ₁ := t.backgroundScale_le_one
  have hρ₂ : t.backgroundScale ^ 2 ≤ 1 := by nlinarith only [hρ.le, hρ₁]
  have hratio : 1 ≤ t.logarithm / t.backgroundScale ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    linarith only [hρ₂, hL]
  have harg : 0 ≤ 8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale) := by
    have hp : 0 ≤ Real.log (1 / t.residualScale) := by linarith only [hlog.1]
    positivity
  have hc := Nat.ceil_lt_add_one harg
  have hm := div_le_div_of_nonneg_right hlog.2 (sq_nonneg t.backgroundScale)
  simp only [warmup, Nat.cast_mul, Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at hc hm hratio ⊢
  nlinarith only [hc, hm, hratio]

lemma iteration_scale_ge_one (t : Tuning) :
    1 ≤ 2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm := by
  have hκ : t.κ ^ 8 ≤ 1 := by simpa using pow_le_pow_left₀ t.margin_pos.le t.margin_le 8
  have hr : t.r ^ 10 ≤ 1 := by simpa using pow_le_pow_left₀ t.ratio_pos.le t.ratio_le 10
  have hm := mul_le_mul_of_nonneg_left hr (pow_nonneg t.margin_pos.le 8)
  have hden : t.κ ^ 8 * t.r ^ 10 ≤ 1 := by nlinarith only [hm, hκ]
  have hdenpos : 0 < t.κ ^ 8 * t.r ^ 10 :=
    mul_pos (pow_pos t.margin_pos 8) (pow_pos t.ratio_pos 10)
  rw [show 2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm =
    2 ^ 140 * t.logarithm / (t.κ ^ 8 * t.r ^ 10) by ring]
  apply (le_div_iff₀ hdenpos).mpr
  have hL := mul_le_mul_of_nonneg_left t.logarithm_ge_one (show (0 : ℝ) ≤ 2 ^ 140 by positivity)
  have hnum : (1 : ℝ) ≤ 2 ^ 140 := by norm_num
  nlinarith only [hden, hL, hnum]

lemma iteration_mass_lower (t : Tuning) :
    2 ^ 140 * t.logarithm ≤ t.κ ^ 8 * t.r ^ 10 * (t.iterations : ℝ) := by
  have hc := Nat.le_ceil (2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm)
  have hd : 2 ^ 140 * t.logarithm / (t.κ ^ 8 * t.r ^ 10) ≤ (t.iterations : ℝ) := by
    calc
      _ = 2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm := by ring
      _ ≤ _ := hc
  have hm := (div_le_iff₀ (mul_pos (pow_pos t.margin_pos 8) (pow_pos t.ratio_pos 10))).mp hd
  nlinarith only [hm]

lemma iterations_upper (t : Tuning) : (t.iterations : ℝ) ≤
    2 * (2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm) := by
  have hb := t.iteration_scale_ge_one
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm by linarith only [hb])
  unfold iterations
  linarith only [hb, hc]

lemma contrast_logarithm (t : Tuning) : t.x * t.logarithm ≤ 1 := by
  have hl := Real.log_le_sub_one_of_pos (one_div_pos.mpr t.contrast_pos)
  have hL : t.logarithm ≤ 1 / t.x := by
    unfold logarithm
    linarith only [hl]
  have hh := (le_div_iff₀ t.contrast_pos).mp hL
  nlinarith only [hh]

lemma contrast_logarithm_sq (t : Tuning) : t.x * t.logarithm ^ 2 ≤ 4 := by
  have he := Real.add_one_le_exp (Real.log (1 / t.x) / 2)
  have hL : t.logarithm ≤ 2 * Real.exp (Real.log (1 / t.x) / 2) := by
    unfold logarithm
    linarith only [he]
  have hexp : Real.exp (Real.log (1 / t.x) / 2) ^ 2 = 1 / t.x := by
    rw [← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (Real.log (1 / t.x) / 2) = Real.log (1 / t.x) by ring]
    exact Real.exp_log (one_div_pos.mpr t.contrast_pos)
  have hL₀ : 0 ≤ t.logarithm := le_trans (by norm_num) t.logarithm_ge_one
  have hs : t.logarithm ^ 2 ≤ 4 * (1 / t.x) := by
    nlinarith only [hL, hL₀, hexp, Real.exp_nonneg (Real.log (1 / t.x) / 2)]
  have hm := mul_le_mul_of_nonneg_left hs t.contrast_pos.le
  have hid : t.x * (4 * (1 / t.x)) = 4 := by field_simp [ne_of_gt t.contrast_pos]
  rwa [hid] at hm

lemma scaled_contrast (t : Tuning) (m n c : ℕ) (hm : m ≤ 20) (hn : n ≤ 24) (hc : c ≤ 400) :
    2 ^ c * t.x ≤ t.κ ^ m * t.r ^ n := by
  have hκ := pow_le_pow_of_le_one t.margin_pos.le t.margin_le hm
  have hr := pow_le_pow_of_le_one t.ratio_pos.le t.ratio_le hn
  have hprod := mul_le_mul hκ hr (pow_nonneg t.ratio_pos.le 24) (pow_nonneg t.margin_pos.le m)
  have hpow : (2 : ℝ) ^ c ≤ 2 ^ (400 : ℕ) := pow_le_pow_right₀ (by norm_num) hc
  have hscale := mul_le_mul_of_nonneg_right hpow t.contrast_pos.le
  have hx := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (400 : ℕ))).mp t.contrast_le
  exact hscale.trans ((by simpa only [mul_comm t.x] using hx : (2 : ℝ) ^ 400 * t.x ≤ t.κ ^ 20 * t.r ^ 24).trans hprod)

lemma iteration_mass_upper (t : Tuning) :
    t.κ ^ 8 * t.r ^ 10 * (t.iterations : ℝ) ≤ 2 ^ 141 * t.logarithm := by
  have hh := t.iterations_upper
  have hid : 2 * (2 ^ 140 / (t.κ ^ 8 * t.r ^ 10) * t.logarithm) =
      2 ^ 141 * t.logarithm / (t.κ ^ 8 * t.r ^ 10) := by
    rw [show (141 : ℕ) = 140 + 1 by omega, pow_succ]
    ring
  rw [hid] at hh
  have hm := (le_div_iff₀ (mul_pos (pow_pos t.margin_pos 8) (pow_pos t.ratio_pos 10))).mp hh
  nlinarith only [hm]

lemma background_denominator (t : Tuning) :
    t.backgroundScale ^ 2 * (t.κ ^ 8 * t.r ^ 10) = t.κ ^ 12 * t.r ^ 16 / 2 ^ 80 := by
  norm_num [backgroundScale, stepScale]
  ring

set_option exponentiation.threshold 1024 in
lemma sharp_smallness (t : Tuning) : 16384 * t.residualScale * (t.iterations : ℝ) ≤
    t.backgroundScale ^ 2 * t.stepScale ^ 2 := by
  have hc := t.scaled_contrast 12 16 235 (by omega) (by omega) (by omega)
  have hcontrast : 16384 * (2 : ℝ) ^ 141 * t.x ≤
      t.backgroundScale ^ 2 * (t.κ ^ 8 * t.r ^ 10) := by
    rw [t.background_denominator]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (80 : ℕ))).mpr
    norm_num at hc ⊢
    nlinarith only [hc]
  have hb := DerivativePerceptronCounting.mass_sharp (t.κ ^ 8 * t.r ^ 10) (2 ^ 141)
    (t.iterations : ℝ) t.x t.logarithm t.backgroundScale
    (mul_pos (pow_pos t.margin_pos 8) (pow_pos t.ratio_pos 10)) (by positivity)
    t.contrast_pos.le t.iteration_mass_upper t.contrast_logarithm hcontrast
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg t.stepScale)
  unfold residualScale
  nlinarith only [hm]

set_option exponentiation.threshold 1024 in
lemma quadratic_smallness (t : Tuning) : t.residualScale * (t.iterations : ℝ) ^ 2 ≤ 1 / 16 := by
  have hc := t.scaled_contrast 16 20 288 (by omega) (by omega) (by omega)
  have hcontrast : 64 * ((2 : ℝ) ^ 141) ^ 2 * t.x ≤ (t.κ ^ 8 * t.r ^ 10) ^ 2 := by
    convert hc using 1 <;> ring
  have hb := DerivativePerceptronCounting.mass_quadratic (t.κ ^ 8 * t.r ^ 10) (2 ^ 141)
    (t.iterations : ℝ) t.x t.logarithm
    (mul_pos (pow_pos t.margin_pos 8) (pow_pos t.ratio_pos 10)) (by positivity)
    (Nat.cast_nonneg _) t.contrast_pos.le (le_trans (by norm_num) t.logarithm_ge_one)
    t.iteration_mass_upper t.contrast_logarithm_sq hcontrast
  have hh : t.stepScale ≤ 1 := t.stepScale_le.trans (by norm_num)
  have hh₂ : t.stepScale ^ 2 ≤ 1 := by nlinarith only [hh, t.stepScale_pos.le]
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg t.stepScale)
  unfold residualScale
  nlinarith only [hm, hh₂]

lemma warmup_dominated (t : Tuning) : 16777216 * (t.warmup : ℝ) ≤
    t.κ ^ 2 * t.r ^ 2 * (t.iterations : ℝ) := by
  have hκ := pow_le_pow_of_le_one t.margin_pos.le t.margin_le (by omega : 6 ≤ 8)
  have hr := pow_le_pow_of_le_one t.ratio_pos.le t.ratio_le (by omega : 8 ≤ 10)
  have hprod := mul_le_mul hκ hr (pow_nonneg t.ratio_pos.le 10) (pow_nonneg t.margin_pos.le 6)
  have hmul := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg t.iterations)
  have hmass := t.iteration_mass_lower.trans hmul
  have hid : (2 : ℝ) ^ 80 * t.backgroundScale ^ 2 * t.κ ^ 2 * t.r ^ 2 = t.κ ^ 6 * t.r ^ 8 := by
    norm_num [backgroundScale, stepScale]
    ring
  rw [← hid] at hmass
  have hwarm := (le_div_iff₀ (sq_pos_of_pos t.backgroundScale_pos)).mp t.warmup_upper
  have hL : 0 ≤ t.logarithm := le_trans (by norm_num) t.logarithm_ge_one
  have hh : t.backgroundScale ^ 2 * (16777216 * (t.warmup : ℝ)) ≤
      t.backgroundScale ^ 2 * (t.κ ^ 2 * t.r ^ 2 * (t.iterations : ℝ)) := by
    nlinarith only [hmass, hwarm, hL]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos t.backgroundScale_pos)).mp hh

lemma warmup_le_iterations (t : Tuning) : t.warmup ≤ t.iterations := by
  have hκ : t.κ ^ 2 ≤ 1 := by nlinarith only [t.margin_pos.le, t.margin_le]
  have hr : t.r ^ 2 ≤ 1 := by nlinarith only [t.ratio_pos.le, t.ratio_le]
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg t.κ)
  have hprod : t.κ ^ 2 * t.r ^ 2 ≤ 1 := by nlinarith only [hm, hκ]
  have hmul := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg t.iterations)
  have hd := t.warmup_dominated
  have hn : (0 : ℝ) ≤ t.warmup := Nat.cast_nonneg _
  have hh : (t.warmup : ℝ) ≤ t.iterations := by nlinarith only [hmul, hd, hn]
  exact Nat.cast_le.mp hh

lemma iterations_linear (t : Tuning) : 65536 ≤ t.κ ^ 2 * (t.iterations : ℝ) := by
  have hκ := pow_le_pow_of_le_one t.margin_pos.le t.margin_le (by omega : 2 ≤ 8)
  have hr : t.r ^ 10 ≤ 1 := by simpa using pow_le_pow_left₀ t.ratio_pos.le t.ratio_le 10
  have hm := mul_le_mul_of_nonneg_left hr (pow_nonneg t.margin_pos.le 8)
  have hprod : t.κ ^ 8 * t.r ^ 10 ≤ t.κ ^ 2 := by nlinarith only [hm, hκ]
  have hmul := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg t.iterations)
  have hmass := t.iteration_mass_lower
  have hL := mul_le_mul_of_nonneg_left t.logarithm_ge_one (show (0 : ℝ) ≤ 2 ^ 140 by positivity)
  nlinarith only [hmul, hmass, hL]

lemma cubic_smallness (t : Tuning) : 16384 * t.residualScale * (t.iterations : ℝ) ≤ t.κ ^ 2 := by
  have hh : t.stepScale ≤ 1 := t.stepScale_le.trans (by norm_num)
  have hh₂ : t.stepScale ^ 2 ≤ 1 := by nlinarith only [hh, t.stepScale_pos.le]
  have hrκ : t.backgroundScale ≤ t.κ := by
    have hhκ := t.stepScale_margin
    have hrh := t.backgroundScale_le
    linarith only [hhκ, hrh, t.margin_pos.le]
  have hrκ₂ : t.backgroundScale ^ 2 ≤ t.κ ^ 2 := by
    nlinarith only [hrκ, t.backgroundScale_pos.le, t.margin_pos.le]
  have hm := mul_le_mul_of_nonneg_left hh₂ (sq_nonneg t.backgroundScale)
  exact t.sharp_smallness.trans (by nlinarith only [hm, hrκ₂])

end Tuning

end LongTails.Proofs.DerivativePerceptronParameters
