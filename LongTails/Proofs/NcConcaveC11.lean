import LongTails.Proofs.NcConcaveInstance

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveC11

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveGadgets
open LongTails.Proofs.NcConcaveInstance

def Model (f f' : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x y, |f y - f x - f' x * (y - x)| ≤ M * (y - x) ^ 2

lemma model_deriv_lip {f f' : ℝ → ℝ} {M : ℝ} (h : Model f f' M) (x y : ℝ) :
    |f' x - f' y| ≤ 2 * M * |x - y| := by
  have h1 := abs_le.mp (h x y)
  have h2 := abs_le.mp (h y x)
  have e : (f' y - f' x) * (y - x) = (f y - f x - f' x * (y - x)) + (f x - f y - f' y * (x - y)) := by
    ring
  have hb : |f' y - f' x| * |y - x| ≤ 2 * M * |y - x| ^ 2 := by
    rw [← abs_mul, e, sq_abs]
    have : (x - y) ^ 2 = (y - x) ^ 2 := by ring
    rw [abs_le]; constructor <;> linarith
  rcases eq_or_lt_of_le (abs_nonneg (y - x)) with h0 | h0
  · have : y = x := by
      have := h0.symm; rw [abs_eq_zero, sub_eq_zero] at this; exact this
    subst this; simp
  · rw [abs_sub_comm x y, abs_sub_comm (f' x)]
    have := le_of_mul_le_mul_right (by nlinarith : |f' y - f' x| * |y - x| ≤ 2 * M * |y - x| * |y - x|) h0
    exact this

lemma zeta_far_pos {θ x : ℝ} (hθ : 0 < θ) (hx : 2 * θ ≤ x) :
    zeta θ x = x - 3 * θ / 2 ∧ dzeta θ x = 1 := by
  have h1 : 1 ≤ x / θ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hθ]; linarith
  have h2 : -x / θ - 1 ≤ 0 := by
    have : 0 ≤ x / θ := div_nonneg (by linarith) hθ.le
    have : -x / θ = -(x / θ) := by ring
    linarith
  have hr : ramp (x / θ - 1) = x / θ - 1 - 1 / 2 := by
    simp only [ramp, show ¬ (x / θ - 1 ≤ 0) by linarith]
    rcases eq_or_lt_of_le h1 with h | h
    · rw [ite_eq_left h.symm.le, ← h]; norm_num
    · rw [ite_eq_right (show ¬ (x / θ - 1 ≤ 1) by linarith)]; simp
  have hl : ramp (-x / θ - 1) = 0 := by simp [ramp, h2]
  have hs1 : rampSlope (x / θ - 1) = 1 := by
    simp only [rampSlope]; rw [max_eq_right (by linarith), min_eq_left h1]
  have hs2 : rampSlope (-x / θ - 1) = 0 := by
    simp only [rampSlope]; rw [max_eq_left h2, min_eq_right (by norm_num)]
  constructor
  · simp only [zeta, rampR, rampL, hr, hl]; field_simp; ring
  · simp only [dzeta, hs1, hs2]; norm_num

lemma zeta_far_neg {θ x : ℝ} (hθ : 0 < θ) (hx : x ≤ -(2 * θ)) :
    zeta θ x = x + 3 * θ / 2 ∧ dzeta θ x = 1 := by
  have h1 : 1 ≤ -x / θ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hθ]; linarith
  have h2 : x / θ - 1 ≤ 0 := by
    have : x / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    linarith
  have hr : ramp (-x / θ - 1) = -x / θ - 1 - 1 / 2 := by
    simp only [ramp, show ¬ (-x / θ - 1 ≤ 0) by linarith]
    rcases eq_or_lt_of_le h1 with h | h
    · rw [ite_eq_left h.symm.le, ← h]; norm_num
    · rw [ite_eq_right (show ¬ (-x / θ - 1 ≤ 1) by linarith)]; simp
  have hl : ramp (x / θ - 1) = 0 := by simp [ramp, h2]
  have hs1 : rampSlope (-x / θ - 1) = 1 := by
    simp only [rampSlope]; rw [max_eq_right (by linarith), min_eq_left h1]
  have hs2 : rampSlope (x / θ - 1) = 0 := by
    simp only [rampSlope]; rw [max_eq_left h2, min_eq_right (by norm_num)]
  constructor
  · simp only [zeta, rampR, rampL, hr, hl]; field_simp; ring
  · simp only [dzeta, hs1, hs2]; norm_num

lemma zeta_near {θ x : ℝ} (hθ : 0 < θ) (hx : |x| ≤ 2 * θ) : |zeta θ x| ≤ θ / 2 := by
  have h := abs_le.mp hx
  have hb1 : ramp (x / θ - 1) ≤ 1 / 2 := by
    have : x / θ - 1 ≤ 1 := by rw [sub_le_iff_le_add, div_le_iff₀ hθ]; linarith
    simp only [ramp]; split_ifs <;> nlinarith
  have hb2 : ramp (-x / θ - 1) ≤ 1 / 2 := by
    have : -x / θ - 1 ≤ 1 := by rw [sub_le_iff_le_add, div_le_iff₀ hθ]; linarith
    simp only [ramp]; split_ifs <;> nlinarith
  have hn1 := rampR_nonneg θ x
  have hn2 := rampL_nonneg θ x
  simp only [rampR, rampL] at hn1 hn2
  simp only [zeta, rampR, rampL]
  rw [abs_mul, abs_of_pos hθ]
  have : |ramp (x / θ - 1) - ramp (-x / θ - 1)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  nlinarith

lemma dzeta_nonneg (θ x : ℝ) : 0 ≤ dzeta θ x := by
  simp only [dzeta]; linarith [rampSlope_nonneg (x / θ - 1), rampSlope_nonneg (-x / θ - 1)]

lemma dzeta_le_one {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : dzeta θ x ≤ 1 := by
  rcases le_total 0 x with h | h
  · have : -x / θ - 1 ≤ 0 := by
      have : 0 ≤ x / θ := div_nonneg h hθ.le
      have : -x / θ = -(x / θ) := by ring
      linarith
    have hs : rampSlope (-x / θ - 1) = 0 := by
      simp only [rampSlope]; rw [max_eq_left this, min_eq_right (by norm_num)]
    simp only [dzeta, hs, add_zero]; exact rampSlope_le_one _
  · have : x / θ - 1 ≤ 0 := by
      have : x / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hθ.le
      linarith
    have hs : rampSlope (x / θ - 1) = 0 := by
      simp only [rampSlope]; rw [max_eq_left this, min_eq_right (by norm_num)]
    simp only [dzeta, hs, zero_add]; exact rampSlope_le_one _

lemma dzeta_abs {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : |dzeta θ x| ≤ 1 := by
  rw [abs_of_nonneg (dzeta_nonneg θ x)]; exact dzeta_le_one hθ x

lemma zeta_lip {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) : |zeta θ x - zeta θ y| ≤ |x - y| := by
  have := lip_of_deriv (zeta_hasDerivAt hθ) (fun t => dzeta_abs hθ t) x y
  linarith

lemma zeta_E_abs {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    |zeta θ y - zeta θ x - dzeta θ x * (y - x)| ≤ 2 * |y - x| := by
  have h1 := zeta_lip hθ y x
  have h2 := dzeta_abs hθ x
  calc _ ≤ |zeta θ y - zeta θ x| + |dzeta θ x * (y - x)| := abs_sub _ _
    _ ≤ |y - x| + 1 * |y - x| := by
        rw [abs_mul]; exact add_le_add h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    _ = _ := by ring

lemma zeta_E_weight {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    |zeta θ x| * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| ≤ 3 * (y - x) ^ 2 := by
  have hm := zeta_model hθ x y
  have ha := zeta_E_abs hθ x y
  have hE0 := abs_nonneg (zeta θ y - zeta θ x - dzeta θ x * (y - x))
  have hsq : (y - x) ^ 2 = |y - x| ^ 2 := (sq_abs _).symm
  by_cases hx : |x| ≤ 2 * θ
  · have hz := zeta_near hθ hx
    calc _ ≤ θ / 2 * (1 / (2 * θ) * (y - x) ^ 2) := mul_le_mul hz hm hE0 (by positivity)
      _ = (y - x) ^ 2 / 4 := by field_simp; ring
      _ ≤ _ := by nlinarith [sq_nonneg (y - x)]
  · push Not at hx
    rcases lt_or_gt_of_ne (show x ≠ 0 by intro h; rw [h, abs_zero] at hx; linarith) with hneg | hpos
    · rw [abs_of_neg hneg] at hx
      obtain ⟨zx, dx⟩ := zeta_far_neg hθ (by linarith : x ≤ -(2 * θ))
      by_cases hy : y ≤ -(2 * θ)
      · obtain ⟨zy, -⟩ := zeta_far_neg hθ hy
        have : zeta θ y - zeta θ x - dzeta θ x * (y - x) = 0 := by rw [zx, zy, dx]; ring
        rw [this, abs_zero, mul_zero]; positivity
      · push Not at hy
        have hz : |zeta θ x| ≤ |y - x| + θ / 2 := by
          rw [zx, abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
        calc _ ≤ (|y - x| + θ / 2) * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| :=
              mul_le_mul_of_nonneg_right hz hE0
          _ = |y - x| * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| +
              θ / 2 * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| := by ring
          _ ≤ |y - x| * (2 * |y - x|) + θ / 2 * (1 / (2 * θ) * (y - x) ^ 2) :=
              add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
                (mul_le_mul_of_nonneg_left hm (by positivity))
          _ = 2 * |y - x| ^ 2 + (y - x) ^ 2 / 4 := by field_simp; ring
          _ ≤ _ := by rw [← hsq]; nlinarith [sq_nonneg (y - x)]
    · rw [abs_of_pos hpos] at hx
      obtain ⟨zx, dx⟩ := zeta_far_pos hθ (by linarith : 2 * θ ≤ x)
      by_cases hy : 2 * θ ≤ y
      · obtain ⟨zy, -⟩ := zeta_far_pos hθ hy
        have : zeta θ y - zeta θ x - dzeta θ x * (y - x) = 0 := by rw [zx, zy, dx]; ring
        rw [this, abs_zero, mul_zero]; positivity
      · push Not at hy
        have hz : |zeta θ x| ≤ |y - x| + θ / 2 := by
          rw [zx, abs_of_pos (by linarith), abs_of_neg (by linarith)]; linarith
        calc _ ≤ (|y - x| + θ / 2) * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| :=
              mul_le_mul_of_nonneg_right hz hE0
          _ = |y - x| * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| +
              θ / 2 * |zeta θ y - zeta θ x - dzeta θ x * (y - x)| := by ring
          _ ≤ |y - x| * (2 * |y - x|) + θ / 2 * (1 / (2 * θ) * (y - x) ^ 2) :=
              add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
                (mul_le_mul_of_nonneg_left hm (by positivity))
          _ = 2 * |y - x| ^ 2 + (y - x) ^ 2 / 4 := by field_simp; ring
          _ ≤ _ := by rw [← hsq]; nlinarith [sq_nonneg (y - x)]

lemma comp_zeta_model {θ : ℝ} (hθ : 0 < θ) {H H' : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hH : Model H H' M) (h0 : H' 0 = 0) :
    Model (fun t => H (zeta θ t)) (fun t => H' (zeta θ t) * dzeta θ t) (7 * M) := by
  intro x y
  set zx := zeta θ x
  set zy := zeta θ y
  set E := zy - zx - dzeta θ x * (y - x)
  have e : H zy - H zx - H' zx * dzeta θ x * (y - x) =
      (H zy - H zx - H' zx * (zy - zx)) + H' zx * E := by simp only [E]; ring
  rw [e]
  have h1 := hH zx zy
  have hl := zeta_lip hθ y x
  have hd : (zy - zx) ^ 2 ≤ (y - x) ^ 2 := by
    rw [← sq_abs, ← sq_abs (y - x)]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have h2 : |H' zx| ≤ 2 * M * |zx| := by
    have := model_deriv_lip hH zx 0
    rw [h0, sub_zero, sub_zero] at this; exact this
  have h3 := zeta_E_weight hθ x y
  calc _ ≤ |H zy - H zx - H' zx * (zy - zx)| + |H' zx * E| := abs_add_le _ _
    _ ≤ M * (y - x) ^ 2 + 2 * M * (3 * (y - x) ^ 2) := by
        apply add_le_add (h1.trans (mul_le_mul_of_nonneg_left hd hM))
        rw [abs_mul]
        calc |H' zx| * |E| ≤ 2 * M * |zx| * |E| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ = 2 * M * (|zx| * |E|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 7 * M * (y - x) ^ 2 := by ring

lemma rr_E_weight (x y : ℝ) :
    |rr x| * |rr y - rr x - drr x * (y - x)| ≤ 2 * (y - x) ^ 2 := by
  have hm := rr_model x y
  have hl := rr_lipschitz y x
  have hd := drr_abs x
  have hE : |rr y - rr x - drr x * (y - x)| ≤ 2 * |y - x| := by
    calc _ ≤ |rr y - rr x| + |drr x * (y - x)| := abs_sub _ _
      _ ≤ |y - x| + 1 * |y - x| := by
          rw [abs_mul]; exact add_le_add hl (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
      _ = _ := by ring
  have hE0 := abs_nonneg (rr y - rr x - drr x * (y - x))
  have hsq : (y - x) ^ 2 = |y - x| ^ 2 := (sq_abs _).symm
  rcases le_or_gt x 0 with hx | hx
  · by_cases hy : y ≤ 0
    · have : rr y - rr x - drr x * (y - x) = 0 := by
        rw [rr_cases x, rr_cases y, drr_cases x]; simp [hx, hy]
      rw [this, abs_zero, mul_zero]; positivity
    · push Not at hy
      have hr : |rr x| ≤ |y - x| := by
        rw [rr_cases x, ite_eq_left hx, abs_of_nonpos hx, abs_of_pos (by linarith)]; linarith
      calc _ ≤ |y - x| * (2 * |y - x|) := mul_le_mul hr hE hE0 (abs_nonneg _)
        _ = _ := by rw [hsq]; ring
  · by_cases hx1 : x ≤ 1
    · have hr : |rr x| ≤ 1 := by
        rw [rr_cases x, ite_eq_right (by linarith), ite_eq_left hx1, abs_le]; constructor <;> nlinarith
      calc _ ≤ 1 * (1 * (y - x) ^ 2) := mul_le_mul hr hm hE0 (by norm_num)
        _ ≤ _ := by nlinarith [sq_nonneg (y - x)]
    · push Not at hx1
      by_cases hy : 1 ≤ y
      · have : rr y - rr x - drr x * (y - x) = 0 := by
          rw [rr_cases x, rr_cases y, drr_cases x]
          simp [show ¬ x ≤ 0 by linarith, show ¬ x ≤ 1 by linarith,
            show ¬ y ≤ 0 by linarith]
          rcases eq_or_lt_of_le hy with h | h
          · subst h; simp
          · simp [show ¬ y ≤ 1 by linarith]
        rw [this, abs_zero, mul_zero]; positivity
      · push Not at hy
        have hr : |rr x| ≤ |y - x| := by
          rw [rr_cases x, ite_eq_right (by linarith), ite_eq_right (by linarith), abs_of_neg (by linarith),
            abs_of_neg (by linarith)]; linarith
        calc _ ≤ |y - x| * (2 * |y - x|) := mul_le_mul hr hE hE0 (abs_nonneg _)
          _ = _ := by rw [hsq]; ring

lemma rrsq_model : Model (fun t => rr t ^ 2) (fun t => 2 * rr t * drr t) 5 := by
  intro x y
  have e : rr y ^ 2 - rr x ^ 2 - 2 * rr x * drr x * (y - x) =
      (rr y - rr x) ^ 2 + 2 * (rr x * (rr y - rr x - drr x * (y - x))) := by ring
  rw [e]
  have h1 : (rr y - rr x) ^ 2 ≤ (y - x) ^ 2 := by
    rw [← sq_abs, ← sq_abs (y - x)]; exact pow_le_pow_left₀ (abs_nonneg _) (rr_lipschitz y x) 2
  have h2 := rr_E_weight x y
  rw [← abs_mul] at h2
  calc _ ≤ |(rr y - rr x) ^ 2| + |2 * (rr x * (rr y - rr x - drr x * (y - x)))| := abs_add_le _ _
    _ ≤ (y - x) ^ 2 + 2 * (2 * (y - x) ^ 2) := by
        rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

lemma sq_model : Model (fun t => t ^ 2) (fun t => 2 * t) 1 := by
  intro x y
  have e : y ^ 2 - x ^ 2 - 2 * x * (y - x) = (y - x) ^ 2 := by ring
  rw [e, abs_of_nonneg (sq_nonneg _), one_mul]

lemma nu_model' : Model nu dnu 3 := nu_model

lemma huber_model' {c : ℝ} (hc : 0 < c) : Model (huber c) (dhuber c) 1 := by
  intro x y
  have h := huber_model hc x y
  rw [abs_of_nonneg h.1, one_mul]; exact h.2

lemma dhuber_zero (c : ℝ) : dhuber c 0 = 0 := by simp [dhuber]

lemma dnu_zero : dnu 0 = 0 := dnu_of_nonpos le_rfl

lemma rrsq_deriv_zero : 2 * rr 0 * drr 0 = 0 := by rw [rr_zero]; ring

lemma nuz_model {θ : ℝ} (hθ : 0 < θ) :
    Model (fun t => nu (zeta θ t)) (fun t => dnu (zeta θ t) * dzeta θ t) 21 := by
  have h := comp_zeta_model hθ (by norm_num) nu_model' dnu_zero
  intro x y; have := h x y; linarith

lemma sqz_model {θ : ℝ} (hθ : 0 < θ) :
    Model (fun t => zeta θ t ^ 2) (fun t => 2 * zeta θ t * dzeta θ t) 7 := by
  have h := comp_zeta_model hθ (by norm_num) sq_model (by norm_num)
  intro x y; have := h x y; simp only [mul_one] at this; linarith

lemma rrsqz_model {θ : ℝ} (hθ : 0 < θ) :
    Model (fun t => rr (zeta θ t) ^ 2) (fun t => 2 * rr (zeta θ t) * drr (zeta θ t) * dzeta θ t) 35 := by
  have h := comp_zeta_model hθ (by norm_num) rrsq_model rrsq_deriv_zero
  intro x y; have := h x y; norm_num at this ⊢; linarith

lemma huberz_model {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    Model (fun t => huber c (zeta θ t)) (fun t => dhuber c (zeta θ t) * dzeta θ t) 7 := by
  have h := comp_zeta_model hθ (by norm_num) (huber_model' hc) (dhuber_zero c)
  intro x y; have := h x y; linarith

lemma rrz_model {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (x y : ℝ) :
    2 * θ * |rr (zeta θ y) - rr (zeta θ x) - drr (zeta θ x) * dzeta θ x * (y - x)| ≤
      3 * (y - x) ^ 2 := by
  set zx := zeta θ x
  set zy := zeta θ y
  have e : rr zy - rr zx - drr zx * dzeta θ x * (y - x) =
      (rr zy - rr zx - drr zx * (zy - zx)) + drr zx * (zy - zx - dzeta θ x * (y - x)) := by ring
  rw [e]
  have h1 := rr_model zx zy
  have hl := zeta_lip hθ y x
  have hd : (zy - zx) ^ 2 ≤ (y - x) ^ 2 := by
    rw [← sq_abs, ← sq_abs (y - x)]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have h2 := zeta_model hθ x y
  have h3 := drr_abs zx
  have hb : |(rr zy - rr zx - drr zx * (zy - zx)) + drr zx * (zy - zx - dzeta θ x * (y - x))| ≤
      (y - x) ^ 2 + 1 / (2 * θ) * (y - x) ^ 2 := by
    calc _ ≤ |rr zy - rr zx - drr zx * (zy - zx)| + |drr zx * (zy - zx - dzeta θ x * (y - x))| :=
          abs_add_le _ _
      _ ≤ (y - x) ^ 2 + 1 * (1 / (2 * θ) * (y - x) ^ 2) := by
          apply add_le_add (by linarith)
          rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  calc _ ≤ 2 * θ * ((y - x) ^ 2 + 1 / (2 * θ) * (y - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * θ * (y - x) ^ 2 + (y - x) ^ 2 := by field_simp
    _ ≤ _ := by nlinarith [sq_nonneg (y - x)]

noncomputable def betaS (θ s t : ℝ) : ℝ := dzeta θ s * t + (1 - dzeta θ s) * zeta θ t

noncomputable def betaT (θ s t : ℝ) : ℝ := zeta θ s + (s - zeta θ s) * dzeta θ t

lemma beta_model {θ : ℝ} (hθ : 0 < θ) (s t s' t' : ℝ) :
    |beta θ s' t' - beta θ s t - betaS θ s t * (s' - s) - betaT θ s t * (t' - t)| ≤
      3 * ((s' - s) ^ 2 + (t' - t) ^ 2) := by
  have e : beta θ s' t' - beta θ s t - betaS θ s t * (s' - s) - betaT θ s t * (t' - t) =
      (t - zeta θ t) * (zeta θ s' - zeta θ s - dzeta θ s * (s' - s)) +
      (s - zeta θ s) * (zeta θ t' - zeta θ t - dzeta θ t * (t' - t)) +
      (zeta θ s' - zeta θ s) * (t' - t) + (s' - s) * (zeta θ t' - zeta θ t) -
      (zeta θ s' - zeta θ s) * (zeta θ t' - zeta θ t) := by
    simp only [beta, betaS, betaT]; ring
  rw [e]
  have a1 := zeta_sub_le (θ := θ) (t := t) hθ
  have a2 := zeta_sub_le (θ := θ) (t := s) hθ
  rw [abs_sub_comm] at a1 a2
  have m1 := zeta_model hθ s s'
  have m2 := zeta_model hθ t t'
  have l1 := zeta_lip hθ s' s
  have l2 := zeta_lip hθ t' t
  have p1 : |(t - zeta θ t) * (zeta θ s' - zeta θ s - dzeta θ s * (s' - s))| ≤ (s' - s) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ 2 * θ * (1 / (2 * θ) * (s' - s) ^ 2) := mul_le_mul a1 m1 (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have p2 : |(s - zeta θ s) * (zeta θ t' - zeta θ t - dzeta θ t * (t' - t))| ≤ (t' - t) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ 2 * θ * (1 / (2 * θ) * (t' - t) ^ 2) := mul_le_mul a2 m2 (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have p3 : |(zeta θ s' - zeta θ s) * (t' - t)| ≤ |s' - s| * |t' - t| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right l1 (abs_nonneg _)
  have p4 : |(s' - s) * (zeta θ t' - zeta θ t)| ≤ |s' - s| * |t' - t| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left l2 (abs_nonneg _)
  have p5 : |(zeta θ s' - zeta θ s) * (zeta θ t' - zeta θ t)| ≤ |s' - s| * |t' - t| := by
    rw [abs_mul]; exact mul_le_mul l1 l2 (abs_nonneg _) (abs_nonneg _)
  have hc : |s' - s| * |t' - t| ≤ ((s' - s) ^ 2 + (t' - t) ^ 2) / 2 := by
    rw [← sq_abs (s' - s), ← sq_abs (t' - t)]; nlinarith [sq_nonneg (|s' - s| - |t' - t|)]
  have q1 := abs_le.mp p1; have q2 := abs_le.mp p2; have q3 := abs_le.mp p3
  have q4 := abs_le.mp p4; have q5 := abs_le.mp p5
  rw [abs_le]; constructor <;> linarith

noncomputable def betaRB (θ b x : ℝ) : ℝ := dzeta θ b * (rr x - rr (zeta θ x)) + rr (zeta θ x)

noncomputable def betaRX (θ b x : ℝ) : ℝ :=
  zeta θ b * drr x + (b - zeta θ b) * (drr (zeta θ x) * dzeta θ x)

lemma betaR_model {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (B : ℝ) (b x b' x' : ℝ) (hb : |b| ≤ B) :
    |betaR θ b' x' - betaR θ b x - betaRB θ b x * (b' - b) - betaRX θ b x * (x' - x)| ≤
      3 * (b' - b) ^ 2 + (B + 5) * (x' - x) ^ 2 := by
  have e : betaR θ b' x' - betaR θ b x - betaRB θ b x * (b' - b) - betaRX θ b x * (x' - x) =
      (rr x - rr (zeta θ x)) * (zeta θ b' - zeta θ b - dzeta θ b * (b' - b)) +
      zeta θ b * (rr x' - rr x - drr x * (x' - x)) +
      (b - zeta θ b) * (rr (zeta θ x') - rr (zeta θ x) - drr (zeta θ x) * dzeta θ x * (x' - x)) +
      (zeta θ b' - zeta θ b) * ((rr x' - rr x) - (rr (zeta θ x') - rr (zeta θ x))) +
      (b' - b) * (rr (zeta θ x') - rr (zeta θ x)) := by
    simp only [betaR, betaRB, betaRX]; ring
  rw [e]
  have a1 : |rr x - rr (zeta θ x)| ≤ 2 * θ := by
    have := rr_lipschitz x (zeta θ x)
    have h2 := zeta_sub_le (θ := θ) (t := x) hθ
    rw [abs_sub_comm] at h2; linarith
  have a2 := zeta_sub_le (θ := θ) (t := b) hθ
  rw [abs_sub_comm] at a2
  have m1 := zeta_model hθ b b'
  have m2 := rr_model x x'
  have m3 := rrz_model hθ hθ1 x x'
  have hzb : |zeta θ b| ≤ B := by
    have h0 := zeta_lip hθ b 0
    have : zeta θ 0 = 0 := zeta_small hθ (by simp [hθ.le])
    rw [this, sub_zero, sub_zero] at h0; linarith
  have l1 := zeta_lip hθ b' b
  have lx1 := rr_lipschitz x' x
  have lx2 : |rr (zeta θ x') - rr (zeta θ x)| ≤ |x' - x| :=
    (rr_lipschitz _ _).trans (zeta_lip hθ x' x)
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have p1 : |(rr x - rr (zeta θ x)) * (zeta θ b' - zeta θ b - dzeta θ b * (b' - b))| ≤ (b' - b) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ 2 * θ * (1 / (2 * θ) * (b' - b) ^ 2) := mul_le_mul a1 m1 (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have p2 : |zeta θ b * (rr x' - rr x - drr x * (x' - x))| ≤ B * (x' - x) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ B * (1 * (x' - x) ^ 2) := mul_le_mul hzb m2 (abs_nonneg _) hB
      _ = _ := by ring
  have p3 : |(b - zeta θ b) * (rr (zeta θ x') - rr (zeta θ x) - drr (zeta θ x) * dzeta θ x * (x' - x))| ≤
      3 * (x' - x) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ 2 * θ * |rr (zeta θ x') - rr (zeta θ x) - drr (zeta θ x) * dzeta θ x * (x' - x)| :=
          mul_le_mul_of_nonneg_right a2 (abs_nonneg _)
      _ ≤ _ := m3
  have p4 : |(zeta θ b' - zeta θ b) * ((rr x' - rr x) - (rr (zeta θ x') - rr (zeta θ x)))| ≤
      |b' - b| * (2 * |x' - x|) := by
    rw [abs_mul]
    apply mul_le_mul l1 _ (abs_nonneg _) (abs_nonneg _)
    calc _ ≤ |rr x' - rr x| + |rr (zeta θ x') - rr (zeta θ x)| := abs_sub _ _
      _ ≤ _ := by linarith
  have p5 : |(b' - b) * (rr (zeta θ x') - rr (zeta θ x))| ≤ |b' - b| * |x' - x| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left lx2 (abs_nonneg _)
  have hc : |b' - b| * |x' - x| ≤ ((b' - b) ^ 2 + (x' - x) ^ 2) / 2 := by
    rw [← sq_abs (b' - b), ← sq_abs (x' - x)]; nlinarith [sq_nonneg (|b' - b| - |x' - x|)]
  have q1 := abs_le.mp p1; have q2 := abs_le.mp p2; have q3 := abs_le.mp p3
  have q4 := abs_le.mp p4; have q5 := abs_le.mp p5
  rw [abs_le]; constructor <;> linarith

lemma omega_scaled_model {θ c : ℝ} (hθ : 0 < θ) (hc : 0 ≤ c) (x y : ℝ) :
    |c * θ * omega θ y - c * θ * omega θ x - c * θ * domega θ x * (y - x)| ≤ c * (y - x) ^ 2 := by
  have h := omega_model hθ x y
  have e : c * θ * omega θ y - c * θ * omega θ x - c * θ * domega θ x * (y - x) =
      c * θ * (omega θ y - omega θ x - domega θ x * (y - x)) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg h.1]
  calc _ ≤ c * θ * (1 / θ * (y - x) ^ 2) := mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = _ := by field_simp

end LongTails.Proofs.NcConcaveC11
