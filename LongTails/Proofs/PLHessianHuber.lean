import Mathlib.Tactic

namespace OracleTemplate.PLHessian

noncomputable def hub (a b t : ℝ) : ℝ :=
  if t ≤ a then 0 else if t ≤ a + b then (t - a) ^ 2 / (2 * b) else t - a - b / 2

noncomputable def dhub (a b t : ℝ) : ℝ :=
  if t ≤ a then 0 else if t ≤ a + b then (t - a) / b else 1

section

variable {a b : ℝ}

lemma hub_nonneg (hb : 0 < b) (t : ℝ) : 0 ≤ hub a b t := by
  unfold hub
  split_ifs with h1 h2
  · exact le_rfl
  · positivity
  · linarith

lemma dhub_nonneg (hb : 0 < b) (t : ℝ) : 0 ≤ dhub a b t := by
  unfold dhub
  split_ifs with h1 h2
  · exact le_rfl
  · exact div_nonneg (by linarith) hb.le
  · norm_num

lemma dhub_le_one (hb : 0 < b) (t : ℝ) : dhub a b t ≤ 1 := by
  unfold dhub
  split_ifs with h1 h2
  · norm_num
  · rw [div_le_one hb]; linarith
  · exact le_rfl

lemma dhub_of_le (t : ℝ) (h : t ≤ a) : dhub a b t = 0 := by
  simp [dhub, h]

lemma hub_of_le (t : ℝ) (h : t ≤ a) : hub a b t = 0 := by
  simp [hub, h]

lemma dhub_of_ge (hb : 0 < b) (t : ℝ) (h : a + b ≤ t) : dhub a b t = 1 := by
  unfold dhub
  split_ifs with h1 h2
  · linarith
  · rw [div_eq_one_iff_eq hb.ne']; linarith
  · rfl

lemma hub_of_ge (hb : 0 < b) (t : ℝ) (h : a + b ≤ t) : hub a b t = t - a - b / 2 := by
  unfold hub
  split_ifs with h1 h2
  · linarith
  · have : t = a + b := le_antisymm h2 h
    subst this
    field_simp
    ring
  · rfl

lemma dhub_le_div (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) : dhub a b t ≤ t / a := by
  by_cases h : t ≤ a
  · rw [dhub_of_le t h]; positivity
  · have h1 := dhub_le_one (a := a) hb t
    have : 1 ≤ t / a := by rw [le_div_iff₀ ha]; linarith
    linarith

lemma hub_le_dhub_mul (ha : 0 ≤ a) (hb : 0 < b) (t : ℝ) :
    hub a b t ≤ dhub a b t * t := by
  unfold hub dhub
  split_ifs with h1 h2
  · simp
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hb]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 (not_le.1 h1).le)
      (by linarith : 0 ≤ t + a)) hb.le]
  · linarith

lemma hub_ge_line (hb : 0 < b) (y : ℝ) : y - a - b / 2 ≤ hub a b y := by
  unfold hub
  split_ifs with h1 h2
  · linarith
  · rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (y - a - b)]
  · exact le_rfl

lemma hub_le_sq (hb : 0 < b) (y : ℝ) : hub a b y ≤ (max (y - a) 0) ^ 2 / (2 * b) := by
  unfold hub
  split_ifs with h1 h2
  · positivity
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_left (by linarith), le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (y - a - b)]

lemma hub_tangent (hb : 0 < b) (x y : ℝ) :
    hub a b x + dhub a b x * (y - x) ≤ hub a b y := by
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  by_cases hx1 : x ≤ a
  · rw [hub_of_le x hx1, dhub_of_le x hx1]
    simpa using hub_nonneg (a := a) hb y
  by_cases hx2 : x ≤ a + b
  · have hh : hub a b x = (x - a) ^ 2 / (2 * b) := by simp [hub, hx1, hx2]
    have hd : dhub a b x = (x - a) / b := by simp [dhub, hx1, hx2]
    rw [hh, hd]
    have e : (x - a) ^ 2 / (2 * b) + (x - a) / b * (y - x) =
        ((y - a) ^ 2 - (y - x) ^ 2) / (2 * b) := by field_simp; ring
    rw [e]
    by_cases hy1 : y ≤ a
    · rw [hub_of_le y hy1, div_le_iff₀ hb2]
      nlinarith
    by_cases hy2 : y ≤ a + b
    · have : hub a b y = (y - a) ^ 2 / (2 * b) := by simp [hub, hy1, hy2]
      rw [this]
      apply div_le_div_of_nonneg_right _ hb2.le
      nlinarith [sq_nonneg (y - x)]
    · rw [hub_of_ge hb y (by linarith), div_le_iff₀ hb2]
      nlinarith
  · rw [dhub_of_ge hb x (by linarith), hub_of_ge hb x (by linarith)]
    have := hub_ge_line (a := a) hb y
    linarith

lemma hub_taylor (hb : 0 < b) (x y : ℝ) :
    hub a b y ≤ hub a b x + dhub a b x * (y - x) + (y - x) ^ 2 / (2 * b) := by
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  by_cases hx1 : x ≤ a
  · rw [hub_of_le x hx1, dhub_of_le x hx1]
    simp only [zero_mul, add_zero, zero_add]
    refine (hub_le_sq hb y).trans (div_le_div_of_nonneg_right ?_ hb2.le)
    rcases le_total (y - a) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (y - x)]
    · rw [max_eq_left h]; nlinarith
  by_cases hx2 : x ≤ a + b
  · have hh : hub a b x = (x - a) ^ 2 / (2 * b) := by simp [hub, hx1, hx2]
    have hd : dhub a b x = (x - a) / b := by simp [dhub, hx1, hx2]
    rw [hh, hd]
    have e : (x - a) ^ 2 / (2 * b) + (x - a) / b * (y - x) + (y - x) ^ 2 / (2 * b) =
        (y - a) ^ 2 / (2 * b) := by field_simp; ring
    rw [e]
    refine (hub_le_sq hb y).trans (div_le_div_of_nonneg_right ?_ hb2.le)
    rcases le_total (y - a) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (y - x)]
    · rw [max_eq_left h]
  · rw [dhub_of_ge hb x (by linarith), hub_of_ge hb x (by linarith)]
    by_cases hy1 : y ≤ a
    · rw [hub_of_le y hy1]
      have : 0 ≤ (y - a - b / 2) + (y - x) ^ 2 / (2 * b) := by
        rw [← sub_nonneg]
        have e : y - a - b / 2 + (y - x) ^ 2 / (2 * b) - 0 =
            ((x - y) ^ 2 + 2 * b * (y - a) - b ^ 2) / (2 * b) := by field_simp; ring
        rw [e]
        apply div_nonneg _ hb2.le
        nlinarith
      linarith
    by_cases hy2 : y ≤ a + b
    · have : hub a b y = (y - a) ^ 2 / (2 * b) := by simp [hub, hy1, hy2]
      rw [this]
      have e : x - a - b / 2 + 1 * (y - x) + (y - x) ^ 2 / (2 * b) - (y - a) ^ 2 / (2 * b) =
          ((x - a - b) * (x - a + b - 2 * (y - a))) / (2 * b) := by field_simp; ring
      have : 0 ≤ ((x - a - b) * (x - a + b - 2 * (y - a))) / (2 * b) := by
        apply div_nonneg _ hb2.le
        apply mul_nonneg <;> linarith
      linarith
    · rw [hub_of_ge hb y (by linarith)]
      have : 0 ≤ (y - x) ^ 2 / (2 * b) := by positivity
      linarith

lemma dhub_eq (hb : 0 < b) (t : ℝ) : dhub a b t = min 1 (max 0 ((t - a) / b)) := by
  unfold dhub
  split_ifs with h1 h2
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)]; simp
  · rw [max_eq_right (div_nonneg (by linarith) hb.le), min_eq_right]
    rw [div_le_one hb]; linarith
  · rw [max_eq_right (div_nonneg (by linarith) hb.le), min_eq_left]
    rw [le_div_iff₀ hb]; linarith

lemma dhub_lip (hb : 0 < b) {x y : ℝ} (hxy : x ≤ y) : dhub a b y - dhub a b x ≤ (y - x) / b := by
  have key : ∀ t, dhub a b t = min 1 (max 0 ((t - a) / b)) := by
    intro t
    unfold dhub
    split_ifs with h1 h2
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)]; simp
    · rw [max_eq_right (div_nonneg (by linarith) hb.le), min_eq_right]
      rw [div_le_one hb]; linarith
    · rw [max_eq_right (div_nonneg (by linarith) hb.le), min_eq_left]
      rw [le_div_iff₀ hb]; linarith
  rw [key, key]
  have h : (y - a) / b - (x - a) / b = (y - x) / b := by field_simp; ring
  have hm : max 0 ((y - a) / b) - max 0 ((x - a) / b) ≤ (y - a) / b - (x - a) / b ∨
      max 0 ((y - a) / b) - max 0 ((x - a) / b) ≤ 0 := by
    rcases le_total ((x - a) / b) 0 with h1 | h1 <;> rcases le_total ((y - a) / b) 0 with h2 | h2
    · right; simp [max_eq_left h1, max_eq_left h2]
    · left; rw [max_eq_left h1, max_eq_right h2]; linarith
    · right; rw [max_eq_right h1, max_eq_left h2]; linarith
    · left; rw [max_eq_right h1, max_eq_right h2]
  have hyx : 0 ≤ (y - x) / b := div_nonneg (by linarith) hb.le
  have hmono : max 0 ((x - a) / b) ≤ max 0 ((y - a) / b) := by
    apply max_le_max le_rfl
    apply div_le_div_of_nonneg_right (by linarith) hb.le
  rcases le_total 1 (max 0 ((x - a) / b)) with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans hmono)]; linarith
  · rw [min_eq_right h1]
    have := min_le_right 1 (max 0 ((y - a) / b))
    rcases hm with hm | hm <;> linarith

lemma dhub_mono (hb : 0 < b) {x y : ℝ} (hxy : x ≤ y) : dhub a b x ≤ dhub a b y := by
  rw [dhub_eq hb, dhub_eq hb]
  exact min_le_min le_rfl (max_le_max le_rfl (div_le_div_of_nonneg_right (by linarith) hb.le))

lemma hub_mono (hb : 0 < b) {x y : ℝ} (hxy : x ≤ y) : hub a b x ≤ hub a b y := by
  have h := hub_tangent (a := a) hb x y
  have := dhub_nonneg (a := a) hb x
  nlinarith

end

end OracleTemplate.PLHessian
