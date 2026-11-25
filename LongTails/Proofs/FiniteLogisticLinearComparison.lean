import LongTails.Proofs.SoftQuadraticDynamics

namespace LongTails.Proofs.FiniteLogisticLinearComparison

open SoftQuadraticDynamics

structure Scores where
  background : ℝ
  residual : ℝ
  first : ℝ

noncomputable def mass (s : Scores) : ℝ :=
  2 * weight (s.background + s.residual) + weight (-s.background + s.residual) +
  2 * weight (s.first + s.residual) + weight (-s.first + s.residual)

noncomputable def step (h μ : ℝ) (s : Scores) : Scores :=
  ⟨s.background + h * (2 * weight (s.background + s.residual) - weight (-s.background + s.residual)),
   s.residual + h * μ ^ 2 * mass s,
   s.first + (h / 16384) * (2 * weight (s.first + s.residual) - weight (-s.first + s.residual))⟩

noncomputable def path (h μ : ℝ) : ℕ → Scores
  | 0 => ⟨0, 0, 0⟩
  | k + 1 => step h μ (path h μ k)

def Separates (s : Scores) : Prop :=
  0 < s.background + s.residual ∧ 0 < -s.background + s.residual ∧
    0 < s.first + s.residual ∧ 0 < -s.first + s.residual

private lemma mass_bounds (s : Scores) : 0 ≤ mass s ∧ mass s ≤ 6 := by
  unfold mass
  constructor
  · linarith [weight_pos (s.background + s.residual), weight_pos (-s.background + s.residual),
      weight_pos (s.first + s.residual), weight_pos (-s.first + s.residual)]
  · linarith [weight_le_one (s.background + s.residual), weight_le_one (-s.background + s.residual),
      weight_le_one (s.first + s.residual), weight_le_one (-s.first + s.residual)]

lemma residual_bounds {h μ : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    0 ≤ (path h μ k).residual ∧ (path h μ k).residual ≤ 6 * k * (h * μ ^ 2) := by
  induction k with
  | zero => simp [path]
  | succ k ih =>
    let s := path h μ k
    have hs := mul_nonneg hh (sq_nonneg μ)
    change 0 ≤ s.residual + h * μ ^ 2 * mass s ∧ s.residual + h * μ ^ 2 * mass s ≤ _
    change 0 ≤ s.residual ∧ s.residual ≤ _ at ih
    push_cast
    exact ⟨add_nonneg ih.1 (mul_nonneg hs (mass_bounds s).1), by
      linarith [ih.2, mul_le_mul_of_nonneg_left (mass_bounds s).2 hs]⟩

private lemma weight_near_zero {x : ℝ} (hx : |x| ≤ Real.log (3 / 2)) :
    2 / 5 ≤ weight x ∧ weight x ≤ 3 / 5 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hu' : Real.exp x ≤ 3 / 2 := (Real.exp_le_exp.mpr hu).trans_eq
    (Real.exp_log (by norm_num))
  have hl' : (2 / 3 : ℝ) ≤ Real.exp x := by
    have h' := Real.exp_le_exp.mpr hl
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h'
    norm_num at h' ⊢
    exact h'
  unfold weight
  constructor
  · apply (le_div_iff₀ (by positivity)).2; linarith
  · apply (div_le_iff₀ (by positivity)).2; linarith

lemma small_step_failure {h μ : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 2000) (k : ℕ)
    (hk : 1048576 * k * μ ^ 2 ≤ 1) : (path h μ k).residual ≤ (path h μ k).first := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    push_cast at hk
    let s := path h μ k
    have hk' : 1048576 * k * μ ^ 2 ≤ 1 := by nlinarith [sq_nonneg μ]
    have prev : s.residual ≤ s.first := ih hk'
    obtain ⟨hy, hy'⟩ := residual_bounds (μ := μ) hh k
    change 0 ≤ s.residual at hy
    change s.residual ≤ _ at hy'
    have hkm := mul_nonneg (Nat.cast_nonneg k (α := ℝ)) (sq_nonneg μ)
    have hySmall : s.residual ≤ 1 / 64 := by
      nlinarith [mul_le_mul_of_nonneg_right hh' hkm]
    have hnoise : h * μ ^ 2 * mass s ≤ h / 131072 := by
      have hb : 6 * μ ^ 2 ≤ 1 / 131072 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb hh,
        mul_le_mul_of_nonneg_left (mass_bounds s).2 (mul_nonneg hh (sq_nonneg μ))]
    change s.residual + h * μ ^ 2 * mass s ≤
      s.first + h / 16384 * (2 * weight (s.first + s.residual) - weight (-s.first + s.residual))
    by_cases far : s.residual + h / 8192 ≤ s.first
    · have hg : -1 ≤ 2 * weight (s.first + s.residual) - weight (-s.first + s.residual) := by
        linarith [weight_pos (s.first + s.residual), weight_le_one (-s.first + s.residual)]
      nlinarith [mul_le_mul_of_nonneg_left hg hh]
    · have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      norm_num at hl
      have h₁ := weight_near_zero (x := s.first + s.residual) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have h₂ := weight_near_zero (x := -s.first + s.residual) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hg : 1 / 5 ≤ 2 * weight (s.first + s.residual) - weight (-s.first + s.residual) := by
        linarith [h₁.1,h₂.2]
      nlinarith [mul_le_mul_of_nonneg_left hg hh]

private lemma weight_tail {x b : ℝ} (hx : b ≤ x) : weight x ≤ Real.exp (-b) := by
  unfold weight
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (by linarith [Real.exp_le_exp.mpr hx])

private lemma weight_reflect (x : ℝ) : weight (-x) = 1 - weight x := by
  unfold weight
  rw [Real.exp_neg]
  field_simp [ne_of_gt (Real.exp_pos x), ne_of_gt (by positivity : 0 < 1 + Real.exp x)]
  ring

private noncomputable def slack (x y : ℝ) : ℝ := 2 * weight (x + y) + weight (x - y)

private lemma slack_nonneg (x y : ℝ) : 0 ≤ slack x y := by
  unfold slack
  linarith [(weight_pos (x + y)).le, (weight_pos (x - y)).le]

private lemma slack_upper {x y b : ℝ} (h : b ≤ x - |y|) :
    slack x y ≤ 3 * Real.exp (-b) := by
  unfold slack
  linarith [weight_tail (x := x + y) (b := b) (by linarith [neg_le_abs y]),
    weight_tail (x := x - y) (b := b) (by linarith [le_abs_self y])]

private lemma slack_small {x y h : ℝ} (hh : 2000 ≤ h) (hx : h / 4 ≤ x)
    (hy : |y| ≤ h / 100) : slack x y ≤ 1 / 100 := by
  have he := Real.add_one_le_exp (h / 5)
  have ht := slack_upper (x := x) (y := y) (b := h / 5) (by linarith)
  rw [Real.exp_neg, ← div_eq_mul_inv] at ht
  exact ht.trans ((div_le_iff₀ (Real.exp_pos _)).2 (by linarith))

private lemma slack_dominates {x₁ y₁ x₂ y₂ h : ℝ} (hh : 2000 ≤ h)
    (h₁ : x₁ + |y₁| ≤ 9 * h / 20) (h₂ : 11 * h / 20 ≤ x₂ - |y₂|) :
    2 * slack x₂ y₂ ≤ slack x₁ y₁ := by
  have he := Real.add_one_le_exp (h / 10)
  have hp : 1 ≤ Real.exp (9 * h / 20) := Real.one_le_exp (by linarith)
  have hw : Real.exp (-(9 * h / 20)) / 2 ≤ weight (x₁ - y₁) := by
    rw [Real.exp_neg]
    unfold weight
    rw [← one_div, div_div]
    apply one_div_le_one_div_of_le (by positivity)
    have hle := Real.exp_le_exp.mpr
      (show x₁ - y₁ ≤ 9 * h / 20 by linarith [neg_le_abs y₁])
    linarith
  have hr : 12 * Real.exp (-(11 * h / 20)) ≤ Real.exp (-(9 * h / 20)) := by
    rw [show -(9 * h / 20) = -(11 * h / 20) + h / 10 by ring, Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left (show (12 : ℝ) ≤ Real.exp (h / 10) by linarith)
      (Real.exp_pos (-(11 * h / 20))).le]
  have hf := slack_upper h₂
  have hnear : weight (x₁ - y₁) ≤ slack x₁ y₁ := by
    unfold slack; linarith [weight_pos (x₁ + y₁)]
  linarith

private lemma plus_move (h μ : ℝ) (s : Scores) :
    (step h μ s).background = s.background - h + h * slack s.background s.residual := by
  unfold step slack
  rw [show -s.background + s.residual = -(s.background - s.residual) by ring, weight_reflect]
  ring

private lemma minus_move (h μ : ℝ) (s : Scores) :
    (step h μ s).background = s.background + 2 * h - h * slack (-s.background) (-s.residual) := by
  unfold step slack
  rw [show -s.background + -s.residual = -(s.background + s.residual) by ring,
    show -s.background - -s.residual = -s.background + s.residual by ring, weight_reflect]
  ring

private lemma cycle_bounds {h μ : ℝ} (hh : 2000 ≤ h) (x : Scores)
    (hlo : h / 3 ≤ x.background) (hhi : x.background ≤ 2 * h / 3)
    (h₀ : |x.residual| ≤ h / 100) (h₁ : |(step h μ x).residual| ≤ h / 100)
    (h₂ : |(step h μ (step h μ x)).residual| ≤ h / 100) :
    let x₁ := step h μ x
    let x₂ := step h μ x₁
    let x₃ := step h μ x₂
    x₁.background ≤ -h / 4 ∧ h ≤ x₂.background ∧
      h / 3 ≤ x₃.background ∧ x₃.background ≤ 2 * h / 3 := by
  let x₁ := step h μ x
  let x₂ := step h μ x₁
  let x₃ := step h μ x₂
  let a := slack x.background x.residual
  let b := slack (-x₁.background) (-x₁.residual)
  let c := slack x₂.background x₂.residual
  have ha : a ≤ 1 / 100 := slack_small hh (by linarith) h₀
  have ha' : 0 ≤ a := slack_nonneg ..
  have e₁ : x₁.background = x.background - h + h * a := plus_move ..
  have up₁ : x₁.background ≤ -h / 4 := by
    linarith [mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ h)]
  have hb : b ≤ 1 / 100 := slack_small hh (by linarith) (by simpa [x₁] using h₁)
  have hb' : 0 ≤ b := slack_nonneg ..
  have e₂ : x₂.background = x₁.background + 2 * h - h * b := minus_move ..
  have lo₂ : h ≤ x₂.background := by
    linarith [mul_nonneg (by linarith : 0 ≤ h) ha',
      mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ h)]
  have hc : c ≤ 1 / 100 := slack_small hh (by linarith) h₂
  have hc' : 0 ≤ c := slack_nonneg ..
  have e₃ : x₃.background = x.background + h * (a - b + c) := by
    rw [show x₃.background = x₂.background - h + h * c from plus_move .., e₂, e₁]
    ring
  have hy₁ : |-x₁.residual| ≤ h / 100 := by simpa [x₁] using h₁
  change |x₂.residual| ≤ _ at h₂
  refine ⟨up₁, lo₂, ?_, ?_⟩
  · by_cases hmid : 2 * h / 5 ≤ x.background
    · linarith [mul_nonneg (by linarith : 0 ≤ h) ha', mul_nonneg (by linarith : 0 ≤ h) hc',
        mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ h)]
    · have hd : 2 * b ≤ a := slack_dominates hh (by linarith)
          (by linarith [mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ h)])
      linarith [mul_nonneg (by linarith : 0 ≤ h) (show 0 ≤ a - b + c by linarith)]
  · by_cases hmid : x.background ≤ 3 * h / 5
    · linarith [mul_nonneg (by linarith : 0 ≤ h) hb',
        mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ h),
        mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ h)]
    · have hd : 2 * a ≤ b := slack_dominates hh
          (by linarith [mul_nonneg (by linarith : 0 ≤ h) ha']) (by linarith)
      have hd' : 2 * c ≤ b := slack_dominates hh
          (by linarith [mul_nonneg (by linarith : 0 ≤ h) ha']) (by linarith)
      linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ h)
        (show a - b + c ≤ 0 by linarith)]

private lemma path_residual_small {h μ : ℝ} (hh : 0 ≤ h) (k : ℕ)
    (hk : 600 * (k : ℝ) * μ ^ 2 ≤ 1) : |(path h μ k).residual| ≤ h / 100 := by
  obtain ⟨hy, hy'⟩ := residual_bounds (μ := μ) hh k
  rw [abs_of_nonneg hy]
  linarith [mul_le_mul_of_nonneg_left hk hh]

private lemma cycle_start {h μ : ℝ} (hh : 2000 ≤ h) (j : ℕ)
    (hj : 600 * (3 * (j : ℝ) + 1) * μ ^ 2 ≤ 1) :
    h / 3 ≤ (path h μ (3 * j + 1)).background ∧
      (path h μ (3 * j + 1)).background ≤ 2 * h / 3 := by
  induction j with
  | zero =>
    norm_num [path, step, weight]
    constructor <;> linarith
  | succ j ih =>
    push_cast at hj
    obtain ⟨hl, hu⟩ := ih (by linarith [sq_nonneg μ])
    have hs (a : ℕ) (ha : a ≤ 3) : |(path h μ (3 * j + a)).residual| ≤ h / 100 := by
      apply path_residual_small (by linarith)
      push_cast
      have ha' : (a : ℝ) ≤ 3 := by exact_mod_cast ha
      linarith [mul_le_mul_of_nonneg_right ha' (sq_nonneg μ), sq_nonneg μ]
    have hb := cycle_bounds hh (path h μ (3 * j + 1)) hl hu (hs 1 (by decide))
      (hs 2 (by decide)) (hs 3 (by decide))
    rw [show 3 * (j + 1) + 1 = 3 * j + 1 + 1 + 1 + 1 by omega]
    exact hb.2.2

private lemma large_step_failure {h μ : ℝ} (hh : 2000 ≤ h) (k : ℕ)
    (hk : 2400 * (k : ℝ) * μ ^ 2 ≤ 1) : ¬Separates (path h μ k) := by
  cases k with
  | zero => simp [Separates, path]
  | succ k =>
    let j := k / 3
    have hcut : 3 * j ≤ k := by dsimp [j]; omega
    have hcut' : 3 * (j : ℝ) ≤ k := by exact_mod_cast hcut
    push_cast at hk
    have hs (a : ℕ) (ha : a ≤ 3) : 600 * ((3 * j + a : ℕ) : ℝ) * μ ^ 2 ≤ 1 := by
      have ha' : (a : ℝ) ≤ 3 := by exact_mod_cast ha
      push_cast
      have hf : 600 * (3 * (j : ℝ) + a) ≤ 2400 * (k + 1) := by
        linarith [Nat.cast_nonneg k (α := ℝ)]
      linarith [mul_le_mul_of_nonneg_right hf (sq_nonneg μ)]
    obtain ⟨hl, hu⟩ := cycle_start hh (μ := μ) j (by simpa using hs 1 (by decide))
    have hy (a : ℕ) (ha : a ≤ 3) := path_residual_small (h := h) (by linarith)
      (3 * j + a) (hs a ha)
    have hb := cycle_bounds hh (path h μ (3 * j + 1)) hl hu (hy 1 (by decide))
      (hy 2 (by decide)) (hy 3 (by decide))
    change (path h μ (3 * j + 2)).background ≤ -h / 4 ∧
      h ≤ (path h μ (3 * j + 3)).background ∧ _ at hb
    have cases' : k + 1 = 3 * j + 1 ∨ k + 1 = 3 * j + 2 ∨ k + 1 = 3 * j + 3 := by
      dsimp [j]; omega
    rcases cases' with e | e | e <;> rw [e] <;> rintro ⟨hp, hn, _⟩
    · linarith [(abs_le.mp (hy 1 (by decide))).2]
    · linarith [hb.1, (abs_le.mp (hy 2 (by decide))).2]
    · linarith [hb.2.1, (abs_le.mp (hy 3 (by decide))).2]

lemma uniform_failure {h μ : ℝ} (hh : 0 < h) (k : ℕ)
    (hk : 1048576 * k * μ ^ 2 ≤ 1) : ¬Separates (path h μ k) := by
  by_cases hs : h ≤ 2000
  · intro hsep
    have h := small_step_failure hh.le hs k hk
    linarith [hsep.2.2.2]
  · exact large_step_failure (by linarith) k (by
      linarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (sq_nonneg μ)])

end LongTails.Proofs.FiniteLogisticLinearComparison
