import Mathlib.Tactic

namespace LongTails.Proofs.DerivativePerceptronControl

lemma imbalance_step (a q b ε : ℝ) :
    (q + b * a) ^ 2 - (a + b * q + ε) ^ 2 =
      (1 - b ^ 2) * (q ^ 2 - a ^ 2) - 2 * ε * (a + b * q) - ε ^ 2 := by
  ring

lemma inward_outer (a q b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hbc : b ≤ c) (hc₁ : c ≤ 1) (hq : c * a ≤ q) :
    (q - b * a) ^ 2 - c ^ 2 * (a - b * q) ^ 2 ≤
      (1 - c ^ 2 * b ^ 2) * (q ^ 2 - c ^ 2 * a ^ 2) := by
  have hc₂ : 0 ≤ 1 - c ^ 2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hq (mul_nonneg hb ha)
  have h₂ : b * (1 + c ^ 2) ≤ 2 * c := by
    have h := mul_le_mul_of_nonneg_left hbc (show 0 ≤ 1 + c ^ 2 by positivity)
    nlinarith [mul_nonneg hc hc₂]
  have h₃ := mul_le_mul_of_nonneg_right h₂ (mul_nonneg hb (sq_nonneg a))
  have h₄ : 2 * b * a * q - b ^ 2 * a ^ 2 * (1 + c ^ 2) ≥ 0 := by nlinarith
  have h₅ := mul_nonneg hc₂ h₄
  nlinarith

lemma inward_inner (a q b c : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b ≤ c) (hc₁ : c ≤ 1)
    (hqa : q ≤ c * a) :
    (q - b * a) ^ 2 ≤ c ^ 2 * (a - b * q) ^ 2 := by
  have hc₂ : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hbc₁ : 0 ≤ 1 - b * c := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hqa (show 0 ≤ 1 + b * c by positivity)
  have h₂ := mul_nonneg (mul_nonneg hb ha) hc₂
  have h₃ : q - b * a ≤ c * (a - b * q) := by nlinarith
  have h₄ := mul_nonneg hbc₁ hq
  have h₅ := mul_le_mul_of_nonneg_right hbc ha
  have h₆ : -(c * (a - b * q)) ≤ q - b * a := by nlinarith
  nlinarith [sq_nonneg (c * (a - b * q) - (q - b * a)),
    mul_nonneg (sub_nonneg.mpr h₃) (show 0 ≤ c * (a - b * q) + (q - b * a) by linarith)]

lemma inward_max (M m b : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    max |M - b * m| |m - b * M| = M - b * m := by
  have hM : 0 ≤ M := hm.trans hmM
  have hp : 0 ≤ M - b * m := by nlinarith
  rw [abs_of_nonneg hp]
  apply max_eq_left
  apply abs_le.mpr
  constructor <;> nlinarith

lemma inward_min_lower (M m b : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hb₁ : b ≤ 1) :
    b * M - m ≤ min |M - b * m| |m - b * M| := by
  apply le_min
  · have h := le_abs_self (M - b * m)
    have hM : 0 ≤ M := hm.trans hmM
    nlinarith
  · have h := neg_le_abs (m - b * M)
    linarith

lemma inward_max_sq (M m b : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    (max |M - b * m| |m - b * M|) ^ 2 ≤ M ^ 2 - b * M * m := by
  rw [inward_max M m b hm hmM hb hb₁]
  have hp : b * m ≤ M := by nlinarith
  have h := mul_nonneg (mul_nonneg hb hm) (sub_nonneg.mpr hp)
  nlinarith

lemma outward_max_sq (M m b S : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) (hg : b * M * m ≤ S) :
    (M + b * m) ^ 2 ≤ M ^ 2 + 3 * S := by
  have hp : b * m ≤ M := by nlinarith
  have h := mul_nonneg (mul_nonneg hb hm) (sub_nonneg.mpr hp)
  nlinarith

lemma large_min_product (M m b ρ : ℝ) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hb : ρ ≤ b) (hm : ρ * M / 4 ≤ m) :
    ρ ^ 2 * M ^ 2 / 4 ≤ b * M * m := by
  have hm₀ : 0 ≤ m := le_trans (by positivity) hm
  have h₁ := mul_le_mul_of_nonneg_right hb (mul_nonneg hM hm₀)
  have h₂ := mul_le_mul_of_nonneg_left hm (mul_nonneg hρ hM)
  nlinarith

lemma large_inward_sq (M m b ρ S : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ b) (hb₁ : b ≤ 1) (hS : 0 ≤ S)
    (hlarge : ρ * M / 4 ≤ m) :
    (max |M - b * m| |m - b * M|) ^ 2 ≤ (1 - ρ ^ 2 / 4) * M ^ 2 + 4 * S := by
  have h₁ := inward_max_sq M m b hm hmM (hρ.trans hb) hb₁
  have h₂ := large_min_product M m b ρ (hm.trans hmM) hρ hb hlarge
  nlinarith

lemma large_outward_sq (M m b ρ S : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ b) (hb₁ : b ≤ 1)
    (hlarge : ρ * M / 4 ≤ m) (hg : b * M * m ≤ S) :
    (M + b * m) ^ 2 ≤ (1 - ρ ^ 2 / 4) * M ^ 2 + 4 * S := by
  have h₁ := outward_max_sq M m b S hm hmM (hρ.trans hb) hb₁ hg
  have h₂ := large_min_product M m b ρ (hm.trans hmM) hρ hb hlarge
  nlinarith

lemma square_perturbation (x y A e : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : 0 ≤ e) (hxy : x ≤ y + e) (hyA : y ≤ 5 * A / 4) :
    x ^ 2 ≤ y ^ 2 + 3 * A * e + e ^ 2 := by
  have h₁ := mul_le_mul_of_nonneg_right hyA he
  have hA : 0 ≤ A := by linarith
  nlinarith [mul_nonneg hA he]

lemma small_min_transition (M m M' m' b ρ e : ℝ)
    (hM : 0 ≤ M) (hm : 0 ≤ m) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hb : b ≤ 1 / 4) (hsmall : m ≤ ρ * M / 4) (he : e ≤ ρ * M / 8)
    (hl : M - b * m - e ≤ M') (hu : M' ≤ M + b * m + e)
    (hg : ρ * M - m - e ≤ m') :
    ρ * M' / 4 ≤ m' ∧ M ^ 2 / 2 ≤ M' ^ 2 := by
  have hbm := mul_le_mul_of_nonneg_right hb hm
  have hr := mul_le_mul_of_nonneg_right hρ₁ hM
  have hlow : 3 * M / 4 ≤ M' := by nlinarith
  have hupp : M' ≤ 2 * M := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hupp hρ
  constructor
  · nlinarith
  · have hn : 0 ≤ M' := by linarith
    nlinarith

lemma two_step_plateau (M M₁ M₂ m m₁ ρ A e S : ℝ)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (he : 0 ≤ e)
    (hbase₁ : M₁ ^ 2 ≤ M ^ 2 + 4 * S + 3 * A * e + e ^ 2)
    (hbase₂ : M₂ ^ 2 ≤ M₁ ^ 2 + 4 * S + 3 * A * e + e ^ 2)
    (hlarge₁ : ρ * M / 4 ≤ m →
      M₁ ^ 2 ≤ (1 - ρ ^ 2 / 4) * M ^ 2 + 4 * S + 3 * A * e + e ^ 2)
    (hlarge₂ : ρ * M₁ / 4 ≤ m₁ →
      M₂ ^ 2 ≤ (1 - ρ ^ 2 / 4) * M₁ ^ 2 + 4 * S + 3 * A * e + e ^ 2)
    (htransition : m ≤ ρ * M / 4 → e ≤ ρ * M / 8 →
      ρ * M₁ / 4 ≤ m₁ ∧ M ^ 2 / 2 ≤ M₁ ^ 2) :
    M₂ ^ 2 ≤ (1 - ρ ^ 2 / 8) * M ^ 2 + 8 * S + 6 * A * e + 10 * e ^ 2 := by
  by_cases hl : ρ * M / 4 ≤ m
  · have hh := hlarge₁ hl
    nlinarith [sq_nonneg (ρ * M), sq_nonneg e]
  · by_cases hs : e ≤ ρ * M / 8
    · obtain ⟨hn, hsq⟩ := htransition (le_of_lt (lt_of_not_ge hl)) hs
      have hh := hlarge₂ hn
      have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg ρ)
      nlinarith [sq_nonneg e]
    · have ht : ρ * M ≤ 8 * e := by linarith [lt_of_not_ge hs]
      have hp := mul_nonneg (sub_nonneg.mpr ht)
        (show 0 ≤ 8 * e + ρ * M by positivity)
      nlinarith

lemma abs_perturbation (x ε e : ℝ) (hε : |ε| ≤ e) :
    |x| - e ≤ |x + ε| ∧ |x + ε| ≤ |x| + e := by
  have hu := abs_add_le x ε
  have hl : |x| ≤ |x + ε| + |ε| := by
    calc
      |x| = |(x + ε) + -ε| := by ring_nf
      _ ≤ |x + ε| + |-ε| := abs_add_le _ _
      _ = |x + ε| + |ε| := by rw [abs_neg]
  constructor <;> linarith

lemma max_min_perturbation (x y ε e : ℝ) (hε : |ε| ≤ e) :
    max |x| |y| - e ≤ max |x + ε| |y| ∧
    max |x + ε| |y| ≤ max |x| |y| + e ∧
    min |x| |y| - e ≤ min |x + ε| |y| := by
  obtain ⟨hl, hu⟩ := abs_perturbation x ε e hε
  have he : 0 ≤ e := (abs_nonneg ε).trans hε
  constructor
  · have hx := le_max_left |x + ε| |y|
    have hy := le_max_right |x + ε| |y|
    have ht : max |x| |y| ≤ max |x + ε| |y| + e := by
      apply max_le <;> linarith
    linarith
  constructor
  · have hx := le_max_left |x| |y|
    have hy := le_max_right |x| |y|
    apply max_le <;> linarith
  · have hx := min_le_left |x| |y|
    have hy := min_le_right |x| |y|
    apply le_min <;> linarith

lemma abs_sum_opposed (x y : ℝ) (h : x * y ≤ 0) :
    |x + y| = |(|x| - |y|)| := by
  have hp : |x| * |y| = -(x * y) := by
    rw [← abs_mul, abs_of_nonpos h]
  have hs : |x + y| ^ 2 = |(|x| - |y|)| ^ 2 := by
    rw [sq_abs, sq_abs]
    nlinarith [sq_abs x, sq_abs y]
  nlinarith [abs_nonneg (x + y), abs_nonneg (|x| - |y|)]

lemma abs_sum_aligned (x y : ℝ) (h : 0 ≤ x * y) :
    |x + y| = |x| + |y| := by
  have hp : |x| * |y| = x * y := by
    rw [← abs_mul, abs_of_nonneg h]
  have hs : |x + y| ^ 2 = (|x| + |y|) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_abs x, sq_abs y]
  nlinarith [abs_nonneg (x + y), abs_nonneg x, abs_nonneg y]

lemma signed_inward_max (a q b : ℝ) (hb : |b| ≤ 1) (hg : b * a * q ≤ 0) :
    max |a + b * q| |q + b * a| = max |a| |q| - |b| * min |a| |q| := by
  have ha : a * (b * q) ≤ 0 := by nlinarith [hg]
  have hq : q * (b * a) ≤ 0 := by nlinarith [hg]
  rw [abs_sum_opposed a (b * q) ha, abs_sum_opposed q (b * a) hq,
    abs_mul, abs_mul]
  rcases le_total |a| |q| with h | h
  · rw [max_eq_right h, min_eq_left h, max_comm]
    exact inward_max |q| |a| |b| (abs_nonneg a) h (abs_nonneg b) hb
  · rw [max_eq_left h, min_eq_right h]
    exact inward_max |a| |q| |b| (abs_nonneg q) h (abs_nonneg b) hb

lemma signed_outward_max (a q b : ℝ) (hb : |b| ≤ 1) (hg : 0 ≤ b * a * q) :
    max |a + b * q| |q + b * a| = max |a| |q| + |b| * min |a| |q| := by
  have ha : 0 ≤ a * (b * q) := by nlinarith [hg]
  have hq : 0 ≤ q * (b * a) := by nlinarith [hg]
  rw [abs_sum_aligned a (b * q) ha, abs_sum_aligned q (b * a) hq,
    abs_mul, abs_mul]
  rcases le_total |a| |q| with h | h
  · rw [max_eq_right h, min_eq_left h]
    apply max_eq_right
    have hp := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h)
    nlinarith
  · rw [max_eq_left h, min_eq_right h]
    apply max_eq_left
    have hp := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h)
    nlinarith

lemma signed_product (a q b : ℝ) :
    |b| * max |a| |q| * min |a| |q| = |b * a * q| := by
  rw [abs_mul, abs_mul]
  rcases le_total |a| |q| with h | h
  · rw [max_eq_right h, min_eq_left h]
    ring
  · rw [max_eq_left h, min_eq_right h]

lemma gated_square_control (a q b ρ S : ℝ)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ |b|) (hb₁ : |b| ≤ 1)
    (hS : 0 ≤ S) (hg : b * a * q ≤ S) :
    (max |a + b * q| |q + b * a|) ^ 2 ≤ (max |a| |q|) ^ 2 + 3 * S ∧
    (ρ * max |a| |q| / 4 ≤ min |a| |q| →
      (max |a + b * q| |q + b * a|) ^ 2 ≤
        (1 - ρ ^ 2 / 4) * (max |a| |q|) ^ 2 + 4 * S) := by
  have hm : 0 ≤ min |a| |q| := le_min (abs_nonneg a) (abs_nonneg q)
  have hmM : min |a| |q| ≤ max |a| |q| :=
    (min_le_left _ _).trans (le_max_left _ _)
  by_cases hi : b * a * q ≤ 0
  · rw [signed_inward_max a q b hb₁ hi]
    have hh := inward_max_sq (max |a| |q|) (min |a| |q|) |b| hm hmM
      (abs_nonneg b) hb₁
    rw [inward_max _ _ _ hm hmM (abs_nonneg b) hb₁] at hh
    constructor
    · have hp := mul_nonneg (mul_nonneg (abs_nonneg b) (hm.trans hmM)) hm
      nlinarith
    · intro hl
      have hh := large_inward_sq (max |a| |q|) (min |a| |q|) |b| ρ S
        hm hmM hρ hb hb₁ hS hl
      rwa [inward_max _ _ _ hm hmM (abs_nonneg b) hb₁] at hh
  · have ho : 0 ≤ b * a * q := le_of_lt (lt_of_not_ge hi)
    have hp : |b| * max |a| |q| * min |a| |q| ≤ S := by
      rw [signed_product, abs_of_nonneg ho]
      exact hg
    rw [signed_outward_max a q b hb₁ ho]
    constructor
    · exact outward_max_sq _ _ _ _ hm hmM (abs_nonneg b) hb₁ hp
    · intro hl
      exact large_outward_sq _ _ _ _ _ hm hmM hρ hb hb₁ hl hp

lemma linear_max_min_bounds (a q b : ℝ) (hb : |b| ≤ 1) :
    max |a| |q| - |b| * min |a| |q| ≤ max |a + b * q| |q + b * a| ∧
    max |a + b * q| |q + b * a| ≤ max |a| |q| + |b| * min |a| |q| ∧
    |b| * max |a| |q| - min |a| |q| ≤ min |a + b * q| |q + b * a| := by
  have ha := abs_perturbation a (b * q) |b * q| le_rfl
  have hq := abs_perturbation q (b * a) |b * a| le_rfl
  have har := (abs_perturbation (b * q) a |a| le_rfl).1
  have hqr := (abs_perturbation (b * a) q |q| le_rfl).1
  simp only [abs_mul] at ha hq har hqr
  rw [add_comm (b * q) a] at har
  rw [add_comm (b * a) q] at hqr
  have hma := le_max_left |a + b * q| |q + b * a|
  have hmq := le_max_right |a + b * q| |q + b * a|
  have hp := mul_nonneg (sub_nonneg.mpr hb)
    (add_nonneg (abs_nonneg a) (abs_nonneg q))
  rcases le_total |a| |q| with h | h
  · rw [max_eq_right h, min_eq_left h]
    have hd := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h)
    constructor
    · linarith [hq.1]
    constructor
    · apply max_le <;> nlinarith [ha.2, hq.2]
    · apply le_min <;> nlinarith [hq.1]
  · rw [max_eq_left h, min_eq_right h]
    have hd := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr h)
    constructor
    · linarith [ha.1]
    constructor
    · apply max_le <;> nlinarith [ha.2, hq.2]
    · apply le_min <;> nlinarith [ha.1]

lemma perturbed_gated_square_control (a q b ε ρ A e S : ℝ)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ |b|) (hb₁ : |b| ≤ 1 / 4)
    (hA : max |a| |q| ≤ A) (hε : |ε| ≤ e)
    (hS : 0 ≤ S) (hg : b * a * q ≤ S) :
    (max |a + b * q + ε| |q + b * a|) ^ 2 ≤
      (max |a| |q|) ^ 2 + 4 * S + 3 * A * e + e ^ 2 ∧
    (ρ * max |a| |q| / 4 ≤ min |a| |q| →
      (max |a + b * q + ε| |q + b * a|) ^ 2 ≤
        (1 - ρ ^ 2 / 4) * (max |a| |q|) ^ 2 + 4 * S + 3 * A * e + e ^ 2) := by
  have hb₂ : |b| ≤ 1 := by linarith
  have hlin := linear_max_min_bounds a q b hb₂
  have hm : 0 ≤ min |a| |q| := le_min (abs_nonneg a) (abs_nonneg q)
  have hmM : min |a| |q| ≤ max |a| |q| :=
    (min_le_left _ _).trans (le_max_left _ _)
  have hp := mul_le_mul_of_nonneg_right hb₁ hm
  have hyA : max |a + b * q| |q + b * a| ≤ 5 * A / 4 := by
    nlinarith [hlin.2.1]
  have he : 0 ≤ e := (abs_nonneg ε).trans hε
  have hpert := max_min_perturbation (a + b * q) (q + b * a) ε e hε
  have hs := square_perturbation
    (max |a + b * q + ε| |q + b * a|) (max |a + b * q| |q + b * a|) A e
    ((abs_nonneg _).trans (le_max_left _ _))
    ((abs_nonneg _).trans (le_max_left _ _)) he hpert.2.1 hyA
  obtain ⟨hbase, hlarge⟩ := gated_square_control a q b ρ S hρ hb hb₂ hS hg
  constructor
  · linarith
  · intro hl
    have hh := hlarge hl
    linarith

lemma perturbed_small_min_transition (a q b ε ρ e : ℝ)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ |b|) (hb₁ : |b| ≤ 1 / 4)
    (hε : |ε| ≤ e) (hsmall : min |a| |q| ≤ ρ * max |a| |q| / 4)
    (he : e ≤ ρ * max |a| |q| / 8) :
    ρ * max |a + b * q + ε| |q + b * a| / 4 ≤
      min |a + b * q + ε| |q + b * a| ∧
    (max |a| |q|) ^ 2 / 2 ≤ (max |a + b * q + ε| |q + b * a|) ^ 2 := by
  have hM : 0 ≤ max |a| |q| := (abs_nonneg a).trans (le_max_left _ _)
  have hm : 0 ≤ min |a| |q| := le_min (abs_nonneg a) (abs_nonneg q)
  have hb₂ : |b| ≤ 1 := by linarith
  obtain ⟨hl, hu, hg⟩ := linear_max_min_bounds a q b hb₂
  obtain ⟨hlp, hup, hgp⟩ := max_min_perturbation (a + b * q) (q + b * a) ε e hε
  have hp := mul_le_mul_of_nonneg_right hb hM
  apply small_min_transition (max |a| |q|) (min |a| |q|)
    (max |a + b * q + ε| |q + b * a|) (min |a + b * q + ε| |q + b * a|)
    |b| ρ e hM hm hρ (by linarith) hb₁ hsmall he <;> linarith

lemma scalar_two_step (a q a₁ q₁ b b₁ ε ε₁ ρ A e S : ℝ)
    (ha₁ : a₁ = a + b * q + ε) (hq₁ : q₁ = q + b * a)
    (hρ : 0 ≤ ρ) (hb : ρ ≤ |b|) (hb₁ : ρ ≤ |b₁|)
    (hbu : |b| ≤ 1 / 4) (hb₁u : |b₁| ≤ 1 / 4)
    (hA : max |a| |q| ≤ A) (hA₁ : max |a₁| |q₁| ≤ A)
    (hε : |ε| ≤ e) (hε₁ : |ε₁| ≤ e) (hS : 0 ≤ S)
    (hg : b * a * q ≤ S) (hg₁ : b₁ * a₁ * q₁ ≤ S) :
    (max |a₁ + b₁ * q₁ + ε₁| |q₁ + b₁ * a₁|) ^ 2 ≤
      (1 - ρ ^ 2 / 8) * (max |a| |q|) ^ 2 + 8 * S + 6 * A * e + 10 * e ^ 2 := by
  have hs := perturbed_gated_square_control a q b ε ρ A e S hρ hb hbu hA hε hS hg
  rw [← ha₁, ← hq₁] at hs
  have hs₁ := perturbed_gated_square_control a₁ q₁ b₁ ε₁ ρ A e S
    hρ hb₁ hb₁u hA₁ hε₁ hS hg₁
  apply two_step_plateau (max |a| |q|) (max |a₁| |q₁|)
    (max |a₁ + b₁ * q₁ + ε₁| |q₁ + b₁ * a₁|)
    (min |a| |q|) (min |a₁| |q₁|) ρ A e S
    ((abs_nonneg a).trans (le_max_left _ _)) hρ ((abs_nonneg ε).trans hε)
    hs.1 hs₁.1 hs.2 hs₁.2
  intro hsmall he
  have ht := perturbed_small_min_transition a q b ε ρ e hρ hb hbu hε hsmall he
  rwa [← ha₁, ← hq₁] at ht

lemma finite_geometric_bound (f : ℕ → ℝ) (n : ℕ) (r Q : ℝ)
    (hr : 0 ≤ r) (hQ : 0 ≤ Q)
    (hstep : ∀ k < n, f (k + 1) ≤ r * f k + (1 - r) * Q) :
    f n ≤ r ^ n * f 0 + Q := by
  induction n with
  | zero => simpa using hQ
  | succ n ih =>
    have hn := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hm := mul_le_mul_of_nonneg_left hn hr
    have hs := hstep n (Nat.lt_succ_self n)
    rw [pow_succ]
    nlinarith

lemma imbalance_barrier_step (a q b ε e A ρ J : ℝ)
    (ha : |a| ≤ A) (hq : |q| ≤ A) (hb : |b| ≤ 1)
    (hε : |ε| ≤ e) (hρ : 0 ≤ ρ) (hρb : ρ ≤ |b|)
    (hJ : 0 ≤ J) (hI : q ^ 2 - a ^ 2 ≤ J)
    (hforce : 4 * e * A ≤ ρ ^ 2 * J) :
    (q + b * a) ^ 2 - (a + b * q + ε) ^ 2 ≤ J := by
  have hA : 0 ≤ A := (abs_nonneg a).trans ha
  have he : 0 ≤ e := (abs_nonneg ε).trans hε
  have hmul := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
  have hx : |a + b * q| ≤ 2 * A := by
    have ht := abs_add_le a (b * q)
    rw [abs_mul] at ht
    linarith
  have hf := mul_le_mul hε hx (abs_nonneg _) he
  have hn := neg_le_abs (ε * (a + b * q))
  rw [abs_mul] at hn
  have hb₂ : b ^ 2 ≤ 1 := by nlinarith [sq_abs b]
  have hr₂ : ρ ^ 2 ≤ b ^ 2 := by nlinarith [sq_abs b]
  have hcontract := mul_le_mul_of_nonneg_left hI (show 0 ≤ 1 - b ^ 2 by linarith)
  have hslack := mul_le_mul_of_nonneg_right hr₂ hJ
  rw [imbalance_step]
  nlinarith [sq_nonneg ε]

lemma square_from_imbalance (a q J : ℝ) (hJ : 0 ≤ J)
    (hI : q ^ 2 - a ^ 2 ≤ J) : q ^ 2 ≤ |a * q| + J := by
  rw [abs_mul]
  rcases le_total |q| |a| with h | h
  · have ht := mul_le_mul_of_nonneg_right h (abs_nonneg q)
    nlinarith [sq_abs q]
  · have ht := mul_le_mul_of_nonneg_left h (abs_nonneg a)
    nlinarith [sq_abs a]

lemma signed_inward_squares (a q b : ℝ) (hg : b * a * q ≤ 0) :
    (a + b * q) ^ 2 = (|a| - |b| * |q|) ^ 2 ∧
    (q + b * a) ^ 2 = (|q| - |b| * |a|) ^ 2 := by
  have ha : a * (b * q) ≤ 0 := by nlinarith [hg]
  have hq : q * (b * a) ≤ 0 := by nlinarith [hg]
  constructor
  · rw [← sq_abs (a + b * q), abs_sum_opposed a (b * q) ha, sq_abs, abs_mul]
  · rw [← sq_abs (q + b * a), abs_sum_opposed q (b * a) hq, sq_abs, abs_mul]

lemma signed_inward_contraction (a q b c : ℝ) (hc : 0 ≤ c)
    (hbc : |b| ≤ c) (hc₁ : c ≤ 1) (hg : b * a * q ≤ 0) :
    (q + b * a) ^ 2 - c ^ 2 * (a + b * q) ^ 2 ≤
      (1 - c ^ 2 * b ^ 2) * max (q ^ 2 - c ^ 2 * a ^ 2) 0 := by
  obtain ⟨ha, hq⟩ := signed_inward_squares a q b hg
  rw [ha, hq]
  by_cases hl : c * |a| ≤ |q|
  · have ht := inward_outer |a| |q| |b| c (abs_nonneg a) (abs_nonneg b)
      hc hbc hc₁ hl
    simp only [sq_abs] at ht
    have hp : 0 ≤ q ^ 2 - c ^ 2 * a ^ 2 := by
      have hm := mul_nonneg (sub_nonneg.mpr hl)
        (add_nonneg (abs_nonneg q) (mul_nonneg hc (abs_nonneg a)))
      nlinarith [sq_abs a, sq_abs q]
    simpa only [max_eq_left hp] using ht
  · have ht := inward_inner |a| |q| |b| c (abs_nonneg a) (abs_nonneg q)
      (abs_nonneg b) hc hbc hc₁ (le_of_lt (lt_of_not_ge hl))
    have hb : b ^ 2 ≤ 1 := by nlinarith [sq_abs b, abs_nonneg b]
    have hc₂ : c ^ 2 ≤ 1 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hc₂ (sq_nonneg b)
    have hn : 0 ≤ 1 - c ^ 2 * b ^ 2 := by linarith
    have hm := mul_nonneg hn (le_max_right (q ^ 2 - c ^ 2 * a ^ 2) 0)
    linarith

lemma negative_square_perturbation (x ε c A e : ℝ)
    (hx : |x| ≤ 2 * A) (hε : |ε| ≤ e) :
    -(c ^ 2 * (x + ε) ^ 2) ≤ -(c ^ 2 * x ^ 2) + 4 * c ^ 2 * e * A := by
  have he : 0 ≤ e := (abs_nonneg ε).trans hε
  have hp := mul_le_mul hε hx (abs_nonneg x) he
  have hn := neg_le_abs (ε * x)
  rw [abs_mul] at hn
  have ht : -2 * ε * x - ε ^ 2 ≤ 4 * e * A := by nlinarith [sq_nonneg ε]
  have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg c)
  nlinarith

lemma signed_outward_energy (a q b c : ℝ)
    (hc : 0 ≤ c) (hbc : |b| ≤ c) (hg : 0 ≤ b * a * q) :
    (q + b * a) ^ 2 - c ^ 2 * (a + b * q) ^ 2 ≤ q ^ 2 + 2 * b * a * q := by
  have hb₂ : b ^ 2 ≤ c ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have h₁ := mul_nonneg (sub_nonneg.mpr hb₂) (sq_nonneg a)
  have h₂ := mul_nonneg (sq_nonneg c) hg
  have h₃ := mul_nonneg (sq_nonneg c) (sq_nonneg (b * q))
  nlinarith

lemma inward_barrier_step (a q b ε c A e ρ D : ℝ)
    (hx : |a + b * q| ≤ 2 * A) (hε : |ε| ≤ e)
    (hc : 0 ≤ c) (hbc : |b| ≤ c) (hc₁ : c ≤ 1)
    (hρ : 0 ≤ ρ) (hρb : ρ ≤ |b|) (hD : 0 ≤ D)
    (hF : q ^ 2 - c ^ 2 * a ^ 2 ≤ D)
    (hg : b * a * q ≤ 0) (hforce : 4 * e * A ≤ ρ ^ 2 * D) :
    (q + b * a) ^ 2 - c ^ 2 * (a + b * q + ε) ^ 2 ≤ D := by
  have hi := signed_inward_contraction a q b c hc hbc hc₁ hg
  have hp := negative_square_perturbation (a + b * q) ε c A e hx hε
  have hb₂ : b ^ 2 ≤ 1 := by nlinarith [sq_abs b, abs_nonneg b]
  have hc₂ : c ^ 2 ≤ 1 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hc₂ (sq_nonneg b)
  have hn : 0 ≤ 1 - c ^ 2 * b ^ 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left (max_le hF hD) hn
  have hr₂ : ρ ^ 2 ≤ b ^ 2 := by nlinarith [sq_abs b]
  have hrD := mul_le_mul_of_nonneg_right hr₂ hD
  have hf := mul_le_mul_of_nonneg_left (le_trans hforce hrD) (sq_nonneg c)
  nlinarith

lemma outward_product_bound (a q b ρ S : ℝ)
    (hρ : 0 < ρ) (hb : ρ ≤ |b|) (hg : 0 ≤ b * a * q)
    (hS : b * a * q ≤ S) : |a * q| ≤ S / ρ := by
  have hp := mul_le_mul_of_nonneg_right hb (abs_nonneg (a * q))
  have he : |b| * |a * q| = b * a * q := by
    rw [← abs_mul, mul_assoc, abs_of_nonneg (by nlinarith [hg])]
  rw [he] at hp
  apply (le_div_iff₀ hρ).2
  nlinarith

lemma outward_barrier_step (a q b ε c A e J T S D : ℝ)
    (hx : |a + b * q| ≤ 2 * A) (hε : |ε| ≤ e)
    (hc : 0 ≤ c) (hbc : |b| ≤ c) (hg : 0 ≤ b * a * q)
    (hS : b * a * q ≤ S) (hJ : 0 ≤ J) (hI : q ^ 2 - a ^ 2 ≤ J)
    (hT : |a * q| ≤ T) (hD : T + J + 2 * S + 4 * c ^ 2 * e * A ≤ D) :
    (q + b * a) ^ 2 - c ^ 2 * (a + b * q + ε) ^ 2 ≤ D := by
  have hi := square_from_imbalance a q J hJ hI
  have ho := signed_outward_energy a q b c hc hbc hg
  have hp := negative_square_perturbation (a + b * q) ε c A e hx hε
  linarith

lemma joint_barrier_step (a q b ε c A e ρ J S D : ℝ)
    (ha : |a| ≤ A) (hq : |q| ≤ A) (hε : |ε| ≤ e)
    (hc : 0 ≤ c) (hbc : |b| ≤ c) (hc₁ : c ≤ 1)
    (hρ : 0 < ρ) (hρb : ρ ≤ |b|)
    (hJ : 0 ≤ J) (hDJ : J ≤ D)
    (hI : q ^ 2 - a ^ 2 ≤ J) (hF : q ^ 2 - c ^ 2 * a ^ 2 ≤ D)
    (hforce : 4 * e * A ≤ ρ ^ 2 * J) (hg : b * a * q ≤ S)
    (hD : S / ρ + J + 2 * S + 4 * c ^ 2 * e * A ≤ D) :
    (q + b * a) ^ 2 - (a + b * q + ε) ^ 2 ≤ J ∧
    (q + b * a) ^ 2 - c ^ 2 * (a + b * q + ε) ^ 2 ≤ D := by
  have hb : |b| ≤ 1 := hbc.trans hc₁
  have hx : |a + b * q| ≤ 2 * A := by
    have hp := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
    have ht := abs_add_le a (b * q)
    rw [abs_mul] at ht
    linarith
  constructor
  · exact imbalance_barrier_step a q b ε e A ρ J ha hq hb hε hρ.le hρb hJ hI hforce
  · by_cases hi : b * a * q ≤ 0
    · have hp := mul_le_mul_of_nonneg_left hDJ (sq_nonneg ρ)
      exact inward_barrier_step a q b ε c A e ρ D hx hε hc hbc hc₁ hρ.le hρb
        (hJ.trans hDJ) hF hi (hforce.trans hp)
    · have ho : 0 ≤ b * a * q := le_of_lt (lt_of_not_ge hi)
      exact outward_barrier_step a q b ε c A e J (S / ρ) S D hx hε hc hbc ho hg
        hJ hI (outward_product_bound a q b ρ S hρ hρb ho hg) hD

lemma two_step_envelope (f : ℕ → ℝ) (N : ℕ) (r B Q H : ℝ)
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hQH : Q + B ≤ H)
    (hcontract : r * Q + B ≤ Q) (hzero : f 0 ≤ Q)
    (hone : ∀ k < N, f k ≤ H → f (k + 1) ≤ f k + B)
    (htwo : ∀ k, k + 2 ≤ N → f k ≤ H → f (k + 1) ≤ H →
      f (k + 2) ≤ r * f k + B) :
    ∀ k, (2 * k ≤ N → f (2 * k) ≤ Q) ∧
      (2 * k + 1 ≤ N → f (2 * k + 1) ≤ Q + B) := by
  intro k
  induction k with
  | zero =>
    constructor
    · intro _
      simpa using hzero
    · intro hk
      have ht := hone 0 (by omega) (show f 0 ≤ H by linarith)
      simpa using le_trans ht (show f 0 + B ≤ Q + B by linarith)
  | succ k ih =>
    have he : 2 * (k + 1) ≤ N → f (2 * (k + 1)) ≤ Q := by
      intro hk
      have hi := ih.1 (by omega)
      have hj := ih.2 (by omega)
      have ht := htwo (2 * k) (by omega) (show f (2 * k) ≤ H by linarith)
        (le_trans hj hQH)
      have hm := mul_le_mul_of_nonneg_left hi hr
      have hh : f (2 * k + 2) ≤ Q := by linarith
      convert hh using 1
    constructor
    · exact he
    · intro hk
      have hi := he (by omega)
      have ht := hone (2 * (k + 1)) (by omega)
        (show f (2 * (k + 1)) ≤ H by linarith)
      linarith

lemma two_step_envelope_all (f : ℕ → ℝ) (N : ℕ) (r B Q H : ℝ)
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hQH : Q + B ≤ H)
    (hcontract : r * Q + B ≤ Q) (hzero : f 0 ≤ Q)
    (hone : ∀ k < N, f k ≤ H → f (k + 1) ≤ f k + B)
    (htwo : ∀ k, k + 2 ≤ N → f k ≤ H → f (k + 1) ≤ H →
      f (k + 2) ≤ r * f k + B) :
    ∀ k ≤ N, f k ≤ Q + B := by
  intro k hk
  have ht := two_step_envelope f N r B Q H hr hB hQH hcontract hzero hone htwo (k / 2)
  by_cases hm : k % 2 = 0
  · have he : k = 2 * (k / 2) := by omega
    have hh := ht.1 (by omega)
    rw [← he] at hh
    linarith
  · have he : k = 2 * (k / 2) + 1 := by omega
    have hh := ht.2 (by omega)
    rwa [← he] at hh

lemma even_geometric_bound (f : ℕ → ℝ) (N n : ℕ) (r B Q : ℝ)
    (hn : 2 * n ≤ N) (hr : 0 ≤ r) (hQ : 0 ≤ Q) (hB : B ≤ (1 - r) * Q)
    (hstep : ∀ k, k + 2 ≤ N → f (k + 2) ≤ r * f k + B) :
    f (2 * n) ≤ r ^ n * f 0 + Q := by
  have hh := finite_geometric_bound (fun k => f (2 * k)) n r Q hr hQ
    (fun k hk => by
      have ht := hstep (2 * k) (by omega)
      have he : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [he]
      linarith)
  simpa using hh

lemma contraction_after_log (τ δ : ℝ) (n : ℕ) (hτ : τ ≤ 1) (hδ : 0 < δ)
    (hn : Real.log (1 / δ) ≤ τ * (n : ℝ)) : (1 - τ) ^ n ≤ δ := by
  have hn' : -(τ * (n : ℝ)) ≤ Real.log δ := by
    rw [Real.log_div one_ne_zero (ne_of_gt hδ), Real.log_one] at hn
    linarith
  calc
    (1 - τ) ^ n ≤ (Real.exp (-τ)) ^ n := by
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg τ) n
    _ = Real.exp (-(τ * (n : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hn'
    _ = δ := Real.exp_log hδ

lemma plateau_after_log (v δ ρ : ℝ) (K n : ℕ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρu : ρ ≤ 1) (hK : 1 ≤ K)
    (hlog : Real.log (1 / δ) ≤ (ρ ^ 2 / 8) * (n : ℝ))
    (hv : v ≤ (1 - ρ ^ 2 / 8) ^ n + 1728 * δ * (K : ℝ) / ρ ^ 2) :
    v ≤ 2048 * δ * (K : ℝ) / ρ ^ 2 := by
  have hd := contraction_after_log (ρ ^ 2 / 8) δ n (by nlinarith [hρ.le]) hδ hlog
  have hKr : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hρK : ρ ^ 2 ≤ (K : ℝ) := by nlinarith [hρ.le]
  have hm := mul_le_mul_of_nonneg_left hρK hδ.le
  have hδle : δ ≤ δ * (K : ℝ) / ρ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hρ)).mpr hm
  have hn : 0 ≤ δ * (K : ℝ) / ρ ^ 2 := by positivity
  simp only [div_eq_mul_inv] at hv hd hδle hn ⊢
  nlinarith

lemma additive_bound (f : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hstep : ∀ k < N, f (k + 1) ≤ f k + C) : f N ≤ f 0 + (N : ℝ) * C := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hn := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hs := hstep N (Nat.lt_succ_self N)
    push_cast
    nlinarith

end LongTails.Proofs.DerivativePerceptronControl
