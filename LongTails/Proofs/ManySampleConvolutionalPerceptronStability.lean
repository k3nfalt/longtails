import Mathlib.Tactic

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronStability

lemma two_step_contraction {ρ c c' V V' V'' D D' e e' : ℝ}
    (hρ : 0 ≤ ρ) (hρc : ρ ≤ c) (hρc' : ρ ≤ c') (hρ1 : ρ ≤ 1)
    (hV : 0 ≤ V) (hD : 0 ≤ D) (hD' : 0 ≤ D') (he : 0 ≤ e)
    (hstep : V' ≤ V - c * D + e)
    (hgap : c * V - D - e ≤ D')
    (hnext : V'' ≤ V' - c' * D' + e') :
    V'' ≤ (1 - ρ ^ 2 / 2) * V + 2 * e + e' := by
  have hcD : ρ * D ≤ c * D := mul_le_mul_of_nonneg_right hρc hD
  have hcD' : ρ * D' ≤ c' * D' := mul_le_mul_of_nonneg_right hρc' hD'
  have hcV : ρ * V ≤ c * V := mul_le_mul_of_nonneg_right hρc hV
  by_cases hlarge : ρ * V / 2 ≤ D
  · have hmul := mul_le_mul_of_nonneg_left hlarge hρ
    have hnext' : V'' ≤ V' + e' := by nlinarith
    nlinarith
  · have hsmall : D < ρ * V / 2 := lt_of_not_ge hlarge
    have hgap' : ρ * V / 2 - e ≤ D' := by linarith
    have hmul := mul_le_mul_of_nonneg_left hgap' hρ
    have her : ρ * e ≤ e := by nlinarith
    have hfirst : V' ≤ V + e := by nlinarith
    nlinarith

noncomputable def scalarStep (c s d : ℝ) : ℝ × ℝ :=
  if |s| ≤ |d| then ((1 + c) * s, (1 - c) * d)
  else ((1 - c) * s, (1 + c) * d)

lemma scalarStep_mass {c s d : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |(scalarStep c s d).1| + |(scalarStep c s d).2| =
      |s| + |d| - c * abs (|s| - |d|) := by
  have hp : 0 ≤ 1 + c := by linarith
  have hm : 0 ≤ 1 - c := by linarith
  unfold scalarStep
  split_ifs with h
  · simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hm]
    rw [abs_of_nonpos (by linarith : |s| - |d| ≤ 0)]
    ring
  · simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hm]
    rw [abs_of_nonneg (by linarith : 0 ≤ |s| - |d|)]
    ring

lemma scalarStep_gap {c s d : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    abs (|(scalarStep c s d).1| - |(scalarStep c s d).2|) =
      |abs (|s| - |d|) - c * (|s| + |d|)| := by
  have hp : 0 ≤ 1 + c := by linarith
  have hm : 0 ≤ 1 - c := by linarith
  unfold scalarStep
  split_ifs with h
  · simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hm]
    rw [abs_of_nonpos (by linarith : |s| - |d| ≤ 0)]
    have hid : (1 + c) * |s| - (1 - c) * |d| =
        -(-(|s| - |d|) - c * (|s| + |d|)) := by ring
    rw [hid, abs_neg]
  · simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hm]
    rw [abs_of_nonneg (by linarith : 0 ≤ |s| - |d|)]
    congr 1
    ring

lemma abs_le_abs_add (x f : ℝ) : |x| ≤ |x + f| + |f| := by
  calc
    |x| = |(x + f) + -f| := by congr 1; ring
    _ ≤ |x + f| + |-f| := abs_add_le _ _
    _ = |x + f| + |f| := by rw [abs_neg]

lemma shifted_mass_le (x y f : ℝ) :
    |x + f| + |y + f| ≤ |x| + |y| + 2 * |f| := by
  have hx := abs_add_le x f
  have hy := abs_add_le y f
  linarith

lemma shifted_gap_ge (x y f : ℝ) :
    abs (|x| - |y|) - 2 * |f| ≤ abs (|x + f| - |y + f|) := by
  have hx := abs_le_abs_add x f
  have hy := abs_le_abs_add y f
  have hx' := abs_add_le x f
  have hy' := abs_add_le y f
  have hl := neg_le_abs (|x + f| - |y + f|)
  have hr := le_abs_self (|x + f| - |y + f|)
  have h : abs (|x| - |y|) ≤ abs (|x + f| - |y + f|) + 2 * |f| := by
    apply abs_le.mpr
    constructor <;> linarith
  linarith

lemma scalarStep_forced_mass {c s d f : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |(scalarStep c s d).1 + f| + |(scalarStep c s d).2 + f| ≤
      |s| + |d| - c * abs (|s| - |d|) + 2 * |f| := by
  have h := shifted_mass_le (scalarStep c s d).1 (scalarStep c s d).2 f
  rw [scalarStep_mass hc hc1] at h
  exact h

lemma scalarStep_forced_gap {c s d f : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    c * (|s| + |d|) - abs (|s| - |d|) - 2 * |f| ≤
      abs (|(scalarStep c s d).1 + f| - |(scalarStep c s d).2 + f|) := by
  have h := shifted_gap_ge (scalarStep c s d).1 (scalarStep c s d).2 f
  rw [scalarStep_gap hc hc1] at h
  have hl := neg_le_abs (abs (|s| - |d|) - c * (|s| + |d|))
  linarith

lemma forced_two_step {ρ c c' s d f f' : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc : ρ ≤ c) (hc1 : c ≤ 1)
    (hc' : ρ ≤ c') (hc1' : c' ≤ 1) :
    let s' := (scalarStep c s d).1 + f
    let d' := (scalarStep c s d).2 + f
    |(scalarStep c' s' d').1 + f'| + |(scalarStep c' s' d').2 + f'| ≤
      (1 - ρ ^ 2 / 2) * (|s| + |d|) + 4 * |f| + 2 * |f'| := by
  dsimp only
  have h := two_step_contraction hρ hc hc' hρ1
    (add_nonneg (abs_nonneg s) (abs_nonneg d)) (abs_nonneg (|s| - |d|))
    (abs_nonneg (|(scalarStep c s d).1 + f| - |(scalarStep c s d).2 + f|))
    (by positivity : 0 ≤ 2 * |f|)
    (scalarStep_forced_mass (le_trans hρ hc) hc1)
    (scalarStep_forced_gap (le_trans hρ hc) hc1)
    (scalarStep_forced_mass (f := f') (le_trans hρ hc') hc1')
  linarith

lemma two_step_bound {V : ℕ → ℝ} {r C A : ℝ}
    (hr : 0 ≤ r) (hzero : V 0 ≤ A + C) (hone : V 1 ≤ A + C)
    (hstep : ∀ n, V (n + 2) ≤ r * V n + (1 - r) * C) :
    ∀ n, V n ≤ A * r ^ (n / 2) + C := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa using hone
  | more n hn _ =>
    have hmul := mul_le_mul_of_nonneg_left hn hr
    have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [hdiv, pow_succ]
    nlinarith [hstep n]

lemma two_step_bound_on {V : ℕ → ℝ} {r C A : ℝ} {K : ℕ}
    (hr : 0 ≤ r) (hzero : V 0 ≤ A + C) (hone : 1 ≤ K → V 1 ≤ A + C)
    (hstep : ∀ n, n + 2 ≤ K → V (n + 2) ≤ r * V n + (1 - r) * C) :
    ∀ n, n ≤ K → V n ≤ A * r ^ (n / 2) + C := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simpa using hzero
  | one => intro h; simpa using hone h
  | more n hn _ =>
    intro h
    have hmul := mul_le_mul_of_nonneg_left (hn (by omega)) hr
    have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [hdiv, pow_succ]
    nlinarith [hstep n h]

noncomputable def escapeKick (σ s : ℝ) : ℝ := if 0 ≤ s then σ else -σ

lemma escapeKick_abs {σ s : ℝ} (hσ : 0 ≤ σ) : |escapeKick σ s| = σ := by
  unfold escapeKick
  split_ifs <;> simp [abs_of_nonneg hσ]

lemma escape_unstable {σ c s : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    |(1 + c) * s + escapeKick σ s| = (1 + c) * |s| + σ := by
  unfold escapeKick
  split_ifs with hs
  · rw [abs_of_nonneg hs, abs_of_nonneg (by positivity)]
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    rw [abs_of_nonpos hs', abs_of_nonpos (by nlinarith)]
    ring

lemma escape_stable {σ ρ c d s : ℝ} (hσ : 0 ≤ σ) (hρc : ρ ≤ c)
    (hc1 : c ≤ 1) :
    |(1 - c) * d + escapeKick σ s| ≤ (1 - ρ) * |d| + σ := by
  calc
    _ ≤ |(1 - c) * d| + |escapeKick σ s| := abs_add_le _ _
    _ = (1 - c) * |d| + σ := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - c), escapeKick_abs hσ]
    _ ≤ _ := by nlinarith [abs_nonneg d]

lemma forced_sequence_bound {V : ℕ → ℝ} {ρ F : ℝ} {K : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hF : 0 ≤ F)
    (hzero : V 0 ≤ 3) (hone : 1 ≤ K → V 1 ≤ 3)
    (hstep : ∀ n, n + 2 ≤ K →
      V (n + 2) ≤ (1 - ρ ^ 2 / 2) * V n + 6 * F) :
    ∀ n, n ≤ K → V n ≤ 3 * (1 - ρ ^ 2 / 2) ^ (n / 2) + 12 * F / ρ ^ 2 := by
  have hr : 0 ≤ 1 - ρ ^ 2 / 2 := by nlinarith
  have hC : 0 ≤ 12 * F / ρ ^ 2 := by positivity
  have hid : (1 - (1 - ρ ^ 2 / 2)) * (12 * F / ρ ^ 2) = 6 * F := by
    field_simp [ne_of_gt hρ]
    ring
  apply two_step_bound_on hr (hzero.trans (by linarith))
    (fun h => (hone h).trans (by linarith))
  intro n hn
  rw [hid]
  exact hstep n hn

lemma switch_criterion (a q : ℝ) : |a + q| ≤ |a - q| ↔ a * q ≤ 0 := by
  rw [← sq_le_sq]
  constructor <;> intro h <;> nlinarith

lemma trajectory_bound {s d c f : ℕ → ℝ} {ρ F : ℝ} {K : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hF : 0 ≤ F)
    (hzero : |s 0| + |d 0| ≤ 3) (hone : 1 ≤ K → |s 1| + |d 1| ≤ 3)
    (hc : ∀ n, n < K → ρ ≤ c n) (hc1 : ∀ n, n < K → c n ≤ 1)
    (hf : ∀ n, n < K → |f n| ≤ F)
    (hs : ∀ n, n < K → s (n + 1) = (scalarStep (c n) (s n) (d n)).1 + f n)
    (hd : ∀ n, n < K → d (n + 1) = (scalarStep (c n) (s n) (d n)).2 + f n) :
    ∀ n, n ≤ K → |s n| + |d n| ≤
      3 * (1 - ρ ^ 2 / 2) ^ (n / 2) + 12 * F / ρ ^ 2 := by
  apply forced_sequence_bound hρ hρ1 hF hzero hone
  intro n hn
  have hn0 : n < K := by omega
  have hn1 : n + 1 < K := by omega
  have ht := forced_two_step (s := s n) (d := d n) (f := f n) (f' := f (n + 1))
    hρ.le hρ1 (hc n hn0) (hc1 n hn0) (hc (n + 1) hn1) (hc1 (n + 1) hn1)
  dsimp only at ht
  rw [← hs n hn0, ← hd n hn0, ← hs (n + 1) hn1, ← hd (n + 1) hn1] at ht
  have hf0 := hf n hn0
  have hf1 := hf (n + 1) hn1
  linarith

lemma escape_growth {s : ℕ → ℝ} {ρ σ : ℝ} {K : ℕ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hstep : ∀ n, n < K → (1 + ρ) * |s n| + σ ≤ |s (n + 1)|) :
    ∀ n, n + 1 ≤ K → σ * (1 + ρ) ^ n ≤ |s (n + 1)| := by
  intro n
  induction n with
  | zero =>
    intro hn
    have h := hstep 0 (by omega)
    have hp : 0 ≤ (1 + ρ) * |s 0| := by positivity
    simpa using (show σ ≤ |s 1| by linarith)
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 + ρ)
    have ht := hstep (n + 1) (by omega)
    rw [pow_succ]
    nlinarith

lemma escape_stable_bound {d : ℕ → ℝ} {ρ σ D : ℝ} {K : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 ≤ σ) (hD : 0 ≤ D)
    (hinit : |d 0| ≤ D)
    (hstep : ∀ n, n < K → |d (n + 1)| ≤ (1 - ρ) * |d n| + σ) :
    ∀ n, n ≤ K → |d n| ≤ D + σ / ρ := by
  intro n
  induction n with
  | zero =>
    intro _
    have hf : 0 ≤ σ / ρ := by positivity
    linarith
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hm := mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ 1 - ρ)
    have ht := hstep n (by omega)
    have hid : ρ * (σ / ρ) = σ := by field_simp
    have hd := mul_nonneg hρ.le hD
    nlinarith

end LongTails.Proofs.ManySampleConvolutionalPerceptronStability
