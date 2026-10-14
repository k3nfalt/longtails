import LongTails.Proofs.TerminalClippingEnergy
import LongTails.Proofs.TerminalClippingSchedule
import Mathlib.Algebra.BigOperators.Intervals

open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma moving_comparator_sum (g h θ : ℕ → ℝ) (n : ℕ)
    (hh : ∀ t < n, h (t + 1) = θ t * h t + (1 - θ t) * g t) :
    (∑ t ∈ Finset.range n, (1 - θ (t + 1)) * (g (t + 1) - h (t + 1))) =
      g n - g 0 + θ 0 * (g 0 - h 0) - θ n * (g n - h n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (fun t ht => hh t (by omega)), hh n (by omega)]
    ring

lemma moving_comparator_terminal (g h θ : ℕ → ℝ) (n : ℕ)
    (hh : ∀ t < n, h (t + 1) = θ t * h t + (1 - θ t) * g t)
    (h0 : θ 0 = 1) (hn : θ n = 0) :
    (∑ t ∈ Finset.range n, (1 - θ (t + 1)) * (g (t + 1) - h (t + 1))) =
      g n - h 0 := by
  rw [moving_comparator_sum g h θ n hh, h0, hn]
  ring

lemma weighted_potential_sum (w d : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range n, w t * (d t - d (t + 1))) =
      w 0 * d 0 - w n * d n +
        ∑ t ∈ Finset.range n, (w (t + 1) - w t) * d (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

lemma weighted_potential_bound (w d : ℕ → ℝ) (n : ℕ)
    (hw : 0 ≤ w n) (hd : 0 ≤ d n) :
    (∑ t ∈ Finset.range n, w t * (d t - d (t + 1))) ≤
      w 0 * d 0 + ∑ t ∈ Finset.range n, (w (t + 1) - w t) * d (t + 1) := by
  rw [weighted_potential_sum]
  nlinarith [mul_nonneg hw hd]

lemma terminal_descent_from_steps (g H θ w d r : ℕ → ℝ) (n : ℕ)
    (hH : ∀ t < n, H (t + 1) = θ t * H t + (1 - θ t) * g t)
    (h0 : θ 0 = 1) (hn : θ n = 0) (hw : 0 ≤ w n) (hd : 0 ≤ d n)
    (hstep : ∀ t < n,
      (1 - θ (t + 1)) * (g (t + 1) - H (t + 1)) ≤
        w t * (d t - d (t + 1)) + r t) :
    g n - H 0 ≤ w 0 * d 0 +
      ∑ t ∈ Finset.range n, ((w (t + 1) - w t) * d (t + 1) + r t) := by
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun t ht =>
    hstep t (Finset.mem_range.mp ht))
  rw [moving_comparator_terminal g H θ n hH h0 hn, Finset.sum_add_distrib] at hs
  rw [Finset.sum_add_distrib]
  have hp := weighted_potential_bound w d n hw hd
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_comparator_upper {X : Set E} {f : E → ℝ} (hf : ConvexOn ℝ X f)
    (x z : ℕ → E) (H θ : ℕ → ℝ) (n : ℕ)
    (hx : ∀ t < n, x t ∈ X) (hz0 : z 0 ∈ X) (hH0 : f (z 0) ≤ H 0)
    (hθ : ∀ t < n, 0 ≤ θ t ∧ θ t ≤ 1)
    (hz : ∀ t < n, z (t + 1) = θ t • z t + (1 - θ t) • x t)
    (hH : ∀ t < n, H (t + 1) = θ t * H t + (1 - θ t) * f (x t)) :
    z n ∈ X ∧ f (z n) ≤ H n := by
  induction n with
  | zero => exact ⟨hz0, hH0⟩
  | succ n ih =>
    have hn : n < n + 1 := by omega
    have hp := ih (fun t ht => hx t (by omega))
      (fun t ht => hθ t (by omega)) (fun t ht => hz t (by omega))
      (fun t ht => hH t (by omega))
    have ha := (hθ n hn).1
    have hb : 0 ≤ 1 - θ n := by linarith [(hθ n hn).2]
    rw [hz n hn, hH n hn]
    refine ⟨hf.1 hp.1 (hx n hn) ha hb (by ring), ?_⟩
    have hh := hf.2 hp.1 (hx n hn) ha hb (by ring)
    dsimp only [smul_eq_mul] at hh
    exact hh.trans (add_le_add_left (mul_le_mul_of_nonneg_left hp.2 ha) _)

lemma moving_comparator_distance {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (x z : E) :
    ‖x - (θ • z + (1 - θ) • x)‖ ^ 2 ≤ θ * ‖x - z‖ ^ 2 := by
  have he : x - (θ • z + (1 - θ) • x) = θ • (x - z) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ, mul_pow]
  have hs : θ ^ 2 ≤ θ := by nlinarith
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

lemma moving_comparator_step {f : E → ℝ} {η M θ H : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {x y z h c : E}
    (hproj : ‖y - (θ • z + (1 - θ) • x)‖ ^ 2 ≤
      ‖x - η • c - (θ • z + (1 - θ) • x)‖ ^ 2)
    (hstep : ‖y - x‖ ≤ η * ‖c‖)
    (hsub : f x - f (θ • z + (1 - θ) • x) ≤
      ⟪h, x - (θ • z + (1 - θ) • x)⟫)
    (hupper : f y - f x ≤ M * ‖y - x‖)
    (hH : f (θ • z + (1 - θ) • x) ≤ H) :
    η * (f y - H) ≤ θ * ‖x - z‖ ^ 2 / 2 -
      ‖y - (θ • z + (1 - θ) • x)‖ ^ 2 / 2 +
      η ^ 2 * (M ^ 2 / 2 + ‖c‖ ^ 2) + η * θ * ⟪h - c, x - z⟫ := by
  have hs := projected_objective_step hη hM hproj hstep hsub hupper
  have he : x - (θ • z + (1 - θ) • x) = θ • (x - z) := by module
  rw [he, real_inner_smul_right] at hs
  have hd := moving_comparator_distance hθ hθ1 x z
  rw [he] at hd
  have hf := mul_le_mul_of_nonneg_left hH hη.le
  nlinarith

lemma auxiliary_comparator_update {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) (x x0 p u : E) :
    x0 + nextAuxiliary B δ T t (x - x0) p +
      (tailWeight B δ T t / tailWeight B δ T 0) • (u - x0) =
    (tailWeight B δ T t / tailWeight B δ T (t - 1)) •
      (x0 + p + (tailWeight B δ T (t - 1) / tailWeight B δ T 0) • (u - x0)) +
    (1 - tailWeight B δ T t / tailWeight B δ T (t - 1)) • x := by
  have hp := (tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)).ne'
  have h0 := (tailWeight_pos hB hδ hδ1 (Nat.zero_lt_of_lt ht)).ne'
  have he : tailWeight B δ T t / tailWeight B δ T (t - 1) *
      (tailWeight B δ T (t - 1) / tailWeight B δ T 0) =
      tailWeight B δ T t / tailWeight B δ T 0 := by field_simp
  unfold nextAuxiliary
  dsimp only
  simp only [smul_add, smul_smul, he]
  module

lemma comparator_influence_decomposition {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T t : ℕ} (ht : t < T) (x x0 p u : E) :
    influenceScale B δ T t •
      (x - (x0 + p + (tailWeight B δ T (t - 1) / tailWeight B δ T 0) • (u - x0))) =
    influenceScale B δ T t • ((x - x0) - p) -
      (weight T t * stepSize B δ T t / tailWeight B δ T 0) • (u - x0) := by
  have hp := (tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)).ne'
  have h0 := (tailWeight_pos hB hδ hδ1 (Nat.zero_lt_of_lt ht)).ne'
  have he : influenceScale B δ T t * (tailWeight B δ T (t - 1) / tailWeight B δ T 0) =
      weight T t * stepSize B δ T t / tailWeight B δ T 0 := by
    unfold influenceScale
    field_simp
  rw [show x - (x0 + p + (tailWeight B δ T (t - 1) / tailWeight B δ T 0) • (u - x0)) =
    ((x - x0) - p) - (tailWeight B δ T (t - 1) / tailWeight B δ T 0) • (u - x0) by module,
    smul_sub, smul_smul, he]

lemma weighted_comparator_step {f : E → ℝ} {η M S P w H : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (hS : 0 < S) (hP : 0 < P) (hSP : S ≤ P)
    (hw : 0 ≤ w) {x y z h c : E}
    (hproj : ‖y - ((S / P) • z + (1 - S / P) • x)‖ ^ 2 ≤
      ‖x - η • c - ((S / P) • z + (1 - S / P) • x)‖ ^ 2)
    (hstep : ‖y - x‖ ≤ η * ‖c‖)
    (hsub : f x - f ((S / P) • z + (1 - S / P) • x) ≤
      ⟪h, x - ((S / P) • z + (1 - S / P) • x)⟫)
    (hupper : f y - f x ≤ M * ‖y - x‖)
    (hH : f ((S / P) • z + (1 - S / P) • x) ≤ H) :
    (w * η / S) * (f y - H) ≤
      w * (‖x - z‖ ^ 2 / (2 * P) - ‖y - ((S / P) • z + (1 - S / P) • x)‖ ^ 2 / (2 * S)) +
      (w * η ^ 2 / S) * (M ^ 2 / 2 + ‖c‖ ^ 2) + ⟪h - c, (w * η / P) • (x - z)⟫ := by
  have hh := moving_comparator_step hη hM (div_nonneg hS.le hP.le) ((div_le_one hP).mpr hSP)
    hproj hstep hsub hupper hH
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ w / S by positivity)
  rw [real_inner_smul_right]
  convert hm using 1 <;> field_simp

lemma shifted_absorption (A N : ℕ → ℝ) {T : ℕ} (hT : 0 < T)
    (hN : 0 ≤ N T) (habsorb : ∀ t, 0 < t → t < T → A t ≤ N t) :
    (∑ t ∈ Finset.range T, (A t - N (t + 1))) ≤ A 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hT)
  rw [Finset.sum_sub_distrib, Finset.sum_range_succ' A, Finset.sum_range_succ]
  have hh : (∑ t ∈ Finset.range n, A (t + 1)) ≤ ∑ t ∈ Finset.range n, N (t + 1) := by
    apply Finset.sum_le_sum
    intro t ht
    exact habsorb (t + 1) (by omega) (by have := Finset.mem_range.mp ht; omega)
  linarith

lemma schedule_terminal_descent {f : E → ℝ} {B δ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) {T : ℕ} (hT : 0 < T)
    (x z h c : ℕ → E) (H M : ℕ → ℝ)
    (hM : ∀ t < T, 0 ≤ M t)
    (hz : ∀ t < T, z (t + 1) = (tailWeight B δ T t / tailWeight B δ T (t - 1)) • z t +
      (1 - tailWeight B δ T t / tailWeight B δ T (t - 1)) • x t)
    (hH : ∀ t < T, H (t + 1) = (tailWeight B δ T t / tailWeight B δ T (t - 1)) * H t +
      (1 - tailWeight B δ T t / tailWeight B δ T (t - 1)) * f (x t))
    (hproj : ∀ t < T, ‖x (t + 1) - z (t + 1)‖ ^ 2 ≤
      ‖x t - stepSize B δ T t • c t - z (t + 1)‖ ^ 2)
    (hstep : ∀ t < T, ‖x (t + 1) - x t‖ ≤ stepSize B δ T t * ‖c t‖)
    (hsub : ∀ t < T, f (x t) - f (z (t + 1)) ≤ ⟪h t, x t - z (t + 1)⟫)
    (hupper : ∀ t < T, f (x (t + 1)) - f (x t) ≤ M t * ‖x (t + 1) - x t‖)
    (hmajor : ∀ t < T, f (z (t + 1)) ≤ H (t + 1)) :
    f (x T) - H 0 ≤ weight T 0 * (‖x 0 - z 0‖ ^ 2 / (2 * tailWeight B δ T 0)) +
      ∑ t ∈ Finset.range T,
        (-‖x (t + 1) - z (t + 1)‖ ^ 2 / (4 * T * tailWeight B δ T t) +
          (weight T t * (stepSize B δ T t) ^ 2 / tailWeight B δ T t) *
            ((M t) ^ 2 / 2 + ‖c t‖ ^ 2) +
          ⟪h t - c t, influenceScale B δ T t • (x t - z t)⟫) := by
  let θ := fun t => tailWeight B δ T t / tailWeight B δ T (t - 1)
  let d := fun t => ‖x t - z t‖ ^ 2 / (2 * tailWeight B δ T (t - 1))
  let r := fun t => (weight T t * (stepSize B δ T t) ^ 2 / tailWeight B δ T t) *
    ((M t) ^ 2 / 2 + ‖c t‖ ^ 2) + ⟪h t - c t, influenceScale B δ T t • (x t - z t)⟫
  have hs0 := (tailWeight_pos hB hδ hδ1 hT).ne'
  have hθ0 : θ 0 = 1 := by simp [θ, hs0]
  have hθT : θ T = 0 := by simp [θ, tailWeight_terminal]
  have hdT : 0 ≤ d T := by
    dsimp [d]
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (tailWeight_pos hB hδ hδ1 (show T - 1 < T by omega)).le)
  have hh := terminal_descent_from_steps (fun t => f (x t)) H θ (weight T) d r T hH hθ0 hθT
    (weight_terminal_nonneg hT) hdT
  have hsteps (t : ℕ) (ht : t < T) :
      (1 - θ (t + 1)) * (f (x (t + 1)) - H (t + 1)) ≤
        weight T t * (d t - d (t + 1)) + r t := by
    have hSt := tailWeight_pos hB hδ hδ1 ht
    have hSp := tailWeight_pos hB hδ hδ1 (show t - 1 < T by omega)
    have hw : 0 ≤ weight T t := by linarith [(weight_bounds ht).1]
    have hθ : 1 - θ (t + 1) = weight T t * stepSize B δ T t / tailWeight B δ T t := by
      dsimp [θ]
      rw [← tailWeight_step B δ ht]
      field_simp
    rw [hθ]
    have hh' := weighted_comparator_step (z := z t) (h := h t) (H := H (t + 1)) (M := M t) (stepSize_pos hB hδ hδ1 ht) (hM t ht) hSt hSp
      (tailWeight_prev_ge hB hδ hδ1 ht) hw
      (by simpa only [← hz t ht] using hproj t ht)
      (hstep t ht) (by simpa only [← hz t ht] using hsub t ht)
      (hupper t ht) (by simpa only [← hz t ht] using hmajor t ht)
    simpa only [d, r, influenceScale, Nat.add_sub_cancel, ← hz t ht, add_assoc] using hh'
  have hfinal := hh hsteps
  convert hfinal using 1
  dsimp [d, r]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [weight_difference T t]
  ring

end OracleTemplate.TerminalClipping
