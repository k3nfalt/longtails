import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.AdamAccumulator

lemma momentum_square {b m g : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (b * m + (1 - b) * g) ^ 2 ≤ b * m ^ 2 + (1 - b) * g ^ 2 := by
  have hp := mul_nonneg (mul_nonneg hb (sub_nonneg.2 hb1)) (sq_nonneg (m - g))
  nlinarith

lemma momentum_normalized_square {b β γ m v g : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hbβ : b ≤ β) (hγ : 0 ≤ γ) (hv : 0 ≤ v) (hm : γ * m ^ 2 ≤ v) :
    γ * (b * m + (1 - b) * g) ^ 2 ≤ β * v + γ * g ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_left (momentum_square hb hb1 (m := m) (g := g)) hγ
  have h2 := mul_le_mul_of_nonneg_left hm hb
  have h3 := mul_le_mul_of_nonneg_right hbβ hv
  have h4 := mul_nonneg (mul_nonneg hγ hb) (sq_nonneg g)
  nlinarith

lemma auxiliary_increment {b η m g d e x : ℝ} (hb : b ≠ 1) (hd : d ≠ 0) (he : e ≠ 0) :
    (x - η * (b * m + (1 - b) * g) / e -
      η * b / (1 - b) * (b * m + (1 - b) * g) / e) -
      (x - η * b / (1 - b) * m / d) =
      -η * g / e + η * b / (1 - b) * m * (1 / d - 1 / e) := by
  have hb' : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  field_simp
  ring

lemma normalized_square_log {β γ v g : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (hv : 0 < v) :
    γ * g ^ 2 / (β * v + γ * g ^ 2) ≤
      Real.log (β * v + γ * g ^ 2) - Real.log v - Real.log β := by
  have hw : 0 < β * v + γ * g ^ 2 := by positivity
  have hh := Real.log_le_sub_one_of_pos (show 0 < β * v / (β * v + γ * g ^ 2) by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hβ.ne' hv.ne'] at hh
  have he : β * v / (β * v + γ * g ^ 2) - 1 =
      -(γ * g ^ 2 / (β * v + γ * g ^ 2)) := by field_simp; ring
  rw [he] at hh
  linarith

lemma accumulator_pos {β γ : ℝ} {v g : ℕ → ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hv : 0 < v 0) (hrec : ∀ t, v (t + 1) = β * v t + γ * (g t) ^ 2) (t : ℕ) :
    0 < v t := by
  induction t with
  | zero => exact hv
  | succ t ih => rw [hrec]; positivity

lemma normalized_square_sum {β γ : ℝ} {v g : ℕ → ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hv : 0 < v 0) (hrec : ∀ t, v (t + 1) = β * v t + γ * (g t) ^ 2) (n : ℕ) :
    (∑ t ∈ Finset.range n, γ * (g t) ^ 2 / v (t + 1)) ≤
      Real.log (v n) - Real.log (v 0) - n * Real.log β := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      have hh := normalized_square_log hβ hγ (accumulator_pos hβ hγ hv hrec n) (g := g n)
      rw [← hrec n] at hh
      linarith

lemma accumulator_upper {β γ : ℝ} {v g : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hγ : 0 ≤ γ) (hv : 0 < v 0)
    (hrec : ∀ t, v (t + 1) = β * v t + γ * (g t) ^ 2) (n : ℕ) :
    v n ≤ v 0 + γ * ∑ t ∈ Finset.range n, (g t) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hrec n, Finset.sum_range_succ]
      have hh := mul_le_mul_of_nonneg_right hβ1 (accumulator_pos hβ hγ hv hrec n).le
      nlinarith

lemma decay_power_lower {T : ℕ} (hT : 2 ≤ T) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (T : ℝ)) ^ T := by
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have hi : 1 / (T : ℝ) ≤ 1 := (div_le_one ht0).2 (by linarith)
  have hh := one_add_mul_self_le_rpow_one_add
    (s := -(1 / (T : ℝ))) (by linarith) (p := (T : ℝ) / 2) (by linarith)
  have he : 1 + (T : ℝ) / 2 * -(1 / (T : ℝ)) = 1 / 2 := by field_simp; ring
  rw [he] at hh
  have hb : 0 ≤ 1 - 1 / (T : ℝ) := by linarith
  have hpow : ((1 - 1 / (T : ℝ)) ^ ((T : ℝ) / 2)) ^ (2 : ℕ) =
      (1 - 1 / (T : ℝ)) ^ T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    norm_num
  have hh' : 1 / 2 ≤ (1 - 1 / (T : ℝ)) ^ ((T : ℝ) / 2) := by
    simpa only [sub_eq_add_neg] using hh
  nlinarith [sq_nonneg ((1 - 1 / (T : ℝ)) ^ ((T : ℝ) / 2) - 1 / 2)]

lemma decay_log_bound {T : ℕ} (hT : 2 ≤ T) :
    -(T : ℝ) * Real.log (1 - 1 / (T : ℝ)) ≤ 2 := by
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have hi : 1 / (T : ℝ) < 1 := (div_lt_one ht0).2 (by linarith)
  have hb : 0 < 1 - 1 / (T : ℝ) := by linarith
  have hh := Real.log_le_sub_one_of_pos (inv_pos.2 hb)
  rw [Real.log_inv] at hh
  have hp := mul_le_mul_of_nonneg_left hh ht0.le
  have he : (T : ℝ) * ((1 - 1 / (T : ℝ))⁻¹ - 1) = T / (T - 1) := by
    have hm : (T : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hm]
    ring
  have hfrac : (T : ℝ) / (T - 1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  rw [he] at hp
  nlinarith

lemma decay_prefix_lower {T n : ℕ} (hT : 2 ≤ T) (hn : n ≤ T) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (T : ℝ)) ^ n := by
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have hi : 1 / (T : ℝ) ≤ 1 := (div_le_one ht0).2 (by linarith)
  exact (decay_power_lower hT).trans (pow_le_pow_of_le_one (by linarith)
    (by linarith [one_div_pos.2 ht0]) hn)

lemma momentum_ratio_step {b β m g v w : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hβ : 0 < β) (hv : 0 < v) (hw : β * v ≤ w) :
    (b * m + (1 - b) * g) ^ 2 / w ≤
      (b / β) * (m ^ 2 / v) + (1 - b) * (g ^ 2 / w) := by
  have hw0 : 0 < w := lt_of_lt_of_le (mul_pos hβ hv) hw
  calc
    _ ≤ (b * m ^ 2 + (1 - b) * g ^ 2) / w :=
      div_le_div_of_nonneg_right (momentum_square hb hb1) hw0.le
    _ = b * (m ^ 2 / w) + (1 - b) * (g ^ 2 / w) := by ring
    _ ≤ b * (m ^ 2 / (β * v)) + (1 - b) * (g ^ 2 / w) := by
      gcongr
    _ = _ := by field_simp

lemma weighted_path_sum {c A : ℝ} {u w : ℕ → ℝ} (hc : 0 ≤ c) (hu : ∀ t, 0 ≤ u t) (hu0 : u 0 = 0)
    (hrec : ∀ t, u (t + 1) ≤ c * u t + A * w t) (n : ℕ) :
    (1 - c) * ∑ t ∈ Finset.range n, u (t + 1) ≤
      A * ∑ t ∈ Finset.range n, w t := by
  have hsum : (1 - c) * ∑ t ∈ Finset.range n, u (t + 1) + c * u n ≤
      A * ∑ t ∈ Finset.range n, w t := by
    induction n with
    | zero => simp [hu0]
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hh := hrec n
        nlinarith
  exact le_trans (by nlinarith [mul_nonneg hc (hu n)]) hsum

lemma momentum_ratio_sum {b β γ : ℝ} {m v g : ℕ → ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hβ : 0 < β)
    (hbβ : (1 + b) / 2 ≤ β) (hγ : 0 ≤ γ) (hv : 0 < v 0)
    (hm0 : m 0 = 0)
    (hm : ∀ t, m (t + 1) = b * m t + (1 - b) * g t)
    (hrec : ∀ t, v (t + 1) = β * v t + γ * (g t) ^ 2) (n : ℕ) :
    ∑ t ∈ Finset.range n, (m (t + 1)) ^ 2 / v (t + 1) ≤
      2 * ∑ t ∈ Finset.range n, (g t) ^ 2 / v (t + 1) := by
  have hvp := accumulator_pos hβ hγ hv hrec
  have hh := weighted_path_sum (div_nonneg hb hβ.le)
    (u := fun t => (m t) ^ 2 / v t) (w := fun t => (g t) ^ 2 / v (t + 1))
    (A := 1 - b) (fun t => div_nonneg (sq_nonneg _) (hvp t).le) (by simp [hm0])
    (fun t => by
      rw [hm t]
      exact momentum_ratio_step hb hb1.le hβ (hvp t)
        (by rw [hrec t]; exact le_add_of_nonneg_right (mul_nonneg hγ (sq_nonneg _)))) n
  have hc : (1 - b) / 2 ≤ 1 - b / β := by
    have hp := mul_le_mul_of_nonneg_right hbβ (show 0 ≤ 1 + b by linarith)
    have hd : b / β ≤ (1 + b) / 2 := (div_le_iff₀ hβ).2 (by
      nlinarith [sq_nonneg (1 - b)])
    linarith
  have hu : 0 ≤ ∑ t ∈ Finset.range n, (m (t + 1)) ^ 2 / v (t + 1) :=
    Finset.sum_nonneg (fun t _ => div_nonneg (sq_nonneg _) (hvp (t + 1)).le)
  have hh' := mul_le_mul_of_nonneg_right hc hu
  have hp : 0 < 1 - b := sub_pos.2 hb1
  nlinarith

lemma ratio_log_bound {u C : ℝ} (hu : 0 < u) (huC : u ≤ C) (hC : 1 ≤ C) :
    |1 - u| ≤ C * |Real.log u| := by
  by_cases h : u ≤ 1
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonpos (Real.log_nonpos hu.le h)]
    have hh := Real.log_le_sub_one_of_pos hu
    have hp := mul_nonneg (sub_nonneg.2 hC) (neg_nonneg.2 (Real.log_nonpos hu.le h))
    nlinarith
  · have hu1 : 1 ≤ u := le_of_lt (lt_of_not_ge h)
    rw [abs_of_nonpos (sub_nonpos.2 hu1), abs_of_nonneg (Real.log_nonneg hu1)]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.2 hu)
    rw [Real.log_inv] at hh
    have hp := mul_le_mul_of_nonneg_left hh hu.le
    have he : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
    have hc := mul_le_mul_of_nonneg_right huC (Real.log_nonneg hu1)
    nlinarith

lemma log_variation {d : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ t, -c ≤ Real.log (d (t + 1)) - Real.log (d t)) (n : ℕ) :
    ∑ t ∈ Finset.range n, |Real.log (d (t + 1)) - Real.log (d t)| ≤
      Real.log (d n) - Real.log (d 0) + 2 * n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      have hh : |Real.log (d (n + 1)) - Real.log (d n)| ≤
          Real.log (d (n + 1)) - Real.log (d n) + 2 * c := by
        apply abs_le.2
        constructor <;> linarith [hstep n]
      linarith

lemma denominator_variation {d : ℕ → ℝ} {C c : ℝ} (hC : 1 ≤ C) (hc : 0 ≤ c)
    (hd : ∀ t, 0 < d t) (hratio : ∀ t, d t / d (t + 1) ≤ C)
    (hstep : ∀ t, -c ≤ Real.log (d (t + 1)) - Real.log (d t)) (n : ℕ) :
    ∑ t ∈ Finset.range n, |1 - d t / d (t + 1)| ≤
      C * (Real.log (d n) - Real.log (d 0) + 2 * n * c) := by
  calc
    _ ≤ ∑ t ∈ Finset.range n, C * |Real.log (d (t + 1)) - Real.log (d t)| := by
      apply Finset.sum_le_sum
      intro t _
      have hh := ratio_log_bound (div_pos (hd t) (hd (t + 1))) (hratio t) hC
      rw [Real.log_div (hd t).ne' (hd (t + 1)).ne'] at hh
      simpa only [abs_sub_comm (Real.log (d t)) (Real.log (d (t + 1)))] using hh
    _ = C * ∑ t ∈ Finset.range n, |Real.log (d (t + 1)) - Real.log (d t)| :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (log_variation hc hstep n) (by linarith)

lemma damped_denominator_decay {β v w τ : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hw : β * v ≤ w) (hτ : 0 ≤ τ) :
    Real.sqrt β * (Real.sqrt v + τ) ≤ Real.sqrt w + τ := by
  have hh := Real.sqrt_le_sqrt hw
  rw [Real.sqrt_mul hβ] at hh
  have hs : Real.sqrt β ≤ 1 := by
    nlinarith [Real.sq_sqrt hβ, Real.sqrt_nonneg β]
  nlinarith [mul_le_mul_of_nonneg_right hs hτ]

lemma damped_endpoint {v w τ B : ℝ} (hv : 0 ≤ v) (hw : w ≤ v * B)
    (hB : 1 ≤ B) (hτ : 0 ≤ τ) :
    Real.sqrt w + τ ≤ Real.sqrt B * (Real.sqrt v + τ) := by
  have hh := Real.sqrt_le_sqrt hw
  rw [Real.sqrt_mul hv] at hh
  have hs : 1 ≤ Real.sqrt B := by
    nlinarith [Real.sq_sqrt (show 0 ≤ B by linarith), Real.sqrt_nonneg B]
  nlinarith [mul_le_mul_of_nonneg_right hs hτ]

lemma damped_log_step {β v w τ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hv : 0 < v) (hw : β * v ≤ w) (hτ : 0 ≤ τ) :
    Real.log β / 2 ≤ Real.log (Real.sqrt w + τ) - Real.log (Real.sqrt v + τ) := by
  have hd : 0 < Real.sqrt v + τ := by positivity
  have hr : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hh := Real.log_le_log (mul_pos hr hd) (damped_denominator_decay hβ.le hβ1 hw hτ)
  rw [Real.log_mul hr.ne' hd.ne', Real.log_sqrt hβ.le] at hh
  linarith

lemma damped_ratio {β v w τ : ℝ} (hβ : 1 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hv : 0 < v) (hw : β * v ≤ w) (hτ : 0 ≤ τ) :
    (Real.sqrt v + τ) / (Real.sqrt w + τ) ≤ 2 := by
  have hβ0 : 0 < β := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (mul_pos hβ0 hv) hw
  have hd : 0 < Real.sqrt w + τ := by positivity
  have hh := damped_denominator_decay hβ0.le hβ1 hw hτ
  have hs : 1 / 2 ≤ Real.sqrt β := by
    nlinarith [Real.sq_sqrt hβ0.le, Real.sqrt_nonneg β]
  apply (div_le_iff₀ hd).2
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ Real.sqrt v + τ by positivity)
  linarith

lemma damped_variation_sum {β τ B : ℝ} {v : ℕ → ℝ}
    (hβ : 1 / 4 ≤ β) (hβ1 : β ≤ 1) (hτ : 0 ≤ τ) (hv : ∀ t, 0 < v t)
    (hrec : ∀ t, β * v t ≤ v (t + 1)) (n : ℕ)
    (hB : 1 ≤ B) (hvn : v n ≤ v 0 * B) (hlog : -(n : ℝ) * Real.log β ≤ 2) :
    ∑ t ∈ Finset.range n, |1 - (Real.sqrt (v t) + τ) / (Real.sqrt (v (t + 1)) + τ)| ≤
      3 * (2 + Real.log B) := by
  have hβ0 : 0 < β := by linarith
  have hl : Real.log β ≤ 0 := Real.log_nonpos hβ0.le hβ1
  have hd (t) : 0 < Real.sqrt (v t) + τ := by
    have ht := hv t
    positivity
  have hh := denominator_variation (d := fun t => Real.sqrt (v t) + τ)
    (C := 2) (c := -Real.log β / 2) (by norm_num) (by linarith) hd
    (fun t => damped_ratio hβ hβ1 (hv t) (hrec t) hτ)
    (fun t => by
      have ht := damped_log_step hβ0 hβ1 (hv t) (hrec t) hτ
      linarith) n
  have he := Real.log_le_log (hd n) (damped_endpoint (hv 0).le hvn hB hτ)
  rw [Real.log_mul (Real.sqrt_pos.2 (by linarith : 0 < B)).ne' (hd 0).ne',
    Real.log_sqrt (by linarith : 0 ≤ B)] at he
  have hb := Real.log_nonneg hB
  nlinarith

lemma damped_square_le {v τ m : ℝ} (hv : 0 < v) (hτ : 0 ≤ τ) :
    (m / (Real.sqrt v + τ)) ^ 2 ≤ m ^ 2 / v := by
  rw [div_pow]
  apply div_le_div_of_nonneg_left (sq_nonneg _) hv
  nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg v]

lemma normalized_square_budget {β γ B : ℝ} {v g : ℕ → ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hv : 0 < v 0)
    (hrec : ∀ t, v (t + 1) = β * v t + γ * (g t) ^ 2) (n : ℕ)
    (hB : 0 < B) (hvn : v n ≤ v 0 * B) (hlog : -(n : ℝ) * Real.log β ≤ 2) :
    ∑ t ∈ Finset.range n, (g t) ^ 2 / v (t + 1) ≤ (2 + Real.log B) / γ := by
  have hh := normalized_square_sum hβ hγ.le hv hrec n
  have hl := Real.log_le_log (accumulator_pos hβ hγ.le hv hrec n) hvn
  rw [Real.log_mul hv.ne' hB.ne'] at hl
  have he : (∑ t ∈ Finset.range n, γ * (g t) ^ 2 / v (t + 1)) =
      γ * ∑ t ∈ Finset.range n, (g t) ^ 2 / v (t + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he] at hh
  apply (le_div_iff₀ hγ).2
  nlinarith

lemma momentum_direction_bound {γ v τ m : ℝ} (hγ : 0 < γ) (hv : 0 < v)
    (hτ : 0 ≤ τ) (hm : γ * m ^ 2 ≤ v) :
    |m / (Real.sqrt v + τ)| ≤ 1 / Real.sqrt γ := by
  have hd : 0 < Real.sqrt v + τ := by positivity
  have hr : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hs : Real.sqrt γ * |m| ≤ Real.sqrt v := by
    have he : (Real.sqrt γ * |m|) ^ 2 = γ * m ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hγ.le, sq_abs]
    nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg v, abs_nonneg m,
      mul_nonneg hr.le (abs_nonneg m)]
  rw [abs_div, abs_of_pos hd]
  apply (div_le_div_iff₀ hd hr).2
  nlinarith

end LongTails.Proofs.AdamAccumulator
