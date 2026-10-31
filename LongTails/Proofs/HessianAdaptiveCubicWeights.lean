import LongTails.Algorithms.HessianAdaptiveCubic
import Mathlib.Tactic

namespace LongTails.Proofs.HessianAdaptiveCubicWeights

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic

lemma mixing_pos (t : ℕ) : 0 < mixing t := by unfold mixing; positivity

lemma mixing_le_one {t : ℕ} (ht : 1 ≤ t) : mixing t ≤ 1 := by
  unfold mixing
  apply (div_le_one (by positivity)).2
  exact_mod_cast (show 4 ≤ t + 3 by omega)

lemma mixing_lt_one {t : ℕ} (ht : 1 < t) : mixing t < 1 := by
  unfold mixing
  apply (div_lt_one (by positivity)).2
  exact_mod_cast (show 4 < t + 3 by omega)

lemma mixing_inverse_le {t : ℕ} (ht : 1 ≤ t) : (mixing t)⁻¹ ≤ t := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  simp only [mixing, inv_div]
  linarith

lemma quadraticDamping_pos (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) : 0 < quadraticDamping p s := by
  have ht' : (0 : ℝ) < s.iteration := by exact_mod_cast (show 0 < s.iteration by omega)
  unfold quadraticDamping
  positivity

lemma damping_pos (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) : 0 < damping p s := by
  have hb := quadraticDamping_pos p s hD hκ ht
  unfold damping
  positivity

lemma increment_pos (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration)
    (hA : 0 < s.weight ∨ s.iteration = 1) : 0 < increment p s := by
  have hα := mixing_pos s.iteration
  have hτ := damping_pos p s hD hκ ht
  unfold increment
  split_ifs with hfirst
  · positivity
  · have hweight : 0 < s.weight := hA.resolve_right hfirst
    have hαone := mixing_lt_one (show 1 < s.iteration by omega)
    apply lt_min <;> positivity

lemma increment_damping_cap (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) :
    increment p s * (mixing s.iteration * damping p s) ≤ s.scale := by
  have hden := mul_pos (mixing_pos s.iteration) (damping_pos p s hD hκ ht)
  apply (le_div_iff₀ hden).mp
  unfold increment
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

lemma increment_weight_cap (p : Public) (s : State p.d) (ht : 1 ≤ s.iteration)
    (hA : 0 ≤ s.weight) :
    increment p s ≤ mixing s.iteration * (s.weight + increment p s) := by
  by_cases hfirst : s.iteration = 1
  · have hα : mixing s.iteration = 1 := by norm_num [hfirst, mixing]
    rw [hα]
    linarith
  · have hαone := mixing_lt_one (show 1 < s.iteration by omega)
    have hbound : increment p s ≤ mixing s.iteration * s.weight / (1 - mixing s.iteration) := by
      simp only [increment, ite_eq_right hfirst]
      exact min_le_left _ _
    have hh := (le_div_iff₀ (sub_pos.mpr hαone)).mp hbound
    nlinarith

lemma reciprocal_mixing_step {A a α : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hα : 0 ≤ α) (hαone : α ≤ 1) :
    (A + a)⁻¹ ≤ (1 - α) * A⁻¹ + α ^ 2 * a⁻¹ := by
  have hsum : 0 < A + a := by positivity
  apply (mul_le_mul_iff_of_pos_right (show 0 < A * a * (A + a) by positivity)).mp
  have hs := sq_nonneg ((1 - α) * a - α * A)
  have hp := mul_nonneg (mul_nonneg hα (sub_nonneg.mpr hαone))
    (show 0 ≤ a * (A + a) by positivity)
  field_simp
  nlinarith

lemma residual_weight_square {a α τ κ : ℝ} (ha : 0 ≤ a) (hα : 0 < α) (hτ : 0 < τ)
    (hcap : a * (α * τ) ≤ κ) : a ^ 2 ≤ κ * a / (α * τ) := by
  apply (le_div_iff₀ (mul_pos hα hτ)).2
  have h := mul_le_mul_of_nonneg_right hcap ha
  nlinarith

lemma normalized_movement_cap {a α τ κ q D : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hτ : 0 ≤ τ) (hκ : 0 < κ) (hq : 0 ≤ q) (hqD : q ≤ D)
    (hcap : a * (α * τ) ≤ κ) :
    0 ≤ (a * α * τ / κ) * q ^ 2 ∧ (a * α * τ / κ) * q ^ 2 ≤ D ^ 2 := by
  have hc : 0 ≤ a * α * τ / κ := by positivity
  have hc1 : a * α * τ / κ ≤ 1 := (div_le_one hκ).2 (by nlinarith)
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_right hc1 (sq_nonneg q)
    nlinarith

lemma advance_scale_floor (p : Public) (s : State p.d) (g : Point p.d) :
    p.σg * ((s.iteration + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2 ≤ (advance p s g).scale :=
  le_max_right _ _

lemma damping_ratio_bound (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) :
    s.scale / (mixing s.iteration * damping p s) ≤
      (s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D := by
  have ht' : (0 : ℝ) < s.iteration := by exact_mod_cast (show 0 < s.iteration by omega)
  have hb := quadraticDamping_pos p s hD hκ ht
  have hα := mixing_pos s.iteration
  have hτ : quadraticDamping p s ≤ damping p s := by
    unfold damping
    exact le_add_of_nonneg_right (mul_nonneg hκ.le (norm_nonneg _))
  calc
    _ ≤ s.scale / (mixing s.iteration * quadraticDamping p s) :=
      div_le_div_of_nonneg_left hκ.le (mul_pos hα hb)
        (mul_le_mul_of_nonneg_left hτ hα.le)
    _ = ((s.iteration : ℝ) * Real.sqrt s.iteration / p.D) * (mixing s.iteration)⁻¹ := by
      unfold quadraticDamping
      field_simp
    _ ≤ ((s.iteration : ℝ) * Real.sqrt s.iteration / p.D) * s.iteration :=
      mul_le_mul_of_nonneg_left (mixing_inverse_le ht) (by positivity)
    _ = _ := by ring

lemma increment_upper_bound (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) :
    increment p s ≤ (s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D := by
  apply le_trans _ (damping_ratio_bound p s hD hκ ht)
  unfold increment
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

lemma inverse_sqrt_step {t : ℝ} (ht : 1 ≤ t) :
    1 / Real.sqrt t ≤ 2 * (Real.sqrt t - Real.sqrt (t - 1)) := by
  have htpos : 0 < t := by linarith
  have hroot := Real.sqrt_pos.mpr htpos
  have hprev := Real.sqrt_nonneg (t - 1)
  have hsq := Real.sq_sqrt htpos.le
  have hpsq := Real.sq_sqrt (show 0 ≤ t - 1 by linarith)
  have hmono := Real.sqrt_le_sqrt (show t - 1 ≤ t by linarith)
  apply (div_le_iff₀ hroot).2
  have hp := mul_nonneg (sub_nonneg.mpr hmono) (sub_nonneg.mpr hmono)
  nlinarith

lemma inverse_weight_telescope (B e : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, 0 ≤ e n) (hbase : B 1 ≤ 128 * D)
    (hstep : ∀ n, 1 ≤ n → B (n + 1) ≤ B n + 64 * D / Real.sqrt (n + 1) + 256 * e (n + 1))
    (N : ℕ) (hN : 1 ≤ N) :
    B N ≤ 128 * D * Real.sqrt N + 256 * ∑ k ∈ Finset.range N, e (k + 1) := by
  have hb : ∀ n : ℕ, B (n + 1) ≤ 128 * D * Real.sqrt (n + 1) +
      256 * ∑ k ∈ Finset.range (n + 1), e (k + 1) := by
    intro n
    induction n with
    | zero => simpa using (show B 1 ≤ 128 * D + 256 * e 1 by linarith [he 1])
    | succ n ih =>
      have hs := hstep (n + 1) (by omega)
      have hr := inverse_sqrt_step (t := (n + 1 + 1 : ℕ)) (by exact_mod_cast (show 1 ≤ n + 1 + 1 by omega))
      have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 64 * D by positivity)
      have hcast : ((n + 1 + 1 : ℕ) : ℝ) - 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at hm
      rw [Finset.sum_range_succ]
      push_cast at hs hm ih ⊢
      simp only [mul_one_div] at hm
      nlinarith
  cases N with
  | zero => omega
  | succ n => simpa using hb n

lemma residualWeight_upper_bound (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) :
    residualWeight p s ≤ (s.iteration : ℝ) ^ 5 / p.D ^ 2 := by
  have hτ := damping_pos p s hD hκ ht
  have hα := mixing_pos s.iteration
  have hB : 0 ≤ (s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D := by positivity
  have hr : 0 ≤ s.scale / (mixing s.iteration * damping p s) := by positivity
  calc
    _ = increment p s * (s.scale / (mixing s.iteration * damping p s)) := by
      unfold residualWeight
      ring
    _ ≤ ((s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D) *
        ((s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D) :=
      mul_le_mul (increment_upper_bound p s hD hκ ht) (damping_ratio_bound p s hD hκ ht) hr hB
    _ = (s.iteration : ℝ) ^ 4 * (Real.sqrt s.iteration) ^ 2 / p.D ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]; ring

lemma scalar_residual_weight_caps {a α τ κ d : ℝ} (ha : 0 ≤ a) (hα : 0 < α)
    (hτ : 0 < τ) (hκ : 0 < κ) (hd : 0 ≤ d)
    (hcap : a * (α * τ) ≤ κ) (hdamp : κ * d ≤ τ) :
    (κ * a / (α * τ)) * d ^ 2 ≤ 1 / α ^ 2 ∧
      (κ * a / (α * τ)) * d ^ 4 ≤ (a * τ / (α * κ)) * d ^ 2 := by
  have hsq := mul_self_le_mul_self (mul_nonneg hκ.le hd) hdamp
  have hm := mul_le_mul_of_nonneg_left hcap (show 0 ≤ κ * d ^ 2 by positivity)
  have hmain : κ * a * α * d ^ 2 ≤ τ := by nlinarith
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hα)).2
    have hid : (κ * a / (α * τ) * d ^ 2) * α ^ 2 = (κ * a * d ^ 2 * α ^ 2) / (α * τ) := by ring
    rw [hid]
    apply (div_le_iff₀ (mul_pos hα hτ)).2
    have h := mul_le_mul_of_nonneg_left hmain hα.le
    nlinarith
  · apply (mul_le_mul_iff_of_pos_right (show 0 < α * τ * κ by positivity)).mp
    have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ a * d ^ 2 by positivity)
    field_simp
    nlinarith

lemma increment_sqrt_weight_cap (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hκ : 0 < s.scale) (ht : 1 ≤ s.iteration) :
    increment p s * Real.sqrt (residualWeight p s) ≤ (s.iteration : ℝ) ^ 5 / p.D ^ 2 := by
  let B := (s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBs : B ^ 2 = (s.iteration : ℝ) ^ 5 / p.D ^ 2 := by
    dsimp [B]
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hw : Real.sqrt (residualWeight p s) ≤ B := by
    apply (Real.sqrt_le_left hB).2
    rw [hBs]
    exact residualWeight_upper_bound p s hD hκ ht
  calc
    _ ≤ B * B := mul_le_mul (increment_upper_bound p s hD hκ ht) hw
      (Real.sqrt_nonneg _) hB
    _ = _ := by rw [← sq, hBs]

end LongTails.Proofs.HessianAdaptiveCubicWeights
