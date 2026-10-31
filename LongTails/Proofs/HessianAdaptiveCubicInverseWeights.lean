import LongTails.Proofs.HessianAdaptiveCubicWeights
import LongTails.Proofs.HessianAdaptiveCubicStep
import LongTails.Proofs.HessianAdaptiveCubicExecution
import Mathlib.Algebra.Order.Chebyshev

namespace LongTails.Proofs.HessianAdaptiveCubicInverseWeights

open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicWeights

def weightPolynomial (t : ℕ) : ℝ := (t : ℝ) * (t + 1) * (t + 2) * (t + 3)

lemma weightPolynomial_nonneg (t : ℕ) : 0 ≤ weightPolynomial t := by
  unfold weightPolynomial
  positivity

lemma weightPolynomial_pos {t : ℕ} (ht : 1 ≤ t) : 0 < weightPolynomial t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  unfold weightPolynomial
  positivity

lemma weightPolynomial_mixing (n : ℕ) :
    weightPolynomial (n + 1) * (1 - mixing (n + 1)) = weightPolynomial n := by
  unfold weightPolynomial mixing
  push_cast
  field_simp
  ring

lemma weightPolynomial_cubic (t : ℕ) :
    weightPolynomial t * mixing t ^ 3 ≤ 64 * t := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  unfold weightPolynomial mixing
  have hden : 0 < (t : ℝ) + 3 := by positivity
  apply (mul_le_mul_iff_of_pos_right (pow_pos hden 3)).mp
  field_simp
  nlinarith [sq_nonneg (t : ℝ), pow_nonneg ht 3]

lemma weightPolynomial_quartic (t : ℕ) :
    weightPolynomial t * mixing t ^ 4 ≤ 256 := by
  have h := mul_le_mul_of_nonneg_right (weightPolynomial_cubic t) (mixing_pos t).le
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm : (t : ℝ) * mixing t ≤ 4 := by
    unfold mixing
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (t : ℝ) + 3)).2
    linarith
  calc
    _ = (weightPolynomial t * mixing t ^ 3) * mixing t := by ring
    _ ≤ (64 * t) * mixing t := h
    _ ≤ 256 := by linarith

lemma weightPolynomial_damping {t : ℕ} (ht : 1 ≤ t) {D : ℝ} (hD : 0 ≤ D) :
    weightPolynomial t * (D * mixing t ^ 3 / ((t : ℝ) * Real.sqrt t)) ≤
      64 * D / Real.sqrt t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hroot : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht'
  have hm := mul_le_mul_of_nonneg_right (weightPolynomial_cubic t) hD
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos ht' hroot) hroot).2
  have h := mul_le_mul_of_nonneg_right hm hroot.le
  nlinarith

lemma inverse_weight_from_recurrence (A e : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, 0 ≤ e n) (hbase : weightPolynomial 1 * (A 1)⁻¹ ≤ 128 * D)
    (hstep : ∀ n, 1 ≤ n → (A (n + 1))⁻¹ ≤
      (1 - mixing (n + 1)) * (A n)⁻¹ +
      D * mixing (n + 1) ^ 3 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (n + 1)) +
      mixing (n + 1) ^ 4 * e (n + 1)) (N : ℕ) (hN : 1 ≤ N) :
    weightPolynomial N * (A N)⁻¹ ≤
      128 * D * Real.sqrt N + 256 * ∑ k ∈ Finset.range N, e (k + 1) := by
  apply inverse_weight_telescope (fun n => weightPolynomial n * (A n)⁻¹) e hD he hbase _ N hN
  intro n hn
  have h := mul_le_mul_of_nonneg_left (hstep n hn) (weightPolynomial_nonneg (n + 1))
  have hd := weightPolynomial_damping (t := n + 1) (by omega) hD
  have he' := mul_le_mul_of_nonneg_right (weightPolynomial_quartic (n + 1)) (he (n + 1))
  have hp := congrArg (fun x : ℝ => x * (A n)⁻¹) (weightPolynomial_mixing n)
  push_cast at hd h
  nlinarith only [h, hd, he', hp]

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicStep

lemma damped_displacement (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hs : Invariant p s)
    (ha : increment p s = s.scale / (mixing s.iteration * damping p s)) :
    ‖displacement s‖ = mixing s.iteration * Real.sqrt (movement p s) := by
  have hα := mixing_pos s.iteration
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have hκ := hs.scale
  have hV : movement p s = ‖s.trial - s.dual‖ ^ 2 := by
    unfold movement
    rw [ha]
    field_simp
  rw [hV, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [displacement, norm_smul, Real.norm_eq_abs, abs_of_pos hα]

lemma reciprocal_state_step (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hs : Invariant p s) (ht : 1 < s.iteration) :
    (s.weight + increment p s)⁻¹ ≤ (1 - mixing s.iteration) * s.weight⁻¹ +
      p.D * mixing s.iteration ^ 3 / ((s.iteration : ℝ) * Real.sqrt s.iteration) +
      mixing s.iteration ^ 4 * Real.sqrt (movement p s) := by
  have hα := mixing_pos s.iteration
  have hαone := mixing_lt_one ht
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have hκ := hs.scale
  have hA : 0 < s.weight := hs.weight_pos.resolve_right (by omega)
  have hneq : s.iteration ≠ 1 := by omega
  by_cases hc : mixing s.iteration * s.weight / (1 - mixing s.iteration) ≤
      s.scale / (mixing s.iteration * damping p s)
  · have ha : increment p s = mixing s.iteration * s.weight / (1 - mixing s.iteration) := by
      unfold increment
      rw [ite_eq_right hneq, min_eq_left hc]
    have hsum : s.weight + increment p s = s.weight / (1 - mixing s.iteration) := by
      rw [ha]
      field_simp [ne_of_gt (sub_pos.mpr hαone)]
      ring
    rw [hsum, inv_div]
    have hrest : 0 ≤ p.D * mixing s.iteration ^ 3 /
        ((s.iteration : ℝ) * Real.sqrt s.iteration) +
        mixing s.iteration ^ 4 * Real.sqrt (movement p s) := by positivity
    simp only [div_eq_mul_inv]
    simp only [div_eq_mul_inv] at hrest
    linarith
  · have ha : increment p s = s.scale / (mixing s.iteration * damping p s) := by
      unfold increment
      rw [ite_eq_right hneq, min_eq_right (le_of_not_ge hc)]
    have he := damped_displacement p s hD hs ha
    have hb := reciprocal_mixing_step hA
      (increment_pos p s hD hs.scale hs.iteration hs.weight_pos) hα.le hαone.le
    have hterm : mixing s.iteration ^ 2 * (increment p s)⁻¹ =
        p.D * mixing s.iteration ^ 3 / ((s.iteration : ℝ) * Real.sqrt s.iteration) +
        mixing s.iteration ^ 4 * Real.sqrt (movement p s) := by
      rw [ha, inv_div]
      unfold damping quadraticDamping
      rw [he]
      field_simp
    rw [hterm] at hb
    linarith

lemma initial_inverse_weight (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hs : Invariant p s) (ht : s.iteration = 1) (hA : s.weight = 0)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    weightPolynomial 1 * (s.weight + increment p s)⁻¹ ≤ 128 * p.D := by
  have hκ := hs.scale
  have hd := displacement_bound p s hs hdiam
  rw [ht] at hd
  norm_num [mixing] at hd
  have he : (s.weight + increment p s)⁻¹ = p.D + ‖displacement s‖ := by
    rw [hA, zero_add]
    unfold increment damping quadraticDamping
    rw [ht]
    norm_num [mixing]
    field_simp
  rw [he]
  norm_num [weightPolynomial]
  nlinarith

open LongTails.Proofs.HessianAdaptiveCubicExecution

lemma inverse_round_weight {Ω : Type*} (p : Public)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (ξ : ℕ → Ω) (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) (N : ℕ) (hN : 1 ≤ N) :
    weightPolynomial N * (roundState p g H ξ N).weight⁻¹ ≤
      128 * p.D * Real.sqrt N +
        256 * ∑ k ∈ Finset.range N, Real.sqrt (movement p (modelAt p g H ξ k)) := by
  let A := fun n => (roundState p g H ξ n).weight
  let e := fun n => Real.sqrt (movement p (modelAt p g H ξ (n - 1)))
  have hbase : weightPolynomial 1 * (A 1)⁻¹ ≤ 128 * p.D := by
    have hb := initial_inverse_weight p (modelAt p g H ξ 0) hD
      (modelAt_invariant p g H ξ hD hρ hσ hx 0) rfl rfl hdiam
    exact hb
  have hrec : ∀ n, 1 ≤ n → (A (n + 1))⁻¹ ≤
      (1 - mixing (n + 1)) * (A n)⁻¹ +
      p.D * mixing (n + 1) ^ 3 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (n + 1)) +
      mixing (n + 1) ^ 4 * e (n + 1) := by
    intro n hn
    have hs := modelAt_invariant p g H ξ hD hρ hσ hx n
    have ht : (modelAt p g H ξ n).iteration = n + 1 := roundState_iteration p g H ξ n
    have hb := reciprocal_state_step p (modelAt p g H ξ n) hD hs (by rw [ht]; omega)
    rw [ht] at hb
    have hw : (modelAt p g H ξ n).weight = (roundState p g H ξ n).weight := rfl
    have hwnew : (roundState p g H ξ (n + 1)).weight =
        (modelAt p g H ξ n).weight + increment p (modelAt p g H ξ n) := rfl
    simpa only [A, e, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hwnew, hw] using hb
  have hb := inverse_weight_from_recurrence A e hD.le (fun _ => Real.sqrt_nonneg _) hbase hrec N hN
  simpa only [A, e, Nat.add_sub_cancel] using hb

lemma weightPolynomial_power (t : ℕ) : (t : ℝ) ^ 4 ≤ weightPolynomial t := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  unfold weightPolynomial
  nlinarith [sq_nonneg (t : ℝ), pow_nonneg ht 3]

lemma sqrt_sum_square (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.sqrt (V n)) ^ 2 ≤ (N : ℝ) * ∑ n ∈ Finset.range N, V n := by
  simpa only [Finset.card_range, Real.sq_sqrt (hV _)] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => Real.sqrt (V n)))

lemma inverse_square_of_potential (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) (N : ℕ) (hN : 1 ≤ N)
    {D X : ℝ} (hX : 0 ≤ X)
    (hpot : weightPolynomial N * X ≤ 128 * D * Real.sqrt N +
      256 * ∑ n ∈ Finset.range N, Real.sqrt (V n)) :
    X ^ 2 * (N : ℝ) ^ 7 ≤ 32768 * D ^ 2 + 131072 * ∑ n ∈ Finset.range N, V n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlow := mul_le_mul_of_nonneg_right (weightPolynomial_power N) hX
  have hb := hlow.trans hpot
  have hsq := mul_self_le_mul_self (show 0 ≤ (N : ℝ) ^ 4 * X by positivity) hb
  have hc := sqrt_sum_square V hV N
  have hcross := sq_nonneg (128 * D * Real.sqrt N -
    256 * ∑ n ∈ Finset.range N, Real.sqrt (V n))
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  apply (mul_le_mul_iff_of_pos_left hNp).mp
  nlinarith only [hsq, hc, hcross, hsqrt]

end LongTails.Proofs.HessianAdaptiveCubicInverseWeights
