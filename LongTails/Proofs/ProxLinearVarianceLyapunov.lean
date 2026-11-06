import Mathlib.Tactic

namespace LongTails.Proofs.ProxLinearVarianceLyapunov

lemma coupled_step {φ φnext V Vnext b t a C β w q N : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 ≤ b) (hV : 0 ≤ V) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hweight : w * β = 12 * a * C)
    (hsmall : w * q ≤ 3 * a / 16)
    (hdescent : φnext ≤ φ - a * b + 6 * a * C * (V + t))
    (hvariance : Vnext ≤ (1 - β) * V + N + q * (b + C * (V + t))) :
    φnext + w * Vnext ≤ φ + w * V - a / 2 * b + 7 * a * C * t + w * N := by
  have hscaled := mul_le_mul_of_nonneg_left hvariance hw
  have hsum : 0 ≤ b + C * (V + t) :=
    add_nonneg hb (mul_nonneg hC (add_nonneg hV ht))
  have hq := mul_le_mul_of_nonneg_right hsmall hsum
  have hcancel := congrArg (fun r : ℝ => r * V) hweight
  have hab := mul_nonneg ha hb
  have haCV := mul_nonneg (mul_nonneg ha hC) hV
  have haCt := mul_nonneg (mul_nonneg ha hC) ht
  nlinarith

lemma sum_steps_le_gap {L b : ℕ → ℝ} {c K lower : ℝ}
    (hstep : ∀ t, L (t + 1) ≤ L t - c * b t + K) (T : ℕ)
    (hlower : lower ≤ L T) :
    c * ∑ t ∈ Finset.range T, b t ≤ L 0 - lower + (T : ℝ) * K := by
  have hsum : ∀ n : ℕ, c * ∑ t ∈ Finset.range n, b t ≤ L 0 - L n + (n : ℝ) * K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, Nat.cast_add, Nat.cast_one]
        linarith [hstep n]
  linarith [hsum T]

lemma average_bound {L b : ℕ → ℝ} {a C β Δ V0 τ σ w lower : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hw : w * β = 12 * a * C)
    (hstep : ∀ t, L (t + 1) ≤ L t - a / 2 * b t +
      (7 * a * C * τ ^ 2 + 2 * w * β ^ 2 * σ ^ 2))
    (hinit : L 0 - lower ≤ Δ + w * V0) (T : ℕ) (hT : 0 < T)
    (hlower : lower ≤ L T) :
    (∑ t ∈ Finset.range T, b t) / T ≤ 2 * Δ / (a * T) +
      24 * C * V0 / (β * T) + 48 * C * β * σ ^ 2 + 14 * C * τ ^ 2 := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  let R := 2 * Δ / (a * T) + 24 * C * V0 / (β * T) +
    48 * C * β * σ ^ 2 + 14 * C * τ ^ 2
  have hs := sum_steps_le_gap hstep T hlower
  have hs' : (a / 2) * ∑ t ∈ Finset.range T, b t ≤ Δ + w * V0 +
      (T : ℝ) * (7 * a * C * τ ^ 2 + 2 * w * β ^ 2 * σ ^ 2) := by linarith
  have hw' : w = 12 * a * C / β := (eq_div_iff hβ.ne').2 hw
  have hcancel : (a / 2) * ((T : ℝ) * R) = Δ + w * V0 +
      (T : ℝ) * (7 * a * C * τ ^ 2 + 2 * w * β ^ 2 * σ ^ 2) := by
    rw [hw']
    dsimp [R]
    field_simp [ha.ne', hβ.ne', hTr.ne']
    ring
  have hscaled : (a / 2) * ∑ t ∈ Finset.range T, b t ≤ (a / 2) * ((T : ℝ) * R) := by
    rw [hcancel]
    exact hs'
  have hsfinal := (mul_le_mul_iff_right₀ (show 0 < a / 2 by positivity)).mp hscaled
  change (∑ t ∈ Finset.range T, b t) / T ≤ R
  apply (div_le_iff₀ hTr).2
  exact hsfinal.trans_eq (mul_comm _ _)

lemma tuned_average_small {a C β Δ V0 τ σ r T : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T)
    (hgap : 1024 * Δ ≤ a * T * r ^ 2)
    (hinit : 1024 * C * V0 ≤ r ^ 2) (hhorizon : 64 ≤ β * T)
    (hnoise : 32768 * C * β * σ ^ 2 ≤ r ^ 2)
    (hbias : 65536 * C * τ ^ 2 = r ^ 2) :
    2 * Δ / (a * T) + 24 * C * V0 / (β * T) +
      48 * C * β * σ ^ 2 + 14 * C * τ ^ 2 ≤ r ^ 2 / 128 := by
  have hfirst : 2 * Δ / (a * T) ≤ r ^ 2 / 512 := by
    apply (div_le_iff₀ (mul_pos ha hT)).mpr
    nlinarith
  have hsecond : 24 * C * V0 / (β * T) ≤ 3 * r ^ 2 / 8192 := by
    apply (div_le_iff₀ (mul_pos hβ hT)).mpr
    have hmul := mul_le_mul_of_nonneg_left hhorizon (sq_nonneg r)
    nlinarith
  have hthird : 48 * C * β * σ ^ 2 ≤ 3 * r ^ 2 / 2048 := by nlinarith
  have hfourth : 14 * C * τ ^ 2 = 7 * r ^ 2 / 32768 := by nlinarith
  nlinarith [sq_nonneg r]

end LongTails.Proofs.ProxLinearVarianceLyapunov
