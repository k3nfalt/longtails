import LongTails.Proofs.ReshuffledBias

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledLastStep

open ReshuffledConvex
open LongTails.Setups.ReshuffledSmoothConvex

lemma scalar_step {n η L R Rnext Φ C D Q M N B P : ℝ}
    (hn : 0 < n) (hη : 0 ≤ η)
    (hb : n * (R - Φ - C) ≤ n * (η * M + η * N) + (7 / 3 : ℝ) * η * P)
    (hd : Q = D - 2 * η * C + η ^ 2 * M - 2 * η * B)
    (hr : Rnext ≤ R + η * L * R + η / 2 * (1 + η * L) * M) :
    2 * η * (Rnext - Φ) ≤ D - Q + (4 + η * L) * η ^ 2 * M +
      2 * η ^ 2 * N + (14 / (3 * n)) * η ^ 2 * P + 2 * η ^ 2 * L * R - 2 * η * B := by
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η by positivity)
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * n * η by positivity)
  apply le_of_mul_le_mul_left (a := n) _ hn
  field_simp [hn.ne']
  nlinarith

lemma gradient_transfer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x z : E) :
    ‖g x‖ ^ 2 ≤ 4 * L * ReshuffledCentered.loss f g x z + 2 * ‖g z‖ ^ 2 := by
  have hb := ReshuffledCentered.centered_grad_sq hL hc hg hlip x z
  rw [norm_sub_rev (g z) (g x)] at hb
  have ht : ‖g x‖ ≤ ‖g x - g z‖ + ‖g z‖ := by
    simpa using norm_add_le (g x - g z) (g z)
  nlinarith [sq_nonneg (‖g x - g z‖ - ‖g z‖), norm_nonneg (g x),
    norm_nonneg (g x - g z), norm_nonneg (g z)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n K : ℕ} [NeZero n]

lemma one_step {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (hη : 0 < η k)
    (hstep : η k * Lmax ≤ 1 / 6) (w : ℕ → ℝ)
    (hw : ∀ t, t ≤ n * k.val + i.val → 0 < w t)
    (hmono : ∀ t, t < n * k.val + i.val → w t ≤ w (t + 1)) :
    let t := n * k.val + i.val
    let X := fun (s : Orders n K) => iterate g (schedule s) η x0
    let Z := fun (s : Orders n K) => anchor w (X s) xstar t
    2 * η k * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (t + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) -
        ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) ≤
      (∑ s, ‖X s t - Z s‖ ^ 2) - (∑ s, ‖X s (t + 1) - Z s‖ ^ 2) +
      (4 + η k * Lmax) * (η k) ^ 2 * (∑ s, ‖g (s k i) (X s t)‖ ^ 2) +
      2 * (η k) ^ 2 * (∑ s, ‖g (s k i) (Z s)‖ ^ 2) +
      (14 / (3 * (n : ℝ))) * (η k) ^ 2 * (∑ j : Fin n, if j.val < i.val then
        ∑ s : Orders n K, ‖g (s k j) (X s (n * k.val + j.val))‖ ^ 2 else 0) +
      2 * (η k) ^ 2 * Lmax * (∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s t) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) -
      2 * η k * (∑ s, ReshuffledCentered.loss (f (s k i)) (g (s k i)) (X s t) (Z s)) := by
  dsimp only
  let X := fun (s : Orders n K) => iterate g (schedule s) η x0
  let t := n * k.val + i.val
  let Z := fun (s : Orders n K) => anchor w (X s) xstar t
  have hx : ∀ s : Orders n K, X s (t + 1) = X s t - η k • g (s k i) (X s t) := by
    intro s
    dsimp [X, t]
    rw [Nat.add_assoc, iterate_inner g (schedule s) η x0 k.val i.val i.isLt]
    simp [schedule, k.isLt]
  have hb := ReshuffledBias.joint_bias h η x0 k i hη hstep w hw hmono
  change n * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s t) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s))) -
      ∑ s, (f (s k i) (X s t) - f (s k i) (Z s))) ≤ _ at hb
  have hd : (∑ s : Orders n K, ‖X s (t + 1) - Z s‖ ^ 2) =
      (∑ s, ‖X s t - Z s‖ ^ 2) - 2 * η k * (∑ s, (f (s k i) (X s t) - f (s k i) (Z s))) +
        (η k) ^ 2 * (∑ s, ‖g (s k i) (X s t)‖ ^ 2) -
        2 * η k * (∑ s, ReshuffledCentered.loss (f (s k i)) (g (s k i)) (X s t) (Z s)) := by
    calc
      _ = ∑ s : Orders n K, (‖X s t - Z s‖ ^ 2 -
          2 * η k * (f (s k i) (X s t) - f (s k i) (Z s)) +
          (η k) ^ 2 * ‖g (s k i) (X s t)‖ ^ 2 -
          2 * η k * ReshuffledCentered.loss (f (s k i)) (g (s k i)) (X s t) (Z s)) := by
        apply sum_congr rfl
        intro s hs
        rw [hx s]
        exact ReshuffledCentered.step_identity (f (s k i)) (g (s k i)) (η k) (X s t) (Z s)
      _ = _ := by simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hr := sum_le_sum (s := univ) (fun s _ =>
    ReshuffledCentered.objective_next_gap h hη.le (X s t) (g (s k i) (X s t)))
  simp only [← hx, sum_add_distrib, ← mul_sum] at hr
  have hb' : n * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s t) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) -
      (∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) -
      ∑ s, (f (s k i) (X s t) - f (s k i) (Z s))) ≤
      n * (η k * (∑ s, ‖g (s k i) (X s t)‖ ^ 2) +
        η k * (∑ s, ‖g (s k i) (Z s)‖ ^ 2)) +
        (7 / 3 : ℝ) * η k * (∑ j : Fin n, if j.val < i.val then
          ∑ s : Orders n K, ‖g (s k j) (X s (n * k.val + j.val))‖ ^ 2 else 0) := by
    simpa only [sum_sub_distrib, sub_sub_sub_cancel_right] using hb
  exact scalar_step (ReshuffledConvex.card_pos' n) hη.le hb' hd hr

end OracleTemplate.ReshuffledLastStep
