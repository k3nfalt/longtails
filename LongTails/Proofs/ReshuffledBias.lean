import LongTails.Proofs.ReshuffledCoupledPaths
import LongTails.Proofs.ReshuffledCenteredLosses

set_option autoImplicit false

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledBias

open ReshuffledConvex ReshuffledExchange
open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n K : ℕ} [NeZero n]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma joint_exchange (f : Fin n → E → ℝ) (k : Fin K) (i : Fin n)
    (X Z : Orders n K → E) :
    n * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s))) -
      ∑ s, (f (s k i) (X s) - f (s k i) (Z s))) =
    ∑ j : Fin n, ∑ s : Orders n K,
      (f (s k i) (X (swapOrder k i j s)) - f (s k i) (X s) +
        f (s k i) (Z s) - f (s k i) (Z (swapOrder k i j s))) := by
  have h := centered_exchange k i (fun a s => f a (X s) - f a (Z s))
  have hl : (∑ s : Orders n K, ∑ a : Fin n, (f a (X s) - f a (Z s))) =
      n * ∑ s : Orders n K, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s)) := by
    simp only [sum_sub_distrib, sum_objective, ← mul_sum, mul_sub]
  rw [hl] at h
  calc
    _ = n * (∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s))) -
        n * ∑ s, (f (s k i) (X s) - f (s k i) (Z s)) := by ring
    _ = _ := h.trans (by
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro s _
      ring)

lemma joint_bias_from_swaps {f : Fin n → E → ℝ} {g : Fin n → E → E} {L η : ℝ}
    (hc : ∀ a, ConvexOn ℝ Set.univ (f a)) (hg : ∀ a x, HasGradientAt (f a) (g a x) x)
    (hlip : ∀ a x y, ‖g a x - g a y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hη : 0 < η) (hstep : η * L ≤ 1 / 6)
    (k : Fin K) (i : Fin n) (X Z : Orders n K → E)
    (D : Fin n → Orders n K → ℝ) (J : Fin n → ℝ)
    (hx : ∀ j, j.val < i.val → ∀ s, ‖X (swapOrder k i j s) - X s‖ ≤ η * D j s)
    (hz : ∀ j, j.val < i.val → ∀ s, ‖Z (swapOrder k i j s) - Z s‖ ≤ η * D j s)
    (hfuture : ∀ j, i.val ≤ j.val → ∀ s,
      X (swapOrder k i j s) = X s ∧ Z (swapOrder k i j s) = Z s)
    (hD : ∀ j, j.val < i.val → ∑ s, (D j s) ^ 2 ≤ 4 * J j) :
    n * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s))) -
      ∑ s, (f (s k i) (X s) - f (s k i) (Z s))) ≤
    n * (η * ∑ s, ‖g (s k i) (X s)‖ ^ 2 + η * ∑ s, ‖g (s k i) (Z s)‖ ^ 2) +
      (7 / 3 : ℝ) * η * ∑ j : Fin n, if j.val < i.val then J j else 0 := by
  classical
  rw [joint_exchange]
  have hp : ∀ j : Fin n,
      (∑ s : Orders n K,
        (f (s k i) (X (swapOrder k i j s)) - f (s k i) (X s) +
        f (s k i) (Z s) - f (s k i) (Z (swapOrder k i j s)))) ≤
        η * ∑ s, ‖g (s k i) (X s)‖ ^ 2 + η * ∑ s, ‖g (s k i) (Z s)‖ ^ 2 +
          (7 / 3 : ℝ) * η * (if j.val < i.val then J j else 0) := by
    intro j
    by_cases hj : j.val < i.val
    · rw [ite_eq_left hj]
      have hs := sum_le_sum (s := univ) (fun s _ =>
        ReshuffledAnchorCoupling.coupled_loss_difference (hc (s k i)) (hg (s k i)) (hlip (s k i))
          hL hη hstep (X s) (X (swapOrder k i j s)) (Z s) (Z (swapOrder k i j s))
          (hx j hj s) (hz j hj s))
      simp only [sum_add_distrib, ← mul_sum] at hs
      have hd := mul_le_mul_of_nonneg_left (hD j hj) (show 0 ≤ (7 / 12 : ℝ) * η by positivity)
      linarith
    · rw [ite_eq_right hj]
      have hf : ∀ s, X (swapOrder k i j s) = X s ∧ Z (swapOrder k i j s) = Z s :=
        hfuture j (by omega)
      simp only [fun s => (hf s).1, fun s => (hf s).2, sub_self, zero_add, sum_const_zero,
        mul_zero, add_zero]
      positivity
  have hs := sum_le_sum (s := univ) (fun j _ => hp j)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_sum, mul_add] using hs

omit [NeZero n] in
lemma reverse_bias_from_swaps {f : Fin n → E → ℝ} {g : Fin n → E → E} {η : ℝ}
    (hc : ∀ a, ConvexOn ℝ Set.univ (f a)) (hg : ∀ a x, HasGradientAt (f a) (g a x) x)
    (hη : 0 < η) (k : Fin K) (i : Fin n) (X : Orders n K → E)
    (D : Fin n → Orders n K → ℝ) (J : Fin n → ℝ)
    (hx : ∀ j, j.val < i.val → ∀ s, ‖X (swapOrder k i j s) - X s‖ ≤ η * D j s)
    (hfuture : ∀ j, i.val ≤ j.val → ∀ s, X (swapOrder k i j s) = X s)
    (hD : ∀ j, j.val < i.val → ∑ s, (D j s) ^ 2 ≤ 4 * J j) :
    n * (∑ s, f (s k i) (X s)) - (∑ s : Orders n K, ∑ a : Fin n, f a (X s)) ≤
      n * η * (∑ s, ‖g (s k i) (X s)‖ ^ 2) +
        η * (∑ j : Fin n, if j.val < i.val then J j else 0) := by
  classical
  have he := centered_exchange k i (fun a s => f a (X s))
  have hid : n * (∑ s, f (s k i) (X s)) - (∑ s : Orders n K, ∑ a : Fin n, f a (X s)) =
      ∑ j : Fin n, ∑ s : Orders n K, (f (s k i) (X s) - f (s k i) (X (swapOrder k i j s))) := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at he ⊢
    linarith
  rw [hid]
  have hp : ∀ j : Fin n,
      (∑ s : Orders n K, (f (s k i) (X s) - f (s k i) (X (swapOrder k i j s)))) ≤
        η * (∑ s, ‖g (s k i) (X s)‖ ^ 2) +
          η * (if j.val < i.val then J j else 0) := by
    intro j
    by_cases hj : j.val < i.val
    · rw [ite_eq_left hj]
      have hs := sum_le_sum (s := univ) (fun s _ =>
        ReshuffledAnchorCoupling.reverse_loss_difference (hc (s k i)) (hg (s k i))
          hη (X s) (X (swapOrder k i j s)) (hx j hj s))
      simp only [sum_add_distrib, ← sum_div, ← mul_sum] at hs
      have hd := mul_le_mul_of_nonneg_left (hD j hj) (show 0 ≤ η / 4 by positivity)
      linarith
    · rw [ite_eq_right hj]
      simp only [hfuture j (by omega), sub_self, sum_const_zero, mul_zero, add_zero]
      positivity
  have hs := sum_le_sum (s := univ) (fun j _ => hp j)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_sum, mul_assoc] using hs

lemma label_noise_sum {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (k : Fin K) (i : Fin n) :
    ∑ s : Orders n K, ‖g (s k i) xstar‖ ^ 2 ≤ Fintype.card (Orders n K) * σ ^ 2 := by
  have he := sum_label_mean_of_invariant k i (fun _ : Orders n K => xstar)
    (fun a x => ‖g a x‖ ^ 2) (fun _ _ => rfl)
  simp only [sum_const, card_univ, nsmul_eq_mul] at he
  have hn := ReshuffledConvex.card_pos' n
  have hb := mul_le_mul_of_nonneg_left h.sum_noise_le
    (Nat.cast_nonneg (Fintype.card (Orders n K)) : (0 : ℝ) ≤ _)
  have hf : (n : ℝ) * (∑ s : Orders n K, ‖g (s k i) xstar‖ ^ 2) ≤
      n * ((Fintype.card (Orders n K) : ℝ) * σ ^ 2) := by
    rw [he]
    nlinarith
  exact le_of_mul_le_mul_left hf hn

lemma joint_bias {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (hη : 0 < η k)
    (hstep : η k * Lmax ≤ 1 / 6) (w : ℕ → ℝ)
    (hw : ∀ t, t ≤ n * k.val + i.val → 0 < w t)
    (hmono : ∀ t, t < n * k.val + i.val → w t ≤ w (t + 1)) :
    let X := fun (s : Orders n K) => iterate g (schedule s) η x0
    let Z := fun (s : Orders n K) => anchor w (X s) xstar (n * k.val + i.val)
    n * ((∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (n * k.val + i.val)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s))) -
      ∑ s, (f (s k i) (X s (n * k.val + i.val)) - f (s k i) (Z s))) ≤
      n * (η k * (∑ s, ‖g (s k i) (X s (n * k.val + i.val))‖ ^ 2) +
        η k * (∑ s, ‖g (s k i) (Z s)‖ ^ 2)) +
        (7 / 3 : ℝ) * η k * (∑ j : Fin n, if j.val < i.val then
          ∑ s : Orders n K, ‖g (s k j) (X s (n * k.val + j.val))‖ ^ 2 else 0) := by
  dsimp only
  exact joint_bias_from_swaps h.convex h.grad h.lip_max h.lmax_pos.le hη hstep k i
    (fun s => iterate g (schedule s) η x0 (n * k.val + i.val))
    (fun s => anchor w (iterate g (schedule s) η x0) xstar (n * k.val + i.val))
    (fun j s => ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
      g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖)
    (fun j => ∑ s : Orders n K, ‖g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2)
    (fun j hj s => iterate_swap_norm h η x0 k i j hj hη (by linarith) s i.val le_rfl)
    (fun j hj s => anchor_swap_norm h η x0 k i j hj hη (by linarith) s w hw hmono)
    (fun j hj s => ⟨iterate_swap_before g η x0 k i j s _ (by omega),
      anchor_swap_before g η x0 xstar k i j s w _ (by omega)⟩)
    (fun j hj => gradient_swap_square_sum g η x0 k i j hj.le)

lemma centered_reverse_bias {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (hη : 0 < η k)
    (hstep : η k * Lmax ≤ 1) :
    let X := fun (s : Orders n K) => iterate g (schedule s) η x0
    n * ((∑ s, ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar (X s (n * k.val + i.val))) -
      ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (n * k.val + i.val)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) ≤
      2 * n * η k * Lmax * (∑ s,
        ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar (X s (n * k.val + i.val))) +
      η k * (∑ j : Fin n, if j.val < i.val then
        ∑ s : Orders n K, ‖g (s k j) (X s (n * k.val + j.val))‖ ^ 2 else 0) := by
  dsimp only
  have hb := reverse_bias_from_swaps
    (fun a => ReshuffledCentered.loss_convex (h.convex a) xstar)
    (fun a => ReshuffledCentered.loss_grad (h.grad a) xstar)
    hη k i (fun s => iterate g (schedule s) η x0 (n * k.val + i.val))
    (fun j s => ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
      g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖)
    (fun j => ∑ s : Orders n K, ‖g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2)
    (fun j hj s => iterate_swap_norm h η x0 k i j hj hη hstep s i.val le_rfl)
    (fun j hj s => iterate_swap_before g η x0 k i j s _ (by omega))
    (fun j hj => gradient_swap_square_sum g η x0 k i j hj.le)
  simp only [ReshuffledCentered.sum_loss h, ← mul_sum] at hb
  have hg2 := sum_le_sum (s := univ) (fun s _ =>
    ReshuffledCentered.centered_grad_sq h.lmax_pos (h.convex (s k i))
      (h.grad (s k i)) (h.lip_max (s k i)) xstar
      (iterate g (schedule s) η x0 (n * k.val + i.val)))
  rw [← mul_sum] at hg2
  have hm := mul_le_mul_of_nonneg_left hg2 (show 0 ≤ (n : ℝ) * η k by positivity)
  nlinarith

lemma sampled_grad_sq_sum {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (k : Fin K) (i : Fin n) (X : Orders n K → E) :
    (∑ s, ‖g (s k i) (X s)‖ ^ 2) ≤
      4 * Lmax * (∑ s, ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar (X s)) +
        2 * Fintype.card (Orders n K) * σ ^ 2 := by
  have hs := sum_le_sum (s := univ) (fun s _ =>
    ReshuffledCentered.grad_sq h.lmax_pos (h.convex (s k i)) (h.grad (s k i))
      (h.lip_max (s k i)) xstar (X s))
  simp only [sum_add_distrib, ← mul_sum] at hs
  have hn := label_noise_sum h k i
  linarith

lemma earlier_label_loss {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (u : ℕ) (hu : u ≤ n * k.val) :
    (∑ s : Orders n K, ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar
      (iterate g (schedule s) η x0 u)) =
      ∑ s : Orders n K,
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (iterate g (schedule s) η x0 u) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
  have he := sum_label_mean_of_invariant k i
    (fun s => iterate g (schedule s) η x0 u)
    (fun a x => ReshuffledCentered.loss (f a) (g a) xstar x)
    (fun j s => iterate_swap_before g η x0 k i j s u (by omega))
  simp only [ReshuffledCentered.sum_loss h, ← mul_sum] at he
  exact mul_left_cancel₀ (show (n : ℝ) ≠ 0 from (ReshuffledConvex.card_pos' n).ne') he

omit [CompleteSpace E] in
lemma same_epoch_label_loss (f : Fin n → E → ℝ) (g : Fin n → E → E)
    (η : ℕ → ℝ) (x0 xstar : E) (k : Fin K) (i j : Fin n) (hji : j.val ≤ i.val) :
    (∑ s : Orders n K, ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar
      (iterate g (schedule s) η x0 (n * k.val + j.val))) =
    ∑ s : Orders n K, ReshuffledCentered.loss (f (s k j)) (g (s k j)) xstar
      (iterate g (schedule s) η x0 (n * k.val + j.val)) := by
  exact sum_label_eq_of_invariant k i j
    (fun s => iterate g (schedule s) η x0 (n * k.val + j.val))
    (fun a x => ReshuffledCentered.loss (f a) (g a) xstar x)
    (fun s => iterate_swap_before g η x0 k i j s _ (by omega))

lemma label_inner (s : Orders n K) (k : Fin K) (i : Fin n) :
    schedule s ((n * k.val + i.val) / n)
      ⟨(n * k.val + i.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = s k i := by
  have hd : (n * k.val + i.val) / n = k.val := by
    rw [Nat.mul_add_div (NeZero.pos n), Nat.div_eq_of_lt i.isLt, add_zero]
  have hm : (n * k.val + i.val) % n = i.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hf : (⟨(n * k.val + i.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := Fin.ext hm
  rw [hd, hf]
  simp [schedule, k.isLt]

lemma past_label_loss {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (u : ℕ) (hu : u ≤ n * k.val + i.val) :
    (∑ s : Orders n K, ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar
      (iterate g (schedule s) η x0 u)) ≤
      (∑ s : Orders n K, ReshuffledCentered.loss
        (f (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩))
        (g (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩)) xstar
        (iterate g (schedule s) η x0 u)) +
      ∑ s : Orders n K,
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (iterate g (schedule s) η x0 u) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
  by_cases he : u ≤ n * k.val
  · rw [earlier_label_loss h η x0 k i u he]
    have ha : 0 ≤ ∑ s : Orders n K, ReshuffledCentered.loss
        (f (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩))
        (g (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩)) xstar
        (iterate g (schedule s) η x0 u) :=
      sum_nonneg fun s _ => ReshuffledCentered.loss_nonneg (h.convex _) (h.grad _) _ _
    linarith
  · let j : Fin n := ⟨u - n * k.val, by have := i.isLt; omega⟩
    have hj : j.val ≤ i.val := by dsimp [j]; omega
    have eu : u = n * k.val + j.val := by dsimp [j]; omega
    rw [eu, same_epoch_label_loss f g η x0 xstar k i j hj]
    simp_rw [label_inner]
    have hr : 0 ≤ ∑ s : Orders n K,
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (iterate g (schedule s) η x0 (n * k.val + j.val)) -
          LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := sum_nonneg fun s _ => h.gap_nonneg _
    linarith

end OracleTemplate.ReshuffledBias
