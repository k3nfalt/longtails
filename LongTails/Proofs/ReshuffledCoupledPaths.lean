import LongTails.Proofs.ReshuffledExchange
import LongTails.Proofs.ReshuffledConvergence

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledExchange

open ReshuffledConvex
open LongTails.Setups.ReshuffledSmoothConvex

variable {n K : ℕ}

lemma schedule_swap_at (k : Fin K) (i j : Fin n) (s : Orders n K) :
    schedule (swapOrder k i j s) k = (Equiv.swap i j).trans (s k) := by
  simp only [schedule, dite_eq_left k.isLt]
  apply Equiv.ext
  intro a
  exact swapOrder_at k i j s a

lemma schedule_swap_other (k : Fin K) (i j : Fin n) (s : Orders n K) (u : ℕ)
    (hu : u ≠ k.val) : schedule (swapOrder k i j s) u = schedule s u := by
  unfold schedule
  split
  · have hfin : (⟨u, by assumption⟩ : Fin K) ≠ k := by
      intro he
      exact hu (congrArg Fin.val he)
    exact swapOrder_other _ _ hfin _ _ _
  · rfl

variable [NeZero n]

lemma swap_label_before (k : Fin K) (i j : Fin n) (s : Orders n K) (u : ℕ)
    (hu : u < n * k.val + min i.val j.val) :
    schedule (swapOrder k i j s) (u / n) ⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩ =
      schedule s (u / n) ⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩ := by
  by_cases he : u / n = k.val
  · rw [he, schedule_swap_at]
    have hid : u = n * k.val + u % n := by
      have h := Nat.mod_add_div u n
      rw [he] at h
      omega
    have hi : (⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩ : Fin n) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    have hj : (⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩ : Fin n) ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hi hj, schedule, k.isLt,
      dite_eq_left]
  · rw [schedule_swap_other k i j s (u / n) he]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma iterate_eq_of_labels (g : Fin n → E → E) (a b : ℕ → Equiv.Perm (Fin n))
    (η : ℕ → ℝ) (x0 : E) (t : ℕ)
    (h : ∀ u, u < t → a (u / n) ⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩ =
      b (u / n) ⟨u % n, Nat.mod_lt u (NeZero.pos n)⟩) :
    iterate g a η x0 t = iterate g b η x0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterate]
    rw [ih (fun u hu => h u (by omega)), h t (by omega)]

omit [CompleteSpace E] in
lemma iterate_swap_before (g : Fin n → E → E) (η : ℕ → ℝ) (x0 : E)
    (k : Fin K) (i j : Fin n) (s : Orders n K) (t : ℕ)
    (ht : t ≤ n * k.val + min i.val j.val) :
    iterate g (schedule (swapOrder k i j s)) η x0 t = iterate g (schedule s) η x0 t := by
  apply iterate_eq_of_labels
  intro u hu
  exact swap_label_before k i j s u (lt_of_lt_of_le hu ht)

lemma iterate_swap_norm {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i j : Fin n) (hji : j.val < i.val)
    (hη : 0 < η k) (hstep : η k * Lmax ≤ 1) (s : Orders n K) (q : ℕ)
    (hqi : q ≤ i.val) :
    ‖iterate g (schedule (swapOrder k i j s)) η x0 (n * k.val + q) -
        iterate g (schedule s) η x0 (n * k.val + q)‖ ≤
      η k * ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ := by
  induction q with
  | zero =>
    rw [iterate_swap_before g η x0 k i j s (n * k.val + 0) (by omega), sub_self, norm_zero]
    positivity
  | succ q ih =>
    by_cases hqj : q + 1 ≤ j.val
    · rw [iterate_swap_before g η x0 k i j s (n * k.val + (q + 1)) (by omega),
        sub_self, norm_zero]
      positivity
    have hqn : q < n := lt_of_lt_of_le (by omega : q < i.val) i.isLt.le
    have hsched : schedule s k = s k := by simp [schedule, k.isLt]
    rw [iterate_inner g (schedule (swapOrder k i j s)) η x0 k.val q hqn,
      iterate_inner g (schedule s) η x0 k.val q hqn, schedule_swap_at, hsched]
    by_cases heq : q = j.val
    · subst q
      have hefin : (⟨j.val, hqn⟩ : Fin n) = j := Fin.ext rfl
      rw [hefin]
      simp only [Equiv.trans_apply, Equiv.swap_apply_right]
      rw [iterate_swap_before g η x0 k i j s (n * k.val + j.val) (by omega)]
      have he : (iterate g (schedule s) η x0 (n * k.val + j.val) -
          η k • g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val))) -
          (iterate g (schedule s) η x0 (n * k.val + j.val) -
          η k • g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))) =
          -(η k • (g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
          g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val)))) := by module
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    · have hfi : (⟨q, hqn⟩ : Fin n) ≠ i := by intro he; have := congrArg Fin.val he; simp at this; omega
      have hfj : (⟨q, hqn⟩ : Fin n) ≠ j := by intro he; exact heq (congrArg Fin.val he)
      simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hfi hfj]
      exact (ReshuffledAnchorCoupling.step_nonexpansive (h.convex _) (h.grad _) (h.lip_max _)
        hη hstep _ _).trans (ih (by omega))

lemma iterate_swap_norm_prefix {f : Fin n → E → ℝ} {g : Fin n → E → E}
    {ℓ : Fin n → ℝ} {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i j : Fin n) (hji : j.val < i.val)
    (hη : 0 < η k) (hstep : η k * Lmax ≤ 1) (s : Orders n K) (t : ℕ)
    (ht : t ≤ n * k.val + i.val) :
    ‖iterate g (schedule (swapOrder k i j s)) η x0 t - iterate g (schedule s) η x0 t‖ ≤
      η k * ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ := by
  by_cases hkt : n * k.val ≤ t
  · have he : t = n * k.val + (t - n * k.val) := by omega
    rw [he]
    exact iterate_swap_norm h η x0 k i j hji hη hstep s _ (by omega)
  · rw [iterate_swap_before g η x0 k i j s t (by omega), sub_self, norm_zero]
    positivity

omit [NeZero n] [CompleteSpace E] in
lemma anchor_norm_le (w : ℕ → ℝ) (X Y : ℕ → E) (xstar : E) (t : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hw : ∀ k, k ≤ t → 0 < w k)
    (hmono : ∀ k, k < t → w k ≤ w (k + 1))
    (hXY : ∀ k, k ≤ t → ‖X k - Y k‖ ≤ D) :
    ‖anchor w X xstar t - anchor w Y xstar t‖ ≤ D := by
  induction t with
  | zero => simpa [anchor] using hD
  | succ t ih =>
    have hw0 := hw t (by omega)
    have hw1 := hw (t + 1) (by omega)
    have hθ0 : 0 ≤ w t / w (t + 1) := div_nonneg hw0.le hw1.le
    have hθ1 : w t / w (t + 1) ≤ 1 := (div_le_one hw1).2 (hmono t (by omega))
    have hprev := ih (fun k hk => hw k (by omega)) (fun k hk => hmono k (by omega))
      (fun k hk => hXY k (by omega))
    have hnext := hXY (t + 1) (by omega)
    have he : anchor w X xstar (t + 1) - anchor w Y xstar (t + 1) =
        (w t / w (t + 1)) • (anchor w X xstar t - anchor w Y xstar t) +
        (1 - w t / w (t + 1)) • (X (t + 1) - Y (t + 1)) := by
      simp only [anchor]
      module
    rw [he]
    calc
      _ ≤ ‖(w t / w (t + 1)) • (anchor w X xstar t - anchor w Y xstar t)‖ +
          ‖(1 - w t / w (t + 1)) • (X (t + 1) - Y (t + 1))‖ := norm_add_le _ _
      _ = (w t / w (t + 1)) * ‖anchor w X xstar t - anchor w Y xstar t‖ +
          (1 - w t / w (t + 1)) * ‖X (t + 1) - Y (t + 1)‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0,
          abs_of_nonneg (sub_nonneg.mpr hθ1)]
      _ ≤ (w t / w (t + 1)) * D + (1 - w t / w (t + 1)) * D :=
        add_le_add (mul_le_mul_of_nonneg_left hprev hθ0)
          (mul_le_mul_of_nonneg_left hnext (sub_nonneg.mpr hθ1))
      _ = D := by ring

lemma anchor_swap_norm {f : Fin n → E → ℝ} {g : Fin n → E → E}
    {ℓ : Fin n → ℝ} {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i j : Fin n) (hji : j.val < i.val)
    (hη : 0 < η k) (hstep : η k * Lmax ≤ 1) (s : Orders n K)
    (w : ℕ → ℝ) (hw : ∀ t, t ≤ n * k.val + i.val → 0 < w t)
    (hmono : ∀ t, t < n * k.val + i.val → w t ≤ w (t + 1)) :
    ‖anchor w (iterate g (schedule (swapOrder k i j s)) η x0) xstar (n * k.val + i.val) -
        anchor w (iterate g (schedule s) η x0) xstar (n * k.val + i.val)‖ ≤
      η k * ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ := by
  exact anchor_norm_le w _ _ xstar _ (by positivity) hw hmono
    (fun t ht => iterate_swap_norm_prefix h η x0 k i j hji hη hstep s t ht)

omit [NeZero n] [CompleteSpace E] in
lemma anchor_eq_of_prefix (w : ℕ → ℝ) (X Y : ℕ → E) (xstar : E) (t : ℕ)
    (hXY : ∀ k, k ≤ t → X k = Y k) : anchor w X xstar t = anchor w Y xstar t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [anchor]
    rw [ih (fun k hk => hXY k (by omega)), hXY (t + 1) (by omega)]

omit [CompleteSpace E] in
lemma anchor_swap_before (g : Fin n → E → E) (η : ℕ → ℝ) (x0 xstar : E)
    (k : Fin K) (i j : Fin n) (s : Orders n K) (w : ℕ → ℝ) (t : ℕ)
    (ht : t ≤ n * k.val + min i.val j.val) :
    anchor w (iterate g (schedule (swapOrder k i j s)) η x0) xstar t =
      anchor w (iterate g (schedule s) η x0) xstar t := by
  exact anchor_eq_of_prefix w _ _ xstar t
    (fun u hu => iterate_swap_before g η x0 k i j s u (hu.trans ht))

omit [CompleteSpace E] in
lemma gradient_swap_square_sum (g : Fin n → E → E) (η : ℕ → ℝ) (x0 : E)
    (k : Fin K) (i j : Fin n) (hji : j.val ≤ i.val) :
    (∑ s : Orders n K,
      ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2) ≤
      4 * ∑ s : Orders n K, ‖g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2 := by
  have hex := sum_label_eq_of_invariant k i j
    (fun s => iterate g (schedule s) η x0 (n * k.val + j.val))
    (fun a x => ‖g a x‖ ^ 2)
    (fun s => iterate_swap_before g η x0 k i j s _ (by omega))
  have hsum : (∑ s : Orders n K,
      ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2) ≤
      ∑ s : Orders n K,
        (2 * ‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2 +
        2 * ‖g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ ^ 2) := by
    apply sum_le_sum
    intro s _
    have hn := norm_sub_le (g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)))
      (g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val)))
    nlinarith [norm_nonneg (g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val))),
      norm_nonneg (g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))),
      norm_nonneg (g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val)) -
        g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))),
      sq_nonneg (‖g (s k i) (iterate g (schedule s) η x0 (n * k.val + j.val))‖ -
        ‖g (s k j) (iterate g (schedule s) η x0 (n * k.val + j.val))‖)]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hex] at hsum
  linarith

end OracleTemplate.ReshuffledExchange
