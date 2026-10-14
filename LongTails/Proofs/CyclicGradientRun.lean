import LongTails.Proofs.CyclicGradientStep
import LongTails.Proofs.Execution

open Set InnerProductSpace Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.CyclicInterpolation

open LongTails.Setups.InterpolatedFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def iter (m : ℕ) [NeZero m] (g : Fin m × E → E) (L : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => iter m g L x0 t - (1 / L) • g (component m t, iter m g L x0 t)

lemma execute_cyclic (m : ℕ) [NeZero m] (g : Fin m × E → E) (L : ℝ) (x0 : E) (T : ℕ) :
    execute { answer := fun _ (_, query) _ => g query } (cyclicGradient m L x0) (fun _ => T) =
      iter m g L x0 T := by
  erw [execute_iterate g (cyclicGradient m L x0) T ()]
  have h : ∀ T : ℕ, (fun s => (cyclicGradient m L x0).update s
      (g (((cyclicGradient m L x0).query s).2)))^[T] ((cyclicGradient m L x0).initial ()) =
        ((iter m g L x0 T, T) : E × ℕ) := by
    intro T
    induction T with
    | zero => rfl
    | succ T ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl
  rw [h T]
  rfl

lemma component_add (m : ℕ) [NeZero m] (t : ℕ) : component m (t + m) = component m t :=
  Fin.ext (Nat.add_mod_right t m)

lemma component_cycle (m : ℕ) [NeZero m] (K : ℕ) (i : Fin m) :
    component m (K * m + i) = i := by
  apply Fin.ext
  show (K * m + i) % m = i
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.2]

lemma sum_range_cast (m : ℕ) : ∑ j ∈ range m, (j : ℝ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

variable [CompleteSpace E]

structure Hyp (m : ℕ) [NeZero m] (f : Fin m → E → ℝ) (g : Fin m × E → E) (L : ℝ)
    (xstar : E) : Prop where
  pos : 0 < L
  convex : ∀ i, ConvexOn ℝ univ (f i)
  grad : ∀ i x, HasGradientAt (f i) (g (i, x)) x
  lip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖
  min : ∀ i, IsMinOn (f i) univ xstar

lemma value_transfer {φ : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L) (hc : ConvexOn ℝ univ φ)
    (hg : ∀ x, HasGradientAt φ (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn φ univ xstar) (x y : E) :
    φ x - φ xstar ≤ 2 * (φ y - φ xstar) + 2 * L * ‖x - y‖ ^ 2 := by
  have h1 := Gradient.convex_support hc hg x y
  have h2 := grad_sq_le hL hc hg hlip hmin x
  have h3 : ⟪g x, y - x⟫ = -⟪g x, x - y⟫ := by
    rw [← neg_sub x y, inner_neg_right]
  have h4 : ⟪g x, x - y⟫ ≤ ‖g x‖ * ‖x - y‖ := real_inner_le_norm _ _
  have h5 : ‖g x‖ * ‖x - y‖ ≤ ‖g x‖ ^ 2 / (4 * L) + L * ‖x - y‖ ^ 2 := by
    have e : ‖g x‖ ^ 2 / (4 * L) + L * ‖x - y‖ ^ 2 - ‖g x‖ * ‖x - y‖ =
        (‖g x‖ - 2 * L * ‖x - y‖) ^ 2 / (4 * L) := by
      field_simp
      ring
    have hpos : 0 ≤ (‖g x‖ - 2 * L * ‖x - y‖) ^ 2 / (4 * L) := by positivity
    linarith
  have h6 : ‖g x‖ ^ 2 / (4 * L) ≤ (φ x - φ xstar) / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * L)]
    linarith
  linarith

section Run

variable {m : ℕ} [NeZero m] {f : Fin m → E → ℝ} {g : Fin m × E → E} {L : ℝ} {xstar : E}

noncomputable def gap (f : Fin m → E → ℝ) (g : Fin m × E → E) (L : ℝ) (x0 xstar : E) (t : ℕ) : ℝ :=
  f (component m t) (iter m g L x0 t) - f (component m t) xstar

noncomputable def online (f : Fin m → E → ℝ) (g : Fin m × E → E) (L : ℝ) (x0 xstar : E)
    (s : ℕ) : ℝ :=
  ∑ j ∈ range m, 2 / L * gap f g L x0 xstar (s + j)

noncomputable def energy (g : Fin m × E → E) (L : ℝ) (x0 : E) (s : ℕ) : ℝ :=
  ∑ j ∈ range m, ‖iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)‖ ^ 2

noncomputable def shift (g : Fin m × E → E) (L : ℝ) (x0 : E) (s : ℕ) : ℝ :=
  ‖iter m g L x0 s - iter m g L x0 (s + m)‖ ^ 2

noncomputable def variation (g : Fin m × E → E) (L : ℝ) (x0 : E) (s : ℕ) : ℝ :=
  ∑ j ∈ range m, ‖(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
    (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1))‖ ^ 2

noncomputable def cross (g : Fin m × E → E) (L : ℝ) (x0 : E) (s : ℕ) : ℝ :=
  2 * ∑ j ∈ range m, ⟪(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
    (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1)),
    iter m g L x0 (s + j + 1) - iter m g L x0 (s + m)⟫

namespace Hyp

variable (h : Hyp m f g L xstar) (x0 : E)
include h

omit [CompleteSpace E] h in
lemma step_eq (t : ℕ) :
    iter m g L x0 t - iter m g L x0 (t + 1) = (1 / L) • g (component m t, iter m g L x0 t) := by
  show iter m g L x0 t - (iter m g L x0 t - (1 / L) • g (component m t, iter m g L x0 t)) = _
  abel

omit [CompleteSpace E] h in
lemma step_eq' (t : ℕ) :
    iter m g L x0 (t + m) - iter m g L x0 (t + m + 1) =
      (1 / L) • g (component m t, iter m g L x0 (t + m)) := by
  show iter m g L x0 (t + m) - (iter m g L x0 (t + m) -
    (1 / L) • g (component m (t + m), iter m g L x0 (t + m))) = _
  rw [component_add]
  abel

lemma gap_nonneg (t : ℕ) : 0 ≤ gap f g L x0 xstar t :=
  sub_nonneg.mpr (h.min _ (mem_univ _))

lemma fejer (t : ℕ) :
    ‖iter m g L x0 (t + 1) - xstar‖ ^ 2 ≤
      ‖iter m g L x0 t - xstar‖ ^ 2 - 2 / L * gap f g L x0 xstar t :=
  step_fejer (φ := f (component m t)) (g := fun x => g (component m t, x)) h.pos (h.convex _)
    (fun x => h.grad _ x) (fun x y => h.lip _ x y) (h.min _) (iter m g L x0 t)

lemma step_sq (t : ℕ) :
    ‖iter m g L x0 t - iter m g L x0 (t + 1)‖ ^ 2 ≤ 2 / L * gap f g L x0 xstar t := by
  have hL := h.pos
  rw [step_eq x0 t, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / L)]
  have h1 : ‖g (component m t, iter m g L x0 t)‖ ^ 2 ≤ 2 * L * gap f g L x0 xstar t :=
    grad_sq_le (φ := f (component m t)) (g := fun x => g (component m t, x)) h.pos
      (h.convex (component m t)) (fun x => h.grad _ x) (fun x y => h.lip _ x y) (h.min _)
      (iter m g L x0 t)
  have h2 : (1 / L * ‖g (component m t, iter m g L x0 t)‖) ^ 2 =
      1 / L ^ 2 * ‖g (component m t, iter m g L x0 t)‖ ^ 2 := by
    field_simp
  have h3 : 2 / L * gap f g L x0 xstar t =
      1 / L ^ 2 * (2 * L * gap f g L x0 xstar t) := by
    field_simp
  rw [h2, h3]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma firm (t : ℕ) :
    ‖iter m g L x0 (t + 1) - iter m g L x0 (t + m + 1)‖ ^ 2 ≤
      ‖iter m g L x0 t - iter m g L x0 (t + m)‖ ^ 2 -
        ‖(iter m g L x0 t - iter m g L x0 (t + 1)) -
          (iter m g L x0 (t + m) - iter m g L x0 (t + m + 1))‖ ^ 2 := by
  rw [step_eq x0 t, step_eq' x0 t]
  have h1 := step_firm (φ := f (component m t)) (g := fun x => g (component m t, x)) h.pos
    (h.convex (component m t)) (fun x => h.grad _ x) (fun x y => h.lip _ x y)
    (iter m g L x0 t) (iter m g L x0 (t + m))
  have e1 : iter m g L x0 (t + 1) =
      iter m g L x0 t - (1 / L) • g (component m t, iter m g L x0 t) := rfl
  have e2 : iter m g L x0 (t + m + 1) =
      iter m g L x0 (t + m) - (1 / L) • g (component m t, iter m g L x0 (t + m)) := by
    show iter m g L x0 (t + m) - (1 / L) • g (component m (t + m), iter m g L x0 (t + m)) = _
    rw [component_add]
  rw [e1, e2]
  exact h1

lemma gamma (t : ℕ) :
    ⟪iter m g L x0 (t + m) - iter m g L x0 (t + m + 1),
        iter m g L x0 (t + 1) - iter m g L x0 (t + m + 1)⟫ ≤
      1 / L * (gap f g L x0 xstar t - gap f g L x0 xstar (t + m)) +
        (‖iter m g L x0 (t + m) - iter m g L x0 (t + m + 1)‖ ^ 2 -
          ‖iter m g L x0 t - iter m g L x0 (t + 1)‖ ^ 2) / 2 := by
  rw [step_eq x0 t, step_eq' x0 t]
  have h1 := step_gamma (φ := f (component m t)) (g := fun x => g (component m t, x)) h.pos
    (h.convex (component m t)) (fun x => h.grad _ x) (fun x y => h.lip _ x y)
    (iter m g L x0 t) (iter m g L x0 (t + m))
  have e1 : iter m g L x0 (t + 1) =
      iter m g L x0 t - (1 / L) • g (component m t, iter m g L x0 t) := rfl
  have e2 : iter m g L x0 (t + m + 1) =
      iter m g L x0 (t + m) - (1 / L) • g (component m t, iter m g L x0 (t + m)) := by
    show iter m g L x0 (t + m) - (1 / L) • g (component m (t + m), iter m g L x0 (t + m)) = _
    rw [component_add]
  have e3 : gap f g L x0 xstar t - gap f g L x0 xstar (t + m) =
      f (component m t) (iter m g L x0 t) - f (component m t) (iter m g L x0 (t + m)) := by
    unfold gap
    rw [component_add]
    ring
  rw [e1, e2, e3]
  exact h1

lemma online_nonneg (s : ℕ) : 0 ≤ online f g L x0 xstar s := by
  have hL := h.pos
  unfold online
  exact sum_nonneg (fun j _ => mul_nonneg (by positivity) (h.gap_nonneg x0 _))

lemma energy_le_online (s : ℕ) : energy g L x0 s ≤ online f g L x0 xstar s := by
  unfold energy online
  exact sum_le_sum (fun j _ => h.step_sq x0 (s + j))

omit [CompleteSpace E] h in
lemma energy_nonneg (s : ℕ) : 0 ≤ energy g L x0 s := by
  unfold energy
  exact sum_nonneg (fun j _ => by positivity)

omit [CompleteSpace E] h in
lemma shift_nonneg (s : ℕ) : 0 ≤ shift g L x0 s := by
  unfold shift
  positivity

lemma online_le_distance (s : ℕ) :
    online f g L x0 xstar s ≤
      ‖iter m g L x0 s - xstar‖ ^ 2 - ‖iter m g L x0 (s + m) - xstar‖ ^ 2 := by
  have h1 : online f g L x0 xstar s ≤ ∑ j ∈ range m,
      (‖iter m g L x0 (s + j) - xstar‖ ^ 2 - ‖iter m g L x0 (s + (j + 1)) - xstar‖ ^ 2) := by
    unfold online
    apply sum_le_sum
    intro j _
    have := h.fejer x0 (s + j)
    rw [← Nat.add_assoc]
    linarith
  rw [sum_range_sub' (fun j => ‖iter m g L x0 (s + j) - xstar‖ ^ 2)] at h1
  simpa using h1

lemma variation_le_shift (s : ℕ) :
    variation g L x0 s ≤ shift g L x0 s - shift g L x0 (s + m) := by
  have h1 : variation g L x0 s ≤ ∑ j ∈ range m,
      (‖iter m g L x0 (s + j) - iter m g L x0 (s + j + m)‖ ^ 2 -
        ‖iter m g L x0 (s + (j + 1)) - iter m g L x0 (s + (j + 1) + m)‖ ^ 2) := by
    unfold variation
    apply sum_le_sum
    intro j _
    have := h.firm x0 (s + j)
    have e : s + (j + 1) + m = s + j + m + 1 := by omega
    rw [e, ← Nat.add_assoc]
    linarith
  rw [sum_range_sub' (fun j => ‖iter m g L x0 (s + j) - iter m g L x0 (s + j + m)‖ ^ 2)] at h1
  unfold shift
  simpa using h1

lemma cycle (s : ℕ) :
    online f g L x0 xstar (s + m) ≤
      online f g L x0 xstar s - shift g L x0 s - shift g L x0 (s + m) + cross g L x0 s := by
  have hL := h.pos
  have hid := cycle_identity (fun j => iter m g L x0 (s + j))
    (fun j => iter m g L x0 (s + j + m)) m (by simp)
  have hgam : ∑ j ∈ range m, ⟪iter m g L x0 (s + j + m) - iter m g L x0 (s + (j + 1) + m),
      iter m g L x0 (s + (j + 1)) - iter m g L x0 (s + (j + 1) + m)⟫ ≤
      ∑ j ∈ range m, (1 / L * (gap f g L x0 xstar (s + j) - gap f g L x0 xstar (s + j + m)) +
        (‖iter m g L x0 (s + j + m) - iter m g L x0 (s + (j + 1) + m)‖ ^ 2 -
          ‖iter m g L x0 (s + j) - iter m g L x0 (s + (j + 1))‖ ^ 2) / 2) := by
    apply sum_le_sum
    intro j _
    have e : s + (j + 1) + m = s + j + m + 1 := by omega
    rw [e, ← Nat.add_assoc]
    exact h.gamma x0 (s + j)
  have hsplit : ∑ j ∈ range m, (1 / L * (gap f g L x0 xstar (s + j) -
        gap f g L x0 xstar (s + j + m)) +
        (‖iter m g L x0 (s + j + m) - iter m g L x0 (s + (j + 1) + m)‖ ^ 2 -
          ‖iter m g L x0 (s + j) - iter m g L x0 (s + (j + 1))‖ ^ 2) / 2) =
      (online f g L x0 xstar s - online f g L x0 xstar (s + m)) / 2 +
        (∑ j ∈ range m, ‖iter m g L x0 (s + j + m) - iter m g L x0 (s + (j + 1) + m)‖ ^ 2 -
          ∑ j ∈ range m, ‖iter m g L x0 (s + j) - iter m g L x0 (s + (j + 1))‖ ^ 2) / 2 := by
    have e : online f g L x0 xstar (s + m) =
        ∑ j ∈ range m, 2 / L * gap f g L x0 xstar (s + j + m) := by
      unfold online
      exact sum_congr rfl (fun j _ => by rw [Nat.add_right_comm])
    rw [e]
    unfold online
    rw [← sum_sub_distrib, ← sum_sub_distrib, sum_div, sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hcross : cross g L x0 s = 2 * ∑ j ∈ range m,
      ⟪(iter m g L x0 (s + j) - iter m g L x0 (s + (j + 1))) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + (j + 1) + m)),
        iter m g L x0 (s + (j + 1)) - iter m g L x0 (s + m)⟫ := by
    unfold cross
    congr 1
    apply sum_congr rfl
    intro j _
    have e : s + (j + 1) + m = s + j + m + 1 := by omega
    rw [e, ← Nat.add_assoc]
  have hshift1 : shift g L x0 s = ‖iter m g L x0 (s + 0) - iter m g L x0 (s + m)‖ ^ 2 := rfl
  have hshift2 : shift g L x0 (s + m) =
      ‖iter m g L x0 (s + 0 + m) - iter m g L x0 (s + m + m)‖ ^ 2 := rfl
  rw [hcross, hshift1, hshift2]
  try beta_reduce at hid
  linarith

omit [CompleteSpace E] h in
lemma cross_young (s : ℕ) {κ : ℝ} (_hκ : 0 ≤ κ) :
    κ * cross g L x0 s ≤
      κ ^ 2 * variation g L x0 s + (m : ℝ) * ((m : ℝ) - 1) * energy g L x0 s := by
  have hterm : ∀ j ∈ range m,
      κ * (2 * ⟪(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1)),
        iter m g L x0 (s + j + 1) - iter m g L x0 (s + m)⟫) ≤
      κ ^ 2 * ‖(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1))‖ ^ 2 +
        ((m : ℝ) - 1) * energy g L x0 s := by
    intro j hj
    have hjm : j + 1 ≤ m := Nat.succ_le_of_lt (mem_range.mp hj)
    have h1 : 0 ≤ ‖κ • ((iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1))) -
        (iter m g L x0 (s + j + 1) - iter m g L x0 (s + m))‖ ^ 2 := by positivity
    rw [norm_sub_sq_real, inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
    simp only [RCLike.conj_to_real] at h1
    have h2 : ‖iter m g L x0 (s + j + 1) - iter m g L x0 (s + m)‖ ^ 2 ≤
        ((m - (j + 1) : ℕ) : ℝ) * energy g L x0 s :=
      path_sq (fun l => iter m g L x0 (s + l)) hjm (le_refl m)
    have h3 : ((m - (j + 1) : ℕ) : ℝ) ≤ (m : ℝ) - 1 := by
      have h4 : m - (j + 1) ≤ m - 1 := by omega
      have h5 : ((m - (j + 1) : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr h4
      rwa [Nat.cast_pred (NeZero.pos m)] at h5
    have h6 := mul_le_mul_of_nonneg_right h3 (energy_nonneg x0 s (g := g) (L := L))
    linarith
  have e1 : κ * cross g L x0 s = ∑ j ∈ range m,
      κ * (2 * ⟪(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1)),
        iter m g L x0 (s + j + 1) - iter m g L x0 (s + m)⟫) := by
    unfold cross
    rw [mul_sum, mul_sum]
  have e2 : κ ^ 2 * variation g L x0 s + (m : ℝ) * ((m : ℝ) - 1) * energy g L x0 s =
      ∑ j ∈ range m, (κ ^ 2 * ‖(iter m g L x0 (s + j) - iter m g L x0 (s + j + 1)) -
        (iter m g L x0 (s + j + m) - iter m g L x0 (s + j + m + 1))‖ ^ 2 +
        ((m : ℝ) - 1) * energy g L x0 s) := by
    unfold variation
    rw [sum_add_distrib, mul_sum, sum_const, card_range, nsmul_eq_mul]
    ring
  rw [e1, e2]
  exact sum_le_sum hterm

lemma potential (K : ℕ) :
    (K : ℝ) * online f g L x0 xstar (K * m) +
        (K : ℝ) * ((K : ℝ) - 1) * shift g L x0 (K * m) +
        ‖iter m g L x0 ((K + 1) * m) - xstar‖ ^ 2 +
        (m : ℝ) * ((m : ℝ) - 1) * ‖iter m g L x0 (K * m) - xstar‖ ^ 2 ≤
      ‖iter m g L x0 m - xstar‖ ^ 2 + (m : ℝ) * ((m : ℝ) - 1) * ‖x0 - xstar‖ ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hB : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
  induction K with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, zero_add, one_mul]
    exact le_of_eq rfl
  | succ K ih =>
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have e1 : (K + 1) * m = K * m + m := Nat.succ_mul K m
    have e2 : (K + 1 + 1) * m = K * m + m + m := by rw [Nat.succ_mul, e1]
    rw [e2]
    rw [e1] at ih ⊢
    have h1 := h.cycle x0 (K * m)
    have h2 := cross_young (g := g) (L := L) x0 (K * m) hK
    have h3 := h.variation_le_shift x0 (K * m)
    have h4 := h.energy_le_online x0 (K * m)
    have h5 := h.online_le_distance x0 (K * m)
    have h6 := h.online_le_distance x0 (K * m + m)
    have h7 := mul_le_mul_of_nonneg_left h1 hK
    have h8 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (K : ℝ))
    have h9 := mul_le_mul_of_nonneg_left h4 hB
    have h10 := mul_le_mul_of_nonneg_left h5 hB
    push_cast
    linarith

theorem online_bound (K : ℕ) (hK : 1 ≤ K) :
    (K : ℝ) * online f g L x0 xstar (K * m) ≤
      (1 + (m : ℝ) * ((m : ℝ) - 1)) * ‖x0 - xstar‖ ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hB : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
  have h1 := h.potential x0 K
  have h2 := h.online_le_distance x0 0
  have h3 := h.online_nonneg x0 0
  have h4 : 0 ≤ (K : ℝ) * ((K : ℝ) - 1) * shift g L x0 (K * m) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (shift_nonneg x0 _)
  have h5 : 0 ≤ ‖iter m g L x0 ((K + 1) * m) - xstar‖ ^ 2 := by positivity
  have h6 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) * ‖iter m g L x0 (K * m) - xstar‖ ^ 2 :=
    mul_nonneg hB (by positivity)
  have h7 : ‖iter m g L x0 m - xstar‖ ^ 2 ≤ ‖x0 - xstar‖ ^ 2 := by
    have e : iter m g L x0 0 = x0 := rfl
    rw [zero_add, e] at h2
    linarith
  linarith

lemma average_le_online (K : ℕ) :
    ∑ i, (f i (iter m g L x0 (K * m)) - f i xstar) ≤
      L * (1 + (m : ℝ) * ((m : ℝ) - 1)) * online f g L x0 xstar (K * m) := by
  have hL := h.pos
  let H : ℕ → ℝ := fun j => f (component m (K * m + j)) (iter m g L x0 (K * m)) -
    f (component m (K * m + j)) xstar
  have e1 : ∑ i, (f i (iter m g L x0 (K * m)) - f i xstar) = ∑ i : Fin m, H i :=
    Fintype.sum_congr _ _ (fun i => by simp only [H]; rw [component_cycle])
  rw [e1, Fin.sum_univ_eq_sum_range H m]
  have hterm : ∀ j ∈ range m, H j ≤ 2 * gap f g L x0 xstar (K * m + j) +
      2 * L * ((j : ℝ) * energy g L x0 (K * m)) := by
    intro j hj
    have h1 := value_transfer (φ := f (component m (K * m + j)))
      (g := fun x => g (component m (K * m + j), x)) h.pos (h.convex (component m (K * m + j)))
      (fun x => h.grad _ x) (fun x y => h.lip _ x y) (h.min _) (iter m g L x0 (K * m))
      (iter m g L x0 (K * m + j))
    have h3 : ‖iter m g L x0 (K * m) - iter m g L x0 (K * m + j)‖ ^ 2 ≤
        (j : ℝ) * energy g L x0 (K * m) :=
      path_sq (fun l => iter m g L x0 (K * m + l)) (Nat.zero_le j) (le_of_lt (mem_range.mp hj))
    have h4 : 2 * L * ‖iter m g L x0 (K * m) - iter m g L x0 (K * m + j)‖ ^ 2 ≤
        2 * L * ((j : ℝ) * energy g L x0 (K * m)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    show f (component m (K * m + j)) (iter m g L x0 (K * m)) -
      f (component m (K * m + j)) xstar ≤ _
    unfold gap
    linarith
  have hsum := sum_le_sum hterm
  have a1 : ∑ j ∈ range m, 2 * gap f g L x0 xstar (K * m + j) =
      L * online f g L x0 xstar (K * m) := by
    unfold online
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    field_simp
  have a2 : ∑ j ∈ range m, 2 * L * ((j : ℝ) * energy g L x0 (K * m)) =
      L * ((m : ℝ) * ((m : ℝ) - 1)) * energy g L x0 (K * m) := by
    rw [← mul_sum, ← sum_mul, sum_range_cast]
    ring
  have e2 : ∑ j ∈ range m, (2 * gap f g L x0 xstar (K * m + j) +
      2 * L * ((j : ℝ) * energy g L x0 (K * m))) =
      L * online f g L x0 xstar (K * m) +
        L * ((m : ℝ) * ((m : ℝ) - 1)) * energy g L x0 (K * m) := by
    rw [sum_add_distrib, a1, a2]
  have h5 := h.energy_le_online x0 (K * m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have h6 : L * ((m : ℝ) * ((m : ℝ) - 1)) * energy g L x0 (K * m) ≤
      L * ((m : ℝ) * ((m : ℝ) - 1)) * online f g L x0 xstar (K * m) :=
    mul_le_mul_of_nonneg_left h5 (mul_nonneg hL.le (by nlinarith))
  rw [e2] at hsum
  linarith

theorem accuracy {R ε : ℝ} (hdist : ‖x0 - xstar‖ ≤ R) (hε : 0 < ε) (K : ℕ)
    (hK : (m : ℝ) ^ 3 * L * R ^ 2 / ε ≤ K) :
    (m : ℝ)⁻¹ * ∑ i, (f i (iter m g L x0 (m * K)) - f i xstar) ≤ ε := by
  have hL := h.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hR : 0 ≤ R := (norm_nonneg _).trans hdist
  have hR2 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  rw [inv_mul_le_iff₀ hm0]
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have h0 : (m : ℝ) ^ 3 * L * R ^ 2 ≤ 0 := by
      have h00 := (div_le_iff₀ hε).mp hK
      rw [Nat.cast_zero, zero_mul] at h00
      exact h00
    have hR0 : R ^ 2 ≤ 0 := by
      by_contra hc
      have : 0 < (m : ℝ) ^ 3 * L * R ^ 2 :=
        mul_pos (mul_pos (pow_pos hm0 3) hL) (lt_of_not_ge hc)
      linarith
    have hx : ‖x0 - xstar‖ = 0 := by nlinarith [norm_nonneg (x0 - xstar)]
    have hx' : x0 = xstar := sub_eq_zero.mp (norm_eq_zero.mp hx)
    have e : iter m g L x0 (m * 0) = xstar := by
      rw [Nat.mul_zero]
      exact hx'
    rw [e]
    simp only [sub_self, sum_const_zero]
    exact (mul_pos hm0 hε).le
  · have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hKr : (0 : ℝ) < K := by linarith
    have h1 := h.online_bound x0 K hKpos
    have h2 := h.average_le_online x0 K
    have h3 := h.online_nonneg x0 (K * m)
    rw [Nat.mul_comm m K]
    set B := 1 + (m : ℝ) * ((m : ℝ) - 1) with hBdef
    have hB1 : 1 ≤ B := by nlinarith
    have hB2 : B ≤ (m : ℝ) ^ 2 := by nlinarith
    have hB0 : 0 ≤ B := le_trans zero_le_one hB1
    have h4 : online f g L x0 xstar (K * m) ≤ B * R ^ 2 / K := by
      rw [le_div_iff₀ hKr]
      have := mul_le_mul_of_nonneg_left hR2 hB0
      linarith
    have h5 : L * B * online f g L x0 xstar (K * m) ≤ L * B * (B * R ^ 2 / K) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hL.le hB0)
    have h6 : L * B * (B * R ^ 2 / K) ≤ ε * m := by
      have h7 : (m : ℝ) ^ 3 * L * R ^ 2 ≤ K * ε := (div_le_iff₀ hε).mp hK
      have h8 : L * B * (B * R ^ 2 / K) = L * R ^ 2 * B ^ 2 / K := by ring
      rw [h8, div_le_iff₀ hKr]
      have h9 : B ^ 2 ≤ (m : ℝ) ^ 4 := by
        have h11 := pow_le_pow_left₀ hB0 hB2 2
        calc B ^ 2 ≤ ((m : ℝ) ^ 2) ^ 2 := h11
          _ = (m : ℝ) ^ 4 := by ring
      have h10 : L * R ^ 2 * B ^ 2 ≤ L * R ^ 2 * (m : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left h9 (mul_nonneg hL.le (sq_nonneg R))
      have h12 := mul_le_mul_of_nonneg_left h7 hm0.le
      linarith
    linarith

end Hyp

end Run

end OracleTemplate.CyclicInterpolation
