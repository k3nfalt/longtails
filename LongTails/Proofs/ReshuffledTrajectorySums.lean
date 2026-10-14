import LongTails.Proofs.ReshuffledAnchorMoments
import LongTails.Proofs.ReshuffledLastIterateStep

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledTrajectory

open ReshuffledConvex ReshuffledExchange
open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n K : ℕ} [NeZero n]

noncomputable def label (s : Orders n K) (t : ℕ) : Fin n :=
  schedule s (t / n) ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩

noncomputable def path (g : Fin n → E → E) (η : ℝ) (x0 : E) (s : Orders n K) : ℕ → E :=
  iterate g (schedule s) (fun _ => η) x0

noncomputable def risk (f : Fin n → E → ℝ) (X : Orders n K → ℕ → E) (xstar : E) (t : ℕ) : ℝ :=
  ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s t) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)

noncomputable def centered (f : Fin n → E → ℝ) (g : Fin n → E → E)
    (X : Orders n K → ℕ → E) (xstar : E) (t : ℕ) : ℝ :=
  ∑ s, ReshuffledCentered.loss (f (label s t)) (g (label s t)) xstar (X s t)

noncomputable def moment (g : Fin n → E → E) (X : Orders n K → ℕ → E) (t : ℕ) : ℝ :=
  ∑ s, ‖g (label s t) (X s t)‖ ^ 2

lemma label_at (s : Orders n K) (k : Fin K) (i : Fin n) : label s (n * k.val + i.val) = s k i :=
  ReshuffledBias.label_inner s k i

lemma index_split {t : ℕ} (ht : t < n * K) :
    ∃ (k : Fin K) (i : Fin n), t = n * k.val + i.val := by
  have hk : t / n < K := (Nat.div_lt_iff_lt_mul (NeZero.pos n)).mpr (by nlinarith)
  refine ⟨⟨t / n, hk⟩, ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩, ?_⟩
  dsimp only
  exact (Nat.div_add_mod t n).symm

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma moment_nonneg (g : Fin n → E → E) (X : Orders n K → ℕ → E) (t : ℕ) :
    0 ≤ moment g X t := sum_nonneg fun _ _ => sq_nonneg _

omit [NeZero n] in
lemma risk_nonneg {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X : Orders n K → ℕ → E) (t : ℕ) : 0 ≤ risk f X xstar t :=
  sum_nonneg fun _ _ => h.gap_nonneg _

lemma centered_nonneg {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X : Orders n K → ℕ → E) (t : ℕ) : 0 ≤ centered f g X xstar t :=
  sum_nonneg fun _ _ => ReshuffledCentered.loss_nonneg (h.convex _) (h.grad _) _ _

lemma moment_bound {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X : Orders n K → ℕ → E) {t : ℕ} (ht : t < n * K) :
    moment g X t ≤ 4 * Lmax * centered f g X xstar t +
      2 * Fintype.card (Orders n K) * σ ^ 2 := by
  obtain ⟨k, i, rfl⟩ := index_split ht
  simp only [moment, centered, label_at]
  exact ReshuffledBias.sampled_grad_sq_sum h k i (fun s => X s (n * k.val + i.val))

lemma fin_prefix (M : ℕ → ℝ) (k : Fin K) (i : Fin n) :
    (∑ j : Fin n, if j.val < i.val then M (n * k.val + j.val) else 0) =
      ReshuffledWeighted.history n M (n * k.val + i.val) := by
  rw [ReshuffledWeighted.history_inner (NeZero.pos n) M k.val i.val i.isLt]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < i.val then M (n * k.val + j) else 0) n]
  rw [← sum_range_add_sum_Ico _ (Nat.le_of_lt i.isLt)]
  have hfirst : (∑ j ∈ range i.val, if j < i.val then M (n * k.val + j) else 0) =
      ∑ j ∈ range i.val, M (n * k.val + j) := by
    apply sum_congr rfl
    intro j hj
    simp [mem_range.mp hj]
  have hsecond : (∑ j ∈ Ico i.val n, if j < i.val then M (n * k.val + j) else 0) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [show ¬j < i.val by have := (mem_Ico.mp hj).1; omega]
  rw [hfirst, hsecond, add_zero]

lemma reverse_bias {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (hη : 0 < η) (hstep : η * Lmax ≤ 1) {t : ℕ} (ht : t < n * K) :
    n * (centered f g (path g η x0 : Orders n K → ℕ → E) xstar t -
      risk f (path g η x0 : Orders n K → ℕ → E) xstar t) ≤
      2 * n * η * Lmax * centered f g (path g η x0 : Orders n K → ℕ → E) xstar t +
        η * ReshuffledWeighted.history n (moment g (path g η x0 : Orders n K → ℕ → E)) t := by
  obtain ⟨k, i, rfl⟩ := index_split ht
  have hb := ReshuffledBias.centered_reverse_bias h (fun _ => η) x0 k i hη hstep
  change n * (_ - _) ≤ 2 * n * η * Lmax * _ + η * _ at hb
  simp only [centered, risk, label_at, path]
  rw [← fin_prefix]
  simpa only [moment, label_at, path] using hb

noncomputable def anchors (w : ℕ → ℝ) (X : Orders n K → ℕ → E) (xstar : E)
    (s : Orders n K) (t : ℕ) : E := anchor w (X s) xstar t

noncomputable def bregman (f : Fin n → E → ℝ) (g : Fin n → E → E)
    (X Z : Orders n K → ℕ → E) (t : ℕ) : ℝ :=
  ∑ s, ReshuffledCentered.loss (f (label s t)) (g (label s t)) (X s t) (Z s t)

lemma bregman_nonneg {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X Z : Orders n K → ℕ → E) (t : ℕ) : 0 ≤ bregman f g X Z t :=
  sum_nonneg fun _ _ => ReshuffledCentered.loss_nonneg (h.convex _) (h.grad _) _ _

lemma bregman_transfer {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X Z : Orders n K → ℕ → E) (t : ℕ) :
    moment g X t ≤ 4 * Lmax * bregman f g X Z t + 2 * moment g Z t := by
  have hs := sum_le_sum (s := univ) (fun s _ => ReshuffledLastStep.gradient_transfer
    h.lmax_pos (h.convex (label s t)) (h.grad (label s t)) (h.lip_max (label s t)) (X s t) (Z s t))
  simpa only [moment, bregman, sum_add_distrib, ← mul_sum] using hs

lemma anchor_moment {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (w : ℕ → ℝ) {t : ℕ} (ht : t < n * K)
    (hw : ∀ u, u ≤ t → 0 < w u) (hmono : ∀ u, u < t → w u ≤ w (u + 1)) :
    let X := (path g η x0 : Orders n K → ℕ → E)
    w t * moment g (anchors w X xstar) t ≤
      4 * Lmax * (∑ u ∈ range t, (w (u + 1) - w u) *
        (centered f g X xstar (u + 1) + risk f X xstar (u + 1))) +
      2 * Fintype.card (Orders n K) * σ ^ 2 * w t := by
  dsimp only
  have hm := mul_le_mul_of_nonneg_left
    (moment_bound h (anchors w (path g η x0) xstar) ht) (hw t le_rfl).le
  obtain ⟨k, i, rfl⟩ := index_split ht
  have ha := ReshuffledAnchorMoments.sampled_anchor_loss h (fun _ => η) x0 k i w hw hmono
  have hal := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * Lmax by have := h.lmax_pos; positivity)
  change _ ≤ _ at hal
  simp only [moment, centered, risk, anchors, path, label_at] at hm ⊢
  dsimp only at hal
  unfold label
  nlinarith

noncomputable def distance (X Z : Orders n K → ℕ → E) (t : ℕ) : ℝ :=
  ∑ s, ‖X s t - Z s t‖ ^ 2

noncomputable def nextDistance (X Z : Orders n K → ℕ → E) (t : ℕ) : ℝ :=
  ∑ s, ‖X s (t + 1) - Z s t‖ ^ 2

lemma step {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (hη : 0 < η) (hstep : η * Lmax ≤ 1 / 6)
    (w : ℕ → ℝ) {t : ℕ} (ht : t < n * K)
    (hw : ∀ u, u ≤ t → 0 < w u) (hmono : ∀ u, u < t → w u ≤ w (u + 1)) :
    let X := (path g η x0 : Orders n K → ℕ → E)
    let Z := anchors w X xstar
    2 * η * (risk f X xstar (t + 1) - risk f Z xstar t) ≤
      distance X Z t - nextDistance X Z t + (4 + η * Lmax) * η ^ 2 * moment g X t +
      2 * η ^ 2 * moment g Z t +
      (14 / (3 * (n : ℝ))) * η ^ 2 * ReshuffledWeighted.history n (moment g X) t +
      2 * η ^ 2 * Lmax * risk f X xstar t - 2 * η * bregman f g X Z t := by
  dsimp only
  obtain ⟨k, i, rfl⟩ := index_split ht
  rw [← fin_prefix]
  have hs := ReshuffledLastStep.one_step h (fun _ => η) x0 k i hη hstep w hw hmono
  simpa only [path, risk, moment, bregman, anchors, distance, nextDistance, label_at] using hs

lemma initial_risk {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) {D : ℝ} (hx0 : ‖x0 - xstar‖ ≤ D) :
    risk f (path g η x0 : Orders n K → ℕ → E) xstar 0 ≤
      Lmax * (Fintype.card (Orders n K) * D ^ 2) / 2 := by
  have hg := h.init_gap x0
  have hd : ‖x0 - xstar‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0 2
  have hc := mul_le_mul h.le hd (sq_nonneg _) h.lmax_pos.le
  have hf : LongTails.Setups.FiniteSumSmoothAndConvex.objective f x0 - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ Lmax * D ^ 2 / 2 := by
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hf
    (Nat.cast_nonneg (Fintype.card (Orders n K)) : (0 : ℝ) ≤ _)
  simpa only [risk, path, iterate, sum_const, card_univ, nsmul_eq_mul, mul_div_assoc,
    mul_left_comm (Fintype.card (Orders n K) : ℝ) Lmax] using hs

end OracleTemplate.ReshuffledTrajectory
