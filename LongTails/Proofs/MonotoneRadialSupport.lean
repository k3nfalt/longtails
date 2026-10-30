import LongTails.Proofs.AnchoredExtragradientStep

open scoped RealInnerProductSpace

namespace OracleTemplate.MonotoneRadialSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affine_growth {a : ℕ → ℝ} {b c : ℝ} {n : ℕ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : a 0 = 0)
    (hs : ∀ k < n, a (k + 1) ≤ (1 + c) * a k + b) :
    a n ≤ b * n * Real.exp (n * c) := by
  have hi : ∀ k ≤ n, a k ≤ b * k * (1 + c) ^ k := by
    intro k hk
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have hk' : k ≤ n := by omega
      have hr := hs k (by omega)
      have hm := mul_le_mul_of_nonneg_left (ih hk') (show 0 ≤ 1 + c by linarith)
      have hp : (1 : ℝ) ≤ (1 + c) ^ (k + 1) := one_le_pow₀ (by linarith)
      have hb' := mul_le_mul_of_nonneg_left hp hb
      push_cast
      rw [pow_succ] at hb' ⊢
      nlinarith
  have hp : (1 + c) ^ n ≤ Real.exp (n * c) := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1 + c by linarith) (show 1 + c ≤ Real.exp c by simpa [add_comm] using Real.add_one_le_exp c) n
    rw [← Real.exp_nat_mul] at h
    simpa [add_comm] using h
  exact (hi n le_rfl).trans (mul_le_mul_of_nonneg_left hp (by positivity))

lemma root_growth {F : E → E} {L0 L1 : ℝ}
    (h : GeneralizedMonotone.Hyp F L0 L1) {u : E} (hu : F u = 0) (x : E) :
    ‖F x‖ ≤ 2 * L0 * ‖x - u‖ * Real.exp (2 * L1 * ‖x - u‖) := by
  let n : ℕ := ⌈2 * L1 * ‖x - u‖⌉₊ + 1
  have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn
  have hnlarge : 2 * L1 * ‖x - u‖ ≤ (n : ℝ) := by
    have hh := Nat.le_ceil (2 * L1 * ‖x - u‖)
    dsimp [n]
    push_cast
    linarith
  let d := (1 / (n : ℝ)) • (x - u)
  let z := fun k : ℕ => u + (k : ℝ) • d
  have hd : ‖d‖ = ‖x - u‖ / n := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  have hdn : ‖d‖ * (n : ℝ) = ‖x - u‖ := by
    rw [hd]
    exact div_mul_cancel₀ _ hn0
  have hlocal : L1 * ‖d‖ ≤ 1 / 2 := by
    rw [hd, ← mul_div_assoc]
    exact (div_le_iff₀ hn).mpr (by linarith)
  have hz0 : z 0 = u := by simp [z]
  have hzn : z n = x := by
    dsimp [z, d]
    rw [smul_smul, mul_one_div_cancel hn0, one_smul]
    abel
  have hzd (k : ℕ) : ‖z k - z (k + 1)‖ = ‖d‖ := by
    have he : z k - z (k + 1) = -d := by dsimp [z]; push_cast; module
    rw [he, norm_neg]
  have hs : ∀ k < n, ‖F (z (k + 1))‖ ≤
      (1 + 2 * L1 * ‖d‖) * ‖F (z k)‖ + 2 * L0 * ‖d‖ := by
    intro k _
    have hl := h.local (z k) (z (k + 1)) (by rw [hzd]; linarith)
    rw [hzd] at hl
    have ht := norm_le_insert (F (z k)) (F (z (k + 1)))
    have hm := mul_le_mul_of_nonneg_right hlocal (norm_nonneg (F (z k) - F (z (k + 1))))
    nlinarith
  have hh := affine_growth (a := fun k => ‖F (z k)‖)
    (b := 2 * L0 * ‖d‖) (c := 2 * L1 * ‖d‖)
    (by positivity [h.L0_pos]) (by positivity [h.L1_nonneg])
    (by rw [hz0, hu, norm_zero]) hs
  rw [hzn] at hh
  have he : (n : ℝ) * (2 * L1 * ‖d‖) = 2 * L1 * ‖x - u‖ := by
    calc
      _ = 2 * L1 * (‖d‖ * (n : ℝ)) := by ring
      _ = _ := by rw [hdn]
  have hb : 2 * L0 * ‖d‖ * (n : ℝ) = 2 * L0 * ‖x - u‖ := by
    rw [mul_assoc (2 * L0), hdn]
  simpa only [he, hb] using hh

lemma offset_support {F : E → E} {x u : E} {R t : ℝ}
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    (hd : ‖x - u‖ ≤ R) (ht : 0 ≤ t) (hg : 0 < ‖F x‖)
    (hb : ‖F (u + (t / ‖F x‖) • F x)‖ * (R + t) ≤ t * ‖F x‖ / 2) :
    t * ‖F x‖ / 2 ≤ ⟪F x, x - u⟫ := by
  let v := u + (t / ‖F x‖) • F x
  have hn : ‖(t / ‖F x‖) • F x‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht hg.le)]
    exact div_mul_cancel₀ t (ne_of_gt hg)
  have hv : ‖x - v‖ ≤ R + t := by
    calc
      ‖x - v‖ = ‖(x - u) - (t / ‖F x‖) • F x‖ := by congr 1; dsimp [v]; abel
      _ ≤ ‖x - u‖ + ‖(t / ‖F x‖) • F x‖ := norm_sub_le _ _
      _ ≤ R + t := by rw [hn]; linarith
  have hm := hmono x v
  have hi : ⟪F x, x - v⟫ = ⟪F x, x - u⟫ - t * ‖F x‖ := by
    have he : x - v = (x - u) - (t / ‖F x‖) • F x := by dsimp [v]; abel
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hc := real_inner_le_norm (-(F v)) (x - v)
  rw [inner_neg_left, norm_neg] at hc
  have hh := mul_le_mul_of_nonneg_left hv (norm_nonneg (F v))
  rw [inner_sub_left, hi] at hm
  change ‖F v‖ * (R + t) ≤ t * ‖F x‖ / 2 at hb
  linarith

lemma large_residual_alignment {F : E → E} {L0 L1 : ℝ}
    (h : GeneralizedMonotone.Hyp F L0 L1) {u x : E} (hu : F u = 0)
    {R t : ℝ} (hR : 0 < R) (hd : ‖x - u‖ ≤ R) (ht : 0 ≤ t) (htR : t ≤ R)
    (hbig : 8 * L0 * R * Real.exp (2 * L1 * t) ≤ ‖F x‖) :
    t * ‖F x‖ / 2 ≤ ⟪F x, x - u⟫ := by
  have hL0 := h.L0_pos
  have hg : 0 < ‖F x‖ := lt_of_lt_of_le (by positivity) hbig
  apply offset_support h.mono hd ht hg
  have hv : ‖u + (t / ‖F x‖) • F x - u‖ = t := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ht hg.le)]
    exact div_mul_cancel₀ _ (ne_of_gt hg)
  have hb := root_growth h hu (u + (t / ‖F x‖) • F x)
  rw [hv] at hb
  calc
    _ ≤ (2 * L0 * t * Real.exp (2 * L1 * t)) * (2 * R) :=
      mul_le_mul hb (by linarith) (by positivity) (by positivity)
    _ ≤ t * ‖F x‖ / 2 := by
      have hm := mul_le_mul_of_nonneg_left hbig ht
      nlinarith

lemma normalized_step_drop {x u g : E} {t : ℝ}
    (hg : 0 < ‖g‖) (ht : 0 ≤ t) (hi : t * ‖g‖ / 2 ≤ ⟪g, x - u⟫) :
    ‖x - (t / (2 * ‖g‖)) • g - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 - t ^ 2 / 4 := by
  have he : x - (t / (2 * ‖g‖)) • g - u = (x - u) - (t / (2 * ‖g‖)) • g := by abel
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ht (by positivity)), real_inner_smul_right,
    real_inner_comm g (x - u)]
  have hp := mul_le_mul_of_nonneg_left hi (show 0 ≤ t / ‖g‖ by positivity)
  field_simp at hp ⊢
  nlinarith [sq_nonneg t]

end OracleTemplate.MonotoneRadialSupport
