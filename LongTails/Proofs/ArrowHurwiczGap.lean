import LongTails.Proofs.ArrowHurwiczRun

open Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ArrowHurwicz

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

structure Hyp (X : Set E) (Y : Set F) (K : E →L[ℝ] F) (g : E → ℝ) (h : F → ℝ) (adj : F → E)
    (px : E × ℝ → E) (py : F × ℝ → F) (η R L M : ℝ) (x0 : E) (y0 : F) : Prop where
  convX : Convex ℝ X
  convY : Convex ℝ Y
  cvg : ConvexOn ℝ X g
  cvh : ConvexOn ℝ Y h
  lipg : ∀ a ∈ X, ∀ b ∈ X, |g a - g b| ≤ M * ‖a - b‖
  liph : ∀ a ∈ Y, ∀ b ∈ Y, |h a - h b| ≤ M * ‖a - b‖
  normK : ‖K‖ ≤ L
  hadj : ∀ y z, ⟪adj y, z⟫ = ⟪y, K z⟫
  proxX : ∀ u, IsProx X g η u (px (u, η))
  proxY : ∀ u, IsProx Y h η u (py (u, η))
  boundX : ∀ x ∈ X, ‖x‖ ≤ R
  boundY : ∀ y ∈ Y, ‖y‖ ≤ R
  hη : 0 < η
  hM : 0 ≤ M
  memx : x0 ∈ X
  memy : y0 ∈ Y

section Gap

variable {X : Set E} {Y : Set F} {K : E →L[ℝ] F} {g : E → ℝ} {h : F → ℝ} {adj : F → E}
  {px : E × ℝ → E} {py : F × ℝ → F} {η R L M : ℝ} {x0 : E} {y0 : F}

noncomputable def xs (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (t : ℕ) : E := (traj adj K px py η x0 y0 t).1

noncomputable def ys (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (t : ℕ) : F := (traj adj K px py η x0 y0 t).2

lemma Hyp.mem (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    xs adj K px py η x0 y0 t ∈ X ∧ ys adj K px py η x0 y0 t ∈ Y := by
  cases t with
  | zero => exact ⟨H.memx, H.memy⟩
  | succ t =>
    refine ⟨?_, ?_⟩
    · unfold xs; rw [traj_fst_succ]; exact (H.proxX _).1
    · unfold ys; rw [traj_snd_succ]; exact (H.proxY _).1

lemma Hyp.prox_x (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    IsProx X g η (xs adj K px py η x0 y0 t - η • adj (ys adj K px py η x0 y0 t))
      (xs adj K px py η x0 y0 (t + 1)) := by
  unfold xs ys; rw [traj_fst_succ]; exact H.proxX _

lemma Hyp.prox_y (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    IsProx Y h η (ys adj K px py η x0 y0 t + η • K (xs adj K px py η x0 y0 (t + 1)))
      (ys adj K px py η x0 y0 (t + 1)) := by
  unfold xs ys; rw [traj_snd_succ (t := t)]; exact H.proxY _

lemma Hyp.vix (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) {w : E} (hw : w ∈ X) :
    ⟪xs adj K px py η x0 y0 t - η • adj (ys adj K px py η x0 y0 t) - xs adj K px py η x0 y0 (t + 1),
      w - xs adj K px py η x0 y0 (t + 1)⟫ ≤ η * (g w - g (xs adj K px py η x0 y0 (t + 1))) :=
  prox_vi H.convX H.cvg (H.prox_x t) H.hη.le hw

lemma Hyp.viy (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) {w : F} (hw : w ∈ Y) :
    ⟪ys adj K px py η x0 y0 t + η • K (xs adj K px py η x0 y0 (t + 1)) - ys adj K px py η x0 y0 (t + 1),
      w - ys adj K px py η x0 y0 (t + 1)⟫ ≤ η * (h w - h (ys adj K px py η x0 y0 (t + 1))) :=
  prox_vi H.convY H.cvh (H.prox_y t) H.hη.le hw

lemma Hyp.L_nonneg (H : Hyp X Y K g h adj px py η R L M x0 y0) : 0 ≤ L :=
  le_trans (norm_nonneg _) H.normK

lemma Hyp.K_le (H : Hyp X Y K g h adj px py η R L M x0 y0) (x : E) : ‖K x‖ ≤ L * ‖x‖ :=
  le_trans (K.le_opNorm x) (by gcongr; exact H.normK)

lemma Hyp.dx_le (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    ‖xs adj K px py η x0 y0 (t + 1) - xs adj K px py η x0 y0 t‖ ≤ η * (L * R + M) := by
  have hb := prox_step_bound H.convX H.cvg (fun a ha b hb => le_trans (le_abs_self _) (H.lipg a ha b hb))
    H.hM H.hη.le (H.mem t).1 (H.prox_x t)
  have ha : ‖adj (ys adj K px py η x0 y0 t)‖ ≤ L * R :=
    le_trans (adj_norm_le K adj H.hadj H.normK _)
      (mul_le_mul_of_nonneg_left (H.boundY _ (H.mem t).2) H.L_nonneg)
  calc _ ≤ η * (‖adj (ys adj K px py η x0 y0 t)‖ + M) := hb
    _ ≤ η * (L * R + M) := by gcongr; exact H.hη.le

lemma Hyp.dy_le (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    ‖ys adj K px py η x0 y0 (t + 1) - ys adj K px py η x0 y0 t‖ ≤ η * (L * R + M) := by
  have hp := H.prox_y t
  rw [show ys adj K px py η x0 y0 t + η • K (xs adj K px py η x0 y0 (t + 1)) =
      ys adj K px py η x0 y0 t - η • (-K (xs adj K px py η x0 y0 (t + 1))) by
    rw [smul_neg, sub_neg_eq_add]] at hp
  have hb := prox_step_bound H.convY H.cvh (fun a ha b hb => le_trans (le_abs_self _) (H.liph a ha b hb))
    H.hM H.hη.le (H.mem t).2 hp
  have ha : ‖-K (xs adj K px py η x0 y0 (t + 1))‖ ≤ L * R := by
    rw [norm_neg]
    exact le_trans (H.K_le _) (mul_le_mul_of_nonneg_left (H.boundX _ (H.mem _).1) H.L_nonneg)
  calc _ ≤ η * (‖-K (xs adj K px py η x0 y0 (t + 1))‖ + M) := hb
    _ ≤ η * (L * R + M) := by gcongr; exact H.hη.le

noncomputable def fr (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (t : ℕ) : ℝ :=
  ⟪xs adj K px py η x0 y0 t - η • adj (ys adj K px py η x0 y0 t) - xs adj K px py η x0 y0 (t + 1),
      xs adj K px py η x0 y0 (t + 1) - xs adj K px py η x0 y0 t⟫ +
    ⟪ys adj K px py η x0 y0 t + η • K (xs adj K px py η x0 y0 (t + 1)) - ys adj K px py η x0 y0 (t + 1),
      ys adj K px py η x0 y0 (t + 1) - ys adj K px py η x0 y0 t⟫

noncomputable def vel (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (t : ℕ) : ℝ :=
  (‖xs adj K px py η x0 y0 (t + 1) - xs adj K px py η x0 y0 t‖ ^ 2 +
    ‖ys adj K px py η x0 y0 (t + 1) - ys adj K px py η x0 y0 t‖ ^ 2) / 2

noncomputable def pot (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (g : E → ℝ) (h : F → ℝ) (t : ℕ) : ℝ :=
  g (xs adj K px py η x0 y0 t) + h (ys adj K px py η x0 y0 t)

lemma Hyp.fr_succ_le (H : Hyp X Y K g h adj px py η R L M x0 y0) (t : ℕ) :
    fr adj K px py η x0 y0 (t + 1) ≤ vel adj K px py η x0 y0 t - vel adj K px py η x0 y0 (t + 1) +
      η ^ 2 / 2 * ‖K (xs adj K px py η x0 y0 (t + 2) - xs adj K px py η x0 y0 (t + 1))‖ ^ 2 +
      η * (pot adj K px py η x0 y0 g h (t + 2) - pot adj K px py η x0 y0 g h (t + 1)) := by
  have hb := friction_bound K adj H.hadj g h η (xs adj K px py η x0 y0 t)
    (xs adj K px py η x0 y0 (t + 1)) (xs adj K px py η x0 y0 (t + 2)) (ys adj K px py η x0 y0 t)
    (ys adj K px py η x0 y0 (t + 1)) (ys adj K px py η x0 y0 (t + 2))
    (H.vix t (H.mem (t + 2)).1) (H.viy t (H.mem (t + 2)).2)
  unfold fr vel pot
  linarith

lemma Hyp.fr_zero_le (H : Hyp X Y K g h adj px py η R L M x0 y0) :
    fr adj K px py η x0 y0 0 ≤ η ^ 2 * L ^ 2 * R ^ 2 / 2 := by
  have e1 : xs adj K px py η x0 y0 0 - η • adj (ys adj K px py η x0 y0 0) - xs adj K px py η x0 y0 1 =
      (-(η • adj (ys adj K px py η x0 y0 0))) - (xs adj K px py η x0 y0 1 - xs adj K px py η x0 y0 0) := by
    abel
  have e2 : ys adj K px py η x0 y0 0 + η • K (xs adj K px py η x0 y0 1) - ys adj K px py η x0 y0 1 =
      (η • K (xs adj K px py η x0 y0 1)) - (ys adj K px py η x0 y0 1 - ys adj K px py η x0 y0 0) := by
    abel
  have i1 := inner_sub_self_le (-(η • adj (ys adj K px py η x0 y0 0)))
    (xs adj K px py η x0 y0 1 - xs adj K px py η x0 y0 0)
  have i2 := inner_sub_self_le (η • K (xs adj K px py η x0 y0 1))
    (ys adj K px py η x0 y0 1 - ys adj K px py η x0 y0 0)
  have n1 : ‖-(η • adj (ys adj K px py η x0 y0 0))‖ ≤ η * (L * R) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos H.hη]
    exact mul_le_mul_of_nonneg_left (le_trans (adj_norm_le K adj H.hadj H.normK _)
      (mul_le_mul_of_nonneg_left (H.boundY _ (H.mem 0).2) H.L_nonneg)) H.hη.le
  have n2 : ‖η • K (xs adj K px py η x0 y0 1)‖ ≤ η * (L * R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos H.hη]
    exact mul_le_mul_of_nonneg_left (le_trans (H.K_le _)
      (mul_le_mul_of_nonneg_left (H.boundX _ (H.mem 1).1) H.L_nonneg)) H.hη.le
  have s1 : ‖-(η • adj (ys adj K px py η x0 y0 0))‖ ^ 2 ≤ (η * (L * R)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) n1 2
  have s2 : ‖η • K (xs adj K px py η x0 y0 1)‖ ^ 2 ≤ (η * (L * R)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) n2 2
  unfold fr
  rw [e1, e2]
  nlinarith

lemma Hyp.sum_fr_succ (H : Hyp X Y K g h adj px py η R L M x0 y0) (N : ℕ) :
    ∑ s ∈ Finset.range N, fr adj K px py η x0 y0 (s + 1) ≤
      vel adj K px py η x0 y0 0 - vel adj K px py η x0 y0 N +
      η ^ 2 / 2 * ∑ s ∈ Finset.range N,
        ‖K (xs adj K px py η x0 y0 (s + 2) - xs adj K px py η x0 y0 (s + 1))‖ ^ 2 +
      η * (pot adj K px py η x0 y0 g h (N + 1) - pot adj K px py η x0 y0 g h 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := H.fr_succ_le N
    linarith

variable (xh : E) (yh : F)

noncomputable def lyap (adj : F → E) (K : E →L[ℝ] F) (px : E × ℝ → E) (py : F × ℝ → F) (η : ℝ)
    (x0 : E) (y0 : F) (xh : E) (yh : F) (t : ℕ) : ℝ :=
  ‖xs adj K px py η x0 y0 t - xh‖ ^ 2 / 2 + ‖ys adj K px py η x0 y0 t - yh‖ ^ 2 / 2 -
    η / 2 * ⟪ys adj K px py η x0 y0 t, K (xs adj K px py η x0 y0 t)⟫ +
    η * ⟪ys adj K px py η x0 y0 t, K xh⟫

noncomputable def gapTerm (K : E →L[ℝ] F) (g : E → ℝ) (h : F → ℝ) (x : E) (y : F) (xh : E) (yh : F) : ℝ :=
  (g x + ⟪yh, K x⟫ - h yh) - (g xh + ⟪y, K xh⟫ - h y)

lemma Hyp.one_step_sum (H : Hyp X Y K g h adj px py η R L M x0 y0) {xh : E} {yh : F}
    (hxh : xh ∈ X) (hyh : yh ∈ Y) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        η * gapTerm K g h (xs adj K px py η x0 y0 (t + 1)) (ys adj K px py η x0 y0 (t + 1)) xh yh ≤
      lyap adj K px py η x0 y0 xh yh 0 - lyap adj K px py η x0 y0 xh yh T +
        (∑ t ∈ Finset.range T, fr adj K px py η x0 y0 t) / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hb := one_step_bound K adj H.hadj g h η (xs adj K px py η x0 y0 T)
      (xs adj K px py η x0 y0 (T + 1)) xh (ys adj K px py η x0 y0 T)
      (ys adj K px py η x0 y0 (T + 1)) yh (H.vix T hxh) (H.viy T hyh)
    unfold gapTerm lyap fr at *
    linarith

end Gap

end OracleTemplate.ArrowHurwicz
