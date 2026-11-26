import LongTails.Proofs.EscapeChainOracle

open MeasureTheory

namespace LongTails.Proofs.EscapeChainSimulator

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets EscapeChainSmooth
open EscapeChainCertificate EscapeChainRegularity EscapeChainCoin EscapeChainOracle
open RelativeHessianArctan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

noncomputable def objJ (K j : ℕ) (u v : ℕ → E) (y : E) : ℝ :=
  RelativeHessianCutoffSpatial.value (radius K) y * hidden j u v y +
    (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y

noncomputable def answerS (K j : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) (U : ℝ) : E :=
  gradient (objJ K j u v) y +
    ∑ l ∈ Finset.range j, (icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y

def reveals (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) (U : ℝ) : Prop :=
  start K A u v l y ≤ U ∧ U < start K A u v l y + prob K A u v l y

omit [FiniteDimensional ℝ E] in
lemma answerS_full (K : ℕ) (A : ℝ) (u v : ℕ → E) : answerS K K A u v = answerN K A u v := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma objJ_smooth (K j : ℕ) (u v : ℕ → E) : ContDiff ℝ 3 (objJ K j u v) :=
  ((RelativeHessianCutoffSpatial.smooth _).mul (hidden_smooth j u v)).add
    (contDiff_const.mul (RelativeHessianGuard.quadratic_smooth 2))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma cutLink_smooth (K : ℕ) (u v : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun y => RelativeHessianCutoffSpatial.value (radius K) y * link u v l y) :=
  (RelativeHessianCutoffSpatial.smooth _).mul (link_smooth u v l)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma objJ_succ (K j : ℕ) (u v : ℕ → E) :
    objJ K (j + 1) u v = fun y => objJ K j u v y +
      (RelativeHessianCutoffSpatial.value (radius K) y * link u v j y + smask K u v j y) := by
  funext y
  unfold objJ smask EscapeChainFunction.hidden
  rw [Finset.sum_range_succ]
  ring

lemma gradient_objJ_succ (K j : ℕ) (u v : ℕ → E) (y : E) :
    gradient (objJ K (j + 1) u v) y = gradient (objJ K j u v) y +
      (gradient (fun y => RelativeHessianCutoffSpatial.value (radius K) y * link u v j y) y +
        mvec K u v j y) := by
  rw [objJ_succ, add_gradient (objJ_smooth K j u v)
    ((cutLink_smooth K u v j).add (smask_smooth K u v j)),
    add_gradient (cutLink_smooth K u v j) (smask_smooth K u v j)]
  rfl

lemma answerS_succ (K j : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) (U : ℝ) :
    answerS K (j + 1) A u v y U = answerS K j A u v y U +
      (gradient (fun y => RelativeHessianCutoffSpatial.value (radius K) y * link u v j y) y +
        icoin (start K A u v j y) (prob K A u v j y) U • mvec K u v j y) := by
  unfold answerS
  rw [gradient_objJ_succ, Finset.sum_range_succ, sub_smul, one_smul]
  abel

lemma link_dead_value (u v : ℕ → E) (l : ℕ) (y : E)
    (h : ⟪v l, y⟫ ^ 2 ≤ 1 / 4096 ∨ (l ≠ 0 ∧ ⟪u (l - 1), y⟫ ≤ 1 / 2)) :
    link u v l y = 0 ∧ gradient (link u v l) y = 0 := by
  have hD : ∀ e, D (link u v l) y e = 0 := by
    intro e
    rw [D_link]
    rcases h with h | ⟨h0, h1⟩
    · obtain ⟨e0, e1, -, -⟩ := lam_flat h
      rw [e0, e1]; ring
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      simp only [Nat.succ_sub_one] at h1
      obtain ⟨p0, p1, -, -⟩ := psi_flat h1
      have hP : prevPsi u (l' + 1) y = 0 := by rw [EscapeChainBounds.prevPsi_succ, p0]
      have hdP : dPsi u (l' + 1) y e = 0 := by simp [dPsi, p1]
      rw [hP, hdP]; ring
  refine ⟨?_, ?_⟩
  · unfold link
    rcases h with h | ⟨h0, h1⟩
    · simp [RidgeJets.value, (lam_flat h).1]
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      simp only [Nat.succ_sub_one] at h1
      rw [EscapeChainBounds.prevPsi_succ, (psi_flat h1).1]; ring
  · apply ext_inner_right ℝ
    intro e
    have := hD e
    unfold D at this
    rw [this, inner_zero_left]

lemma cutLink_dead (u v : ℕ → E) (l : ℕ) (y : E)
    (h : ⟪v l, y⟫ ^ 2 ≤ 1 / 4096 ∨ (l ≠ 0 ∧ ⟪u (l - 1), y⟫ ≤ 1 / 2)) :
    gradient (fun y => RelativeHessianCutoffSpatial.value (radius K) y * link u v l y) y = 0 := by
  obtain ⟨h0, h1⟩ := link_dead_value u v l y h
  rw [ProductCompositionJets.product_gradient (RelativeHessianCutoffSpatial.smooth _)
    (link_smooth u v l), h0, h1, smul_zero, zero_smul, add_zero]

lemma saddle_dead_value (u v : ℕ → E) (l : ℕ) (y : E) (h0 : l ≠ 0) (h1 : ⟪u (l - 1), y⟫ ≤ 3 / 5) :
    saddle u v l y = 0 ∧ gradient (saddle u v l) y = 0 := by
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
  simp only [Nat.succ_sub_one] at h1
  obtain ⟨g0, g1, -, -⟩ := gam_flat h1
  have hG : prevGam u (l' + 1) y = 0 := by rw [EscapeChainBounds.prevGam_succ, g0]
  refine ⟨?_, ?_⟩
  · unfold saddle; rw [hG]; ring
  · apply ext_inner_right ℝ
    intro e
    have h := D_saddle u v (l' + 1) y e
    unfold D at h
    rw [h, hG, inner_zero_left]
    have hdG : dGam u (l' + 1) y e = 0 := by simp [dGam, g1]
    rw [hdG]; ring

lemma mvec_dead (u v : ℕ → E) (l : ℕ) (y : E) (h0 : l ≠ 0) (h1 : ⟪u (l - 1), y⟫ ≤ 3 / 5) :
    mvec K u v l y = 0 := by
  obtain ⟨s0, s1⟩ := saddle_dead_value u v l y h0 h1
  rw [mvec_eq, s0, s1, smul_zero, zero_smul, add_zero]

lemma prob_dead (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) (h0 : l ≠ 0) (h1 : ⟪u (l - 1), y⟫ ≤ 3 / 5) :
    prob K A u v l y = 0 := by
  unfold prob; rw [mvec_dead u v l y h0 h1]; simp

lemma answerS_step (A : ℝ) (u v : ℕ → E) (j : ℕ) (y : E) (U : ℝ)
    (h : (⟪v j, y⟫ ^ 2 ≤ 1 / 4096 ∧ ¬ reveals K A u v j y U) ∨ (j ≠ 0 ∧ ⟪u (j - 1), y⟫ ≤ 1 / 2)) :
    answerS K (j + 1) A u v y U = answerS K j A u v y U := by
  rw [answerS_succ]
  rcases h with ⟨hc, hr⟩ | ⟨h0, h1⟩
  · rw [cutLink_dead u v j y (Or.inl hc), icoin_zero_of_not hr, zero_smul, add_zero, add_zero]
  · rw [cutLink_dead u v j y (Or.inr ⟨h0, h1⟩), mvec_dead u v j y h0 (by linarith), smul_zero,
      add_zero, add_zero]

def Clean (K : ℕ) (u v : ℕ → E) (j : ℕ) (y : E) : Prop :=
  ∀ l, j ≤ l → l < K → |⟪u l, y⟫| ≤ 1 / 128 ∧ |⟪v l, y⟫| ≤ 1 / 128

lemma clean_sq {t : ℝ} (h : |t| ≤ 1 / 128) : t ^ 2 ≤ 1 / 16384 := by
  have := sq_abs t ▸ pow_le_pow_left₀ (abs_nonneg t) h 2
  nlinarith

lemma answer_eq_sim (A : ℝ) (u v : ℕ → E) {j : ℕ} (hj : j ≤ K) (y : E) (U : ℝ)
    (hc : Clean K u v j y) (hr : j < K → ¬ reveals K A u v j y U) :
    answerN K A u v y U = answerS K j A u v y U := by
  rw [← answerS_full]
  have key : ∀ n, j + n ≤ K → answerS K (j + n) A u v y U = answerS K j A u v y U := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [← ih (by omega), ← add_assoc]
      apply answerS_step
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp only [Nat.add_zero]
        left
        refine ⟨by have := (hc j le_rfl (by omega)).2; linarith [clean_sq this], hr (by omega)⟩
      · right
        refine ⟨by omega, ?_⟩
        have := (hc (j + n - 1) (by omega) (by omega)).1
        rw [show j + n - 1 = j + n - 1 from rfl]
        linarith [le_abs_self ⟪u (j + n - 1), y⟫]
  have := key (K - j) (by omega)
  rwa [Nat.add_sub_cancel' hj] at this

lemma no_reveal_of_clean (A : ℝ) (u v : ℕ → E) {j : ℕ} (y : E) (U : ℝ) (hc : Clean K u v j y)
    (hjK : j + 1 < K) : ¬ reveals K A u v (j + 1) y U := by
  intro h
  have hp : prob K A u v (j + 1) y = 0 := prob_dead A u v (j + 1) y (by omega) (by
    simp only [Nat.add_sub_cancel]
    have := (hc j le_rfl (by omega)).1
    linarith [le_abs_self ⟪u j, y⟫])
  unfold reveals at h
  rw [hp, add_zero] at h
  linarith [h.1, h.2]

end LongTails.Proofs.EscapeChainSimulator
