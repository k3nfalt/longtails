import LongTails.Proofs.SplitBroxStep
import LongTails.Proofs.SplitBroxGeometry

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Model (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  C : Set E
  f : E → ℝ
  grad : E → E
  L : ℝ
  fstar : ℝ
  xstar : E
  convex : Convex ℝ C
  L_nonneg : 0 ≤ L
  star_mem : xstar ∈ C
  star_value : f xstar = fstar
  lower : ∀ x ∈ C, ∀ y ∈ C, f x + ⟪grad x, y - x⟫ ≤ f y
  upper : ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2

structure Invariant (M : Model E) (K : ℕ) (b R : ℝ) (s : State E) : Prop where
  completed_le : s.completed ≤ K
  momentum_mem : s.momentum ∈ M.C
  primal_mem : s.primal ∈ M.C
  energy : potentialWeight s.completed * (M.f s.primal - M.fstar) +
    4 * M.L * ‖s.momentum - M.xstar‖ ^ 2 ≤ 4 * M.L * R ^ 2 + s.completed * M.L * b ^ 2
  calls : s.extra * b ^ 2 + ‖s.momentum - M.xstar‖ ^ 2 ≤ R ^ 2
  phase_valid : match s.phase with
    | .first => True
    | .local g cut j previous =>
      g = M.grad (mix s.completed s.primal s.momentum) ∧
      cut = M.f (mix s.completed s.primal s.momentum) +
        ⟪g, s.momentum - mix s.completed s.primal s.momentum⟫ - M.fstar ∧
      0 < cut ∧
      (if j = 0 then previous = s.momentum else
        previous ∈ M.C ∧ ‖previous - M.xstar‖ ^ 2 ≤
          ‖s.momentum - M.xstar‖ ^ 2 - (radius b (j - 1)) ^ 2)

lemma invariant_initial (M : Model E) (K : ℕ) (b R : ℝ) (x0 : E)
    (hx : x0 ∈ M.C) (hd : ‖x0 - M.xstar‖ ^ 2 ≤ R ^ 2) :
    Invariant M K b R ⟨0, 0, x0, x0, .first⟩ := by
  constructor
  · simp
  · exact hx
  · exact hx
  · simp only [potentialWeight, Nat.cast_zero, zero_mul, zero_add]
    simpa using mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * M.L from mul_nonneg (by norm_num) M.L_nonneg)
  · simpa using hd
  · trivial

lemma invariant_completion (M : Model E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hn : s.completed < K)
    (j : ℕ) (x y : E) (d r : ℝ)
    (hx : x ∈ M.C) (hy : y ∈ M.C)
    (hcharge : (j : ℝ) * b ^ 2 ≤ d)
    (hdecrease : ‖x - M.xstar‖ ^ 2 ≤ ‖s.momentum - M.xstar‖ ^ 2 - d)
    (hradius : r ^ 2 ≤ 4 * d + b ^ 2)
    (hstep : potentialWeight (s.completed + 1) * (M.f y - M.fstar) ≤
      potentialWeight s.completed * (M.f s.primal - M.fstar) + M.L * r ^ 2) :
    Invariant M K b R ⟨s.completed + 1, s.extra + j, x, y, .first⟩ := by
  constructor
  · dsimp; omega
  · exact hx
  · exact hy
  · dsimp
    push_cast
    have h1 := mul_le_mul_of_nonneg_left hdecrease (show 0 ≤ 4 * M.L from mul_nonneg (by norm_num) M.L_nonneg)
    have h2 := mul_le_mul_of_nonneg_left hradius M.L_nonneg
    have he := hs.energy
    nlinarith
  · dsimp
    push_cast
    have hc := hs.calls
    nlinarith
  · trivial

lemma invariant_first (M : Model E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hn : s.completed < K) (hp : s.phase = .first) :
    Invariant M K b R (update K M.fstar s
      (.inl (M.f (mix s.completed s.primal s.momentum),
        M.grad (mix s.completed s.primal s.momentum)))) := by
  have hz := mix_mem M.convex hs.momentum_mem hs.primal_mem s.completed
  unfold update
  rw [ite_eq_right (by omega), hp]
  dsimp only
  split_ifs with hcut
  · apply invariant_completion M hs hn 0 s.momentum _ 0 0 hs.momentum_mem hz
    · simp
    · simp
    · simpa using sq_nonneg b
    · apply weighted_cut_step s.completed M.L_nonneg
      apply cut_step s.completed M.L_nonneg
        (M.upper _ hz _ hz) (M.lower _ hz _ hs.primal_mem)
      · linarith
      · simp
  · constructor
    · exact hs.completed_le
    · exact hs.momentum_mem
    · exact hs.primal_mem
    · exact hs.energy
    · exact hs.calls
    · exact ⟨rfl, rfl, lt_of_not_ge hcut, by simp⟩

lemma invariant_local (M : Model E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hn : s.completed < K) (hb : 0 < b)
    (g : E) (cut : ℝ) (j : ℕ) (previous v : E)
    (hp : s.phase = .local g cut j previous)
    (hv : v ∈ M.C) (hvr : ‖v - s.momentum‖ ≤ radius b j)
    (hmin : ∀ z ∈ M.C, ‖z - s.momentum‖ ≤ radius b j → ⟪g, v⟫ ≤ ⟪g, z⟫) :
    Invariant M K b R (update K M.fstar s (.inr v)) := by
  have hphase := hs.phase_valid
  rw [hp] at hphase
  obtain ⟨hg, hcut, hpos, hprevious⟩ := hphase
  have hz := mix_mem M.convex hs.momentum_mem hs.primal_mem s.completed
  unfold update
  rw [ite_eq_right (by omega), hp]
  dsimp only
  by_cases hcross : cut ≤ ⟪g, s.momentum - v⟫
  · rw [ite_eq_left hcross]
    have hstep : potentialWeight (s.completed + 1) *
        (M.f (mix s.completed s.primal v) - M.fstar) ≤
        potentialWeight s.completed * (M.f s.primal - M.fstar) + M.L * (radius b j) ^ 2 := by
      apply weighted_cut_step s.completed M.L_nonneg
      apply cut_step (g := g) (x := s.momentum) s.completed M.L_nonneg
      · rw [hg]; exact M.upper _ hz _ (mix_mem M.convex hv hs.primal_mem _)
      · rw [hg]; exact M.lower _ hz _ hs.primal_mem
      · rw [inner_sub_right] at hcross
        rw [hcut, inner_sub_right] at hcross
        rw [inner_sub_right]
        linarith
      · exact hvr
    by_cases hj : j = 0
    · subst j
      simp only [ite_true]
      apply invariant_completion M hs hn 0 s.momentum _ 0 (radius b 0)
        hs.momentum_mem (mix_mem M.convex hv hs.primal_mem _) _ _ _ hstep
      · simp
      · simp
      · simp [radius]
    · simp only [hj, ite_false] at hprevious ⊢
      obtain ⟨hpmem, hpdist⟩ := hprevious
      apply invariant_completion M hs hn j previous _ ((radius b (j - 1)) ^ 2) (radius b j)
        hpmem (mix_mem M.convex hv hs.primal_mem _) _ hpdist _ hstep
      · have hc := mul_le_mul_of_nonneg_right (doublings_charge (j - 1)) (sq_nonneg b)
        have hj1 : j - 1 + 1 = j := by omega
        have hjreal : (j - 1 : ℕ) + (1 : ℝ) = j := by exact_mod_cast hj1
        rw [hjreal] at hc
        simpa [radius, mul_pow] using hc
      · have hj1 : j = (j - 1) + 1 := by omega
        rw [hj1, radius_succ]
        have hj2 : j - 1 + 1 - 1 = j - 1 := by omega
        rw [hj2]
        nlinarith [sq_nonneg b]
  · rw [ite_eq_right hcross]
    have hsep : ⟪g, M.xstar⟫ < ⟪g, v⟫ := by
      have hl := M.lower _ hz _ M.star_mem
      rw [M.star_value, ← hg, inner_sub_right] at hl
      rw [hcut, inner_sub_right, inner_sub_right] at hcross
      linarith
    have hc := local_strict_cut_contraction M.convex M.star_mem hv
      (le_of_lt (radius_pos hb j)) hvr hmin hsep
    constructor
    · exact hs.completed_le
    · exact hs.momentum_mem
    · exact hs.primal_mem
    · exact hs.energy
    · exact hs.calls
    · exact ⟨hg, hcut, hpos, by simpa using And.intro hv hc.2⟩

end OracleTemplate.SplitBrox
