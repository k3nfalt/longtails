import LongTails.Proofs.SplitBroxStep
import LongTails.Proofs.SplitBroxGeometry
import LongTails.Proofs.SplitBroxCounting

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure LevelModel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  C : Set E
  f : E → ℝ
  grad : E → E
  L : ℝ
  level : ℝ
  anchor : E
  convex : Convex ℝ C
  L_nonneg : 0 ≤ L
  anchor_mem : anchor ∈ C
  anchor_le : f anchor ≤ level
  lower : ∀ x ∈ C, ∀ y ∈ C, f x + ⟪grad x, y - x⟫ ≤ f y

structure LevelInvariant (M : LevelModel E) (K : ℕ) (b R : ℝ) (s : State E) : Prop where
  completed_le : s.completed ≤ K
  momentum_mem : s.momentum ∈ M.C
  primal_mem : s.primal ∈ M.C
  energy : potentialWeight s.completed * (M.f s.primal - M.level) +
    4 * M.L * ‖s.momentum - M.anchor‖ ^ 2 ≤ 4 * M.L * R ^ 2 + s.completed * M.L * b ^ 2
  calls : s.extra * b ^ 2 + ‖s.momentum - M.anchor‖ ^ 2 ≤ R ^ 2
  phase_valid : match s.phase with
    | .first => True
    | .local g cut j previous =>
      g = M.grad (mix s.completed s.primal s.momentum) ∧
      cut = M.f (mix s.completed s.primal s.momentum) +
        ⟪g, s.momentum - mix s.completed s.primal s.momentum⟫ - M.level ∧
      0 < cut ∧
      (if j = 0 then previous = s.momentum else
        previous ∈ M.C ∧ ‖previous - M.anchor‖ ^ 2 ≤
          ‖s.momentum - M.anchor‖ ^ 2 - (radius b (j - 1)) ^ 2)

lemma level_invariant_initial (M : LevelModel E) (K : ℕ) (b R : ℝ) (x0 : E)
    (hx : x0 ∈ M.C) (hd : ‖x0 - M.anchor‖ ^ 2 ≤ R ^ 2) :
    LevelInvariant M K b R ⟨0, 0, x0, x0, .first⟩ := by
  constructor
  · simp
  · exact hx
  · exact hx
  · simp only [potentialWeight, Nat.cast_zero, zero_mul, zero_add]
    simpa using mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * M.L from mul_nonneg (by norm_num) M.L_nonneg)
  · simpa using hd
  · trivial

lemma level_invariant_completion (M : LevelModel E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : LevelInvariant M K b R s) (hn : s.completed < K)
    (j : ℕ) (x y : E) (d r : ℝ)
    (hx : x ∈ M.C) (hy : y ∈ M.C)
    (hcharge : (j : ℝ) * b ^ 2 ≤ d)
    (hdecrease : ‖x - M.anchor‖ ^ 2 ≤ ‖s.momentum - M.anchor‖ ^ 2 - d)
    (hradius : r ^ 2 ≤ 4 * d + b ^ 2)
    (hstep : potentialWeight (s.completed + 1) * (M.f y - M.level) ≤
      potentialWeight s.completed * (M.f s.primal - M.level) + M.L * r ^ 2) :
    LevelInvariant M K b R ⟨s.completed + 1, s.extra + j, x, y, .first⟩ := by
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

lemma level_invariant_first (M : LevelModel E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : LevelInvariant M K b R s) (hn : s.completed < K) (hp : s.phase = .first) :
    LevelInvariant M K b R (update K M.level s
      (.inl (M.f (mix s.completed s.primal s.momentum),
        M.grad (mix s.completed s.primal s.momentum)))) := by
  have hz := mix_mem M.convex hs.momentum_mem hs.primal_mem s.completed
  unfold update
  rw [ite_eq_right (by omega), hp]
  dsimp only
  split_ifs with hcut
  · apply level_invariant_completion M hs hn 0 s.momentum _ 0 0 hs.momentum_mem hz
    · simp
    · simp
    · simpa using sq_nonneg b
    · apply weighted_cut_step s.completed M.L_nonneg
      apply cut_step s.completed M.L_nonneg _ (M.lower _ hz _ hs.primal_mem)
      · linarith
      · simp
      · simp
  · constructor
    · exact hs.completed_le
    · exact hs.momentum_mem
    · exact hs.primal_mem
    · exact hs.energy
    · exact hs.calls
    · exact ⟨rfl, rfl, lt_of_not_ge hcut, by simp⟩

lemma level_invariant_local (M : LevelModel E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : LevelInvariant M K b R s) (hn : s.completed < K) (hb : 0 < b)
    (g : E) (cut : ℝ) (j : ℕ) (previous v : E)
    (hp : s.phase = .local g cut j previous)
    (hv : v ∈ M.C) (hvr : ‖v - s.momentum‖ ≤ radius b j)
    (hmin : ∀ z ∈ M.C, ‖z - s.momentum‖ ≤ radius b j → ⟪g, v⟫ ≤ ⟪g, z⟫)
    (hupper : cut ≤ ⟪g, s.momentum - v⟫ →
      M.f (mix s.completed s.primal v) ≤ M.f (mix s.completed s.primal s.momentum) +
      ⟪g, mix s.completed s.primal v - mix s.completed s.primal s.momentum⟫ +
      M.L / 2 * ‖mix s.completed s.primal v - mix s.completed s.primal s.momentum‖ ^ 2) :
    LevelInvariant M K b R (update K M.level s (.inr v)) := by
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
        (M.f (mix s.completed s.primal v) - M.level) ≤
        potentialWeight s.completed * (M.f s.primal - M.level) + M.L * (radius b j) ^ 2 := by
      apply weighted_cut_step s.completed M.L_nonneg
      apply cut_step (g := g) (x := s.momentum) s.completed M.L_nonneg (hupper hcross)
      · rw [hg]; exact M.lower _ hz _ hs.primal_mem
      · rw [inner_sub_right] at hcross
        rw [hcut, inner_sub_right] at hcross
        rw [inner_sub_right]
        linarith
      · exact hvr
    by_cases hj : j = 0
    · subst j
      simp only [ite_true]
      apply level_invariant_completion M hs hn 0 s.momentum _ 0 (radius b 0)
        hs.momentum_mem (mix_mem M.convex hv hs.primal_mem _) _ _ _ hstep
      · simp
      · simp
      · simp [radius]
    · simp only [hj, ite_false] at hprevious ⊢
      obtain ⟨hpmem, hpdist⟩ := hprevious
      apply level_invariant_completion M hs hn j previous _ ((radius b (j - 1)) ^ 2) (radius b j)
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
    have hsep : ⟪g, M.anchor⟫ < ⟪g, v⟫ := by
      have hl := M.lower _ hz _ M.anchor_mem
      have ha := M.anchor_le
      rw [← hg, inner_sub_right] at hl
      rw [hcut, inner_sub_right, inner_sub_right] at hcross
      linarith
    have hc := local_strict_cut_contraction M.convex M.anchor_mem hv
      (le_of_lt (radius_pos hb j)) hvr hmin hsep
    constructor
    · exact hs.completed_le
    · exact hs.momentum_mem
    · exact hs.primal_mem
    · exact hs.energy
    · exact hs.calls
    · exact ⟨hg, hcut, hpos, by simpa using And.intro hv hc.2⟩

lemma level_pending_calls (M : LevelModel E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : LevelInvariant M K b R s) (hb : 0 < b) (hR : R ^ 2 ≤ (K : ℝ) * b ^ 2)
    (g : E) (cut : ℝ) (j : ℕ) (previous : E)
    (hp : s.phase = .local g cut j previous) : s.extra + j ≤ K := by
  have hc := hs.calls
  have he : (s.extra + j : ℝ) * b ^ 2 ≤ R ^ 2 := by
    by_cases hj : j = 0
    · subst j
      simp only [Nat.cast_zero, add_zero]
      nlinarith [sq_nonneg ‖s.momentum - M.anchor‖]
    · have hv := hs.phase_valid
      rw [hp] at hv
      have hd := hv.2.2.2
      simp only [hj, ite_false] at hd
      have hjc := mul_le_mul_of_nonneg_right (doublings_charge (j - 1)) (sq_nonneg b)
      have hj1 : j - 1 + 1 = j := by omega
      have hjreal : (j - 1 : ℕ) + (1 : ℝ) = j := by exact_mod_cast hj1
      rw [hjreal] at hjc
      simp only [radius, mul_pow] at hd
      nlinarith [sq_nonneg ‖previous - M.anchor‖]
  have heK := le_trans he hR
  have hsq : 0 < b ^ 2 := sq_pos_of_pos hb
  have hreal : (s.extra : ℝ) + (j : ℝ) ≤ K := (mul_le_mul_iff_left₀ hsq).mp heK
  exact_mod_cast hreal

lemma level_incomplete_rank (M : LevelModel E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : LevelInvariant M K b R s) (hb : 0 < b) (hR : R ^ 2 ≤ (K : ℝ) * b ^ 2)
    (hn : s.completed < K) : rank s < 3 * K := by
  cases hp : s.phase with
  | first =>
    have hc := hs.calls
    have he : (s.extra : ℝ) * b ^ 2 ≤ (K : ℝ) * b ^ 2 := by
      nlinarith [sq_nonneg ‖s.momentum - M.anchor‖]
    have hre : (s.extra : ℝ) ≤ K := (mul_le_mul_iff_left₀ (sq_pos_of_pos hb)).mp he
    have hen : s.extra ≤ K := by exact_mod_cast hre
    simp only [rank, hp]
    omega
  | «local» g cut j previous =>
    have hc := level_pending_calls M hs hb hR g cut j previous hp
    simp only [rank, hp]
    omega

end OracleTemplate.SplitBrox
