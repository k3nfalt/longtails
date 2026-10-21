import LongTails.Proofs.CertifiedLevelBroxTransition

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inv_init0 (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    {s : State E} {T : ℕ} (hst : s.stage = .init0) (hs : Inv c s T) (k : ℕ) (seed : O.Seed k) :
    Inv c (update c.R c.ε c.x0 s (O.answer k (0, query c.R c.x0 s) seed)) (T + 1) := by
  simp only [Inv, hst] at hs
  obtain ⟨hT, rfl⟩ := hs
  have hq : query c.R c.x0 ((algorithm c.R c.ε c.x0).initial ()) = .inl c.x0 := rfl
  rw [hq, hO.first k seed c.x0 c.x0_mem]
  simp [update, algorithm, Inv, hT]

lemma inv_frozen (c : Ctx E) {O : Oracle (Query E) (Reply E)}
    {s : State E} {T : ℕ} (hst : s.stage = .frozen) (hs : Inv c s T) (k : ℕ) (seed : O.Seed k) :
    Inv c (update c.R c.ε c.x0 s (O.answer k (0, query c.R c.x0 s) seed)) (T + 1) := by
  have hu : ∀ r, update c.R c.ε c.x0 s r = s := by
    intro r; cases r <;> simp [update, hst]
  rw [hu]
  simp only [Inv, hst] at hs ⊢
  exact hs

lemma inv_init1 (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    {s : State E} {T : ℕ} (hst : s.stage = .init1) (hs : Inv c s T) (k : ℕ) (seed : O.Seed k) :
    Inv c (update c.R c.ε c.x0 s (O.answer k (0, query c.R c.x0 s) seed)) (T + 1) := by
  simp only [Inv, hst] at hs
  obtain ⟨hT, hf0, hg0, hub, hbest, hph, hd⟩ := hs
  obtain ⟨v, hv, hvr, hmin, he⟩ := hO.linear k seed c.x0 c.R s.g0 c.x0_mem c.R_nonneg
  have hq : query c.R c.x0 s = .inr (c.x0, c.R, s.g0) := by simp [query, hst]
  rw [hq, he]
  have hu : update c.R c.ε c.x0 s (.inr v) =
      startPhase c.ε c.x0 { s with lb := s.f0 + ⟪s.g0, v - c.x0⟫, Lh := c.ε / c.R ^ 2 } := by
    simp [update, hst]
  rw [hu]
  set s' : State E := { s with lb := s.f0 + ⟪s.g0, v - c.x0⟫, Lh := c.ε / c.R ^ 2 } with hs'
  have hxs : ‖c.xs - c.x0‖ ≤ c.R := by rw [norm_sub_rev]; exact c.dist
  have hlb : s'.lb ≤ c.f c.xs := by
    have h1 := hmin c.xs c.xs_mem hxs
    have h2 := c.lower c.x0 c.x0_mem c.xs c.xs_mem
    simp only [hs', hf0, hg0, inner_sub_right] at *
    linarith
  have hgap : gap s' = ⟪c.grad c.x0, c.x0 - v⟫ := by
    simp only [gap, hs', hub, hf0, hg0, inner_sub_right]; ring
  apply inv_start c s' (T + 1)
  · exact ⟨hlb, by simp only [hs', hbest]; exact c.x0_mem, by simp only [hs', hub, hbest]⟩
  · intro hε
    have hR : 0 < c.R := by
      rcases (lt_or_eq_of_le c.R_nonneg) with h | h
      · exact h
      · exfalso
        have hv0 : v = c.x0 := by
          rw [← h] at hvr; exact sub_eq_zero.mp (norm_le_zero_iff.mp hvr)
        rw [hgap, hv0, sub_self, inner_zero_right] at hε
        linarith [c.ε_pos]
    refine ⟨hR, ?_, Or.inl hd, ?_⟩
    · show c.ε / c.R ^ 2 = c.ε / c.R ^ 2 * 2 ^ s.doublings
      rw [hd, pow_zero, mul_one]
    · show gap s' * (4 / 3 : ℝ) ^ s.phases ≤ c.Δ + c.L * c.R ^ 2 / 2
      rw [hph, pow_zero, mul_one, hgap]
      have hup := c.upper c.x0 c.x0_mem v hv
      have hvm := c.xs_min v hv
      have hg := c.gap0
      have hvr2 : ‖v - c.x0‖ ^ 2 ≤ c.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvr 2
      have hLv := mul_le_mul_of_nonneg_left hvr2 (show 0 ≤ c.L / 2 by linarith [c.L_nonneg])
      rw [inner_sub_right] at *
      nlinarith
  · intro _
    show ((T + 1 : ℕ) : ℝ) ≤ 200 * Real.sqrt (s'.Lh * c.R ^ 2 / gap s') +
      9 * ((s.phases : ℝ) + s.doublings) + 2
    rw [hph, hd, hT]
    have := Real.sqrt_nonneg (s'.Lh * c.R ^ 2 / gap s')
    push_cast
    linarith

end OracleTemplate.CertifiedLevelBrox
