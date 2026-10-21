import LongTails.Proofs.CertifiedLevelBroxRunStep

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma final_value_le (c : Ctx E) {s : State E} (hgap : 0 < gap s)
    {h : c.f c.xs ≤ level s} {hL : 0 ≤ s.Lh}
    (hI : LevelInvariant (goodModel c s h hL) (phaseK c.R s) (phaseB c.R s) c.R s.inner)
    (hK : s.inner.completed = phaseK c.R s) :
    c.f s.inner.primal ≤ level s + gap s / 4 := by
  have he := hI.energy
  rw [hK] at he
  have hb := base_sq c.R s.Lh (gap s)
  have hw := horizon_weight (R := c.R) hgap hL
  have hpos : 0 < potentialWeight (phaseK c.R s) := by
    unfold potentialWeight
    have : (0 : ℝ) < phaseK c.R s := by exact_mod_cast horizon_pos c.R s.Lh (gap s)
    positivity
  have hm : 0 ≤ 4 * s.Lh * ‖s.inner.momentum - c.xs‖ ^ 2 := by positivity
  have hkb : (phaseK c.R s : ℝ) * s.Lh * phaseB c.R s ^ 2 = s.Lh * c.R ^ 2 := by
    unfold phaseK phaseB; rw [hb]; ring
  change potentialWeight (phaseK c.R s) * (c.f s.inner.primal - level s) +
    4 * s.Lh * ‖s.inner.momentum - c.xs‖ ^ 2 ≤
    4 * s.Lh * c.R ^ 2 + (phaseK c.R s : ℝ) * s.Lh * phaseB c.R s ^ 2 at he
  have hw' : 5 * s.Lh * c.R ^ 2 ≤ potentialWeight (phaseK c.R s) * (gap s / 4) := hw
  have h1 : potentialWeight (phaseK c.R s) * (c.f s.inner.primal - level s) ≤
      potentialWeight (phaseK c.R s) * (gap s / 4) := by
    linarith
  have h2 := le_of_mul_le_mul_left h1 hpos
  linarith

lemma inv_check (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    {s : State E} {T : ℕ} (hst : s.stage = .check) (hs : Inv c s T) (history : List ((Fin 1 × Query E) × Reply E)) (seed : O.Seed history.length) :
    Inv c (update c.R c.ε c.x0 s (O.answer history (0, query c.R c.x0 s) seed)) (T + 1) := by
  simp only [Inv, hst] at hs
  obtain ⟨hv, hp, hc, hk⟩ := hs
  have hR := hp.R_pos
  have hL := hp.Lh_nonneg
  have hgap : 0 < gap s := lt_trans c.ε_pos hk.gap_gt
  have hy := hk.feasible.primal_mem
  have hq : query c.R c.x0 s = .inl s.inner.primal := by simp [query, hst]
  rw [hq, hO.first history seed _ hy]
  have hu : update c.R c.ε c.x0 s (.inl (c.f s.inner.primal, c.grad s.inner.primal)) =
      checkUpdate c.R c.ε c.x0 s (c.f s.inner.primal) := by simp [update, hst]
  rw [hu]
  unfold Count at hc
  simp only [checkUpdate, hk.zval_eq, hk.zg_eq]
  by_cases hfail : c.f s.zpt + ⟪c.grad s.zpt, s.inner.primal - s.zpt⟫ +
      s.Lh / 2 * ‖s.inner.primal - s.zpt‖ ^ 2 < c.f s.inner.primal
  · rw [ite_eq_left hfail]
    have hLL : s.Lh ≤ c.L := by
      by_contra hlt
      have hup := c.upper s.zpt hk.zpt_mem s.inner.primal hy
      have hsq := sq_nonneg ‖s.inner.primal - s.zpt‖
      have : c.L / 2 * ‖s.inner.primal - s.zpt‖ ^ 2 ≤ s.Lh / 2 * ‖s.inner.primal - s.zpt‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsq; linarith
      linarith
    exact double_transition c hv hp hc hk.calls_le hLL rfl rfl rfl rfl rfl rfl
  · rw [ite_eq_right hfail]
    have hpass : UpperAt c s.Lh s.zpt s.inner.primal := le_of_not_gt hfail
    by_cases hK : phaseK c.R s ≤ s.inner.completed
    · rw [ite_eq_left hK]
      have hKe : s.inner.completed = phaseK c.R s := le_antisymm hk.completed_le hK
      by_cases hval : c.f s.inner.primal ≤ level s + gap s / 4
      · rw [ite_eq_left hval]
        exact upper_transition c hv hp hc hk.calls_le s.inner.primal hy hval
          rfl rfl rfl rfl rfl rfl
      · rw [ite_eq_right hval]
        have hl : level s < c.f c.xs := by
          by_contra hle
          have hI := (hk.good (le_of_not_gt hle) hL).1 hpass
          exact hval (final_value_le c hgap hI hKe)
        exact lower_transition c hv hp hc hgap hk.calls_le hl rfl rfl rfl rfl rfl rfl
    · rw [ite_eq_right hK]
      have hlt : s.inner.completed < phaseK c.R s := lt_of_not_ge hK
      by_cases hcap : 4 * phaseK c.R s ≤ s.calls + 1
      · rw [ite_eq_left hcap]
        have hl : level s < c.f c.xs :=
          level_lt_of_cap c (fun h hL' => ⟨(hk.good h hL').1 hpass, (hk.good h hL').2⟩)
            hL hR hlt hcap
        exact lower_transition c hv hp hc hgap hk.calls_le hl rfl rfl rfl rfl rfl rfl
      · rw [ite_eq_right hcap]
        simp only [Inv]
        refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hp.R_pos, hp.Lh_eq, hp.Lh_le, hp.shrink⟩, ?_, ?_⟩
        · unfold Count gap at *; dsimp only at *; push_cast; linarith
        · refine ⟨hk.gap_gt, hlt, by show s.calls + 1 < 4 * phaseK c.R s; omega, hk.feasible, ?_, ?_⟩
          · dsimp only
            rw [hk.phase_first]
            trivial
          · intro h hL'
            exact ⟨(hk.good h hL').1 hpass, by have := (hk.good h hL').2; dsimp only; omega⟩

end OracleTemplate.CertifiedLevelBrox
