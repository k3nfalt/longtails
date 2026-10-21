import LongTails.Proofs.CertifiedLevelBroxInit

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sb_first_cut {K : ℕ} {ℓ : ℝ} {t : SplitBrox.State E} (hn : t.completed < K)
    (hp : t.phase = .first) {value : ℝ} {g : E}
    (hc : value + ⟪g, t.momentum - mix t.completed t.primal t.momentum⟫ - ℓ ≤ 0) :
    SplitBrox.update K ℓ t (.inl (value, g)) =
      { t with completed := t.completed + 1, primal := mix t.completed t.primal t.momentum, phase := .first } := by
  simp only [SplitBrox.update, ite_eq_right (not_le.mpr hn), hp]
  exact ite_eq_left hc

lemma sb_first_nocut {K : ℕ} {ℓ : ℝ} {t : SplitBrox.State E} (hn : t.completed < K)
    (hp : t.phase = .first) {value : ℝ} {g : E}
    (hc : ¬ value + ⟪g, t.momentum - mix t.completed t.primal t.momentum⟫ - ℓ ≤ 0) :
    SplitBrox.update K ℓ t (.inl (value, g)) =
      { t with phase := .local g (value + ⟪g, t.momentum - mix t.completed t.primal t.momentum⟫ - ℓ) 0 t.momentum } := by
  simp only [SplitBrox.update, ite_eq_right (not_le.mpr hn), hp]
  exact ite_eq_right hc

lemma sb_local_cross {K : ℕ} {ℓ : ℝ} {t : SplitBrox.State E} (hn : t.completed < K)
    {g : E} {cut : ℝ} {j : ℕ} {prev v : E} (hp : t.phase = .local g cut j prev)
    (hc : cut ≤ ⟪g, t.momentum - v⟫) :
    SplitBrox.update K ℓ t (.inr v) =
      ⟨t.completed + 1, t.extra + j, if j = 0 then t.momentum else prev,
        mix t.completed t.primal v, .first⟩ := by
  simp only [SplitBrox.update, ite_eq_right (not_le.mpr hn), hp]
  exact ite_eq_left hc

lemma sb_local_nocross {K : ℕ} {ℓ : ℝ} {t : SplitBrox.State E} (hn : t.completed < K)
    {g : E} {cut : ℝ} {j : ℕ} {prev v : E} (hp : t.phase = .local g cut j prev)
    (hc : ¬ cut ≤ ⟪g, t.momentum - v⟫) :
    SplitBrox.update K ℓ t (.inr v) = { t with phase := .local g cut (j + 1) v } := by
  simp only [SplitBrox.update, ite_eq_right (not_le.mpr hn), hp]
  exact ite_eq_right hc

lemma runUpdate_first (R ε : ℝ) (x0 : E) (s : State E) (hp : s.inner.phase = .first)
    (value : ℝ) (g : E) :
    runUpdate R ε x0 s (.inl (value, g)) =
      let t := SplitBrox.update (phaseK R s) (level s) s.inner (.inl (value, g))
      let s1 : State E := { s with zval := value, zpt := mix s.inner.completed s.inner.primal s.inner.momentum, zg := g }
      if s.inner.completed < t.completed then { s1 with stage := .check, inner := t, calls := s.calls + 1 }
      else if 4 * phaseK R s ≤ s.calls + 1 then
        startPhase ε x0 { s1 with lb := level s, phases := s.phases + 1, calls := s.calls + 1 }
      else { s1 with inner := t, calls := s.calls + 1 } := by
  simp only [runUpdate, hp]

lemma runUpdate_local (R ε : ℝ) (x0 : E) (s : State E) {g : E} {cut : ℝ} {j : ℕ} {prev : E}
    (hp : s.inner.phase = .local g cut j prev) (v : E) :
    runUpdate R ε x0 s (.inr v) =
      let t := SplitBrox.update (phaseK R s) (level s) s.inner (.inr v)
      if s.inner.completed < t.completed then { s with stage := .check, inner := t, calls := s.calls + 1 }
      else if 4 * phaseK R s ≤ s.calls + 1 then
        startPhase ε x0 { s with lb := level s, phases := s.phases + 1, calls := s.calls + 1 }
      else { s with inner := t, calls := s.calls + 1 } := by
  simp only [runUpdate, hp]

lemma inv_run (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    {s : State E} {T : ℕ} (hst : s.stage = .run) (hs : Inv c s T) (k : ℕ) (seed : O.Seed k) :
    Inv c (update c.R c.ε c.x0 s (O.answer k (0, query c.R c.x0 s) seed)) (T + 1) := by
  simp only [Inv, hst] at hs
  obtain ⟨hv, hp, hc, hr⟩ := hs
  have hR := hp.R_pos
  have hL := hp.Lh_nonneg
  have hgap : 0 < gap s := lt_trans c.ε_pos hr.gap_gt
  have hn := hr.completed_lt
  have hcl := hr.calls_lt
  have hbpos : 0 < phaseB c.R s := base_pos hR
  have hupd : ∀ r, update c.R c.ε c.x0 s r = runUpdate c.R c.ε c.x0 s r := by
    intro r; rcases r with ⟨value, g⟩ | v <;> simp [update, hst]
  have hq : query c.R c.x0 s = SplitBrox.query (phaseK c.R s) (phaseB c.R s) s.inner := by
    simp [query, hst]
  rw [hq, hupd]
  unfold Count at hc
  cases hph : s.inner.phase with
  | first =>
    have hz : mix s.inner.completed s.inner.primal s.inner.momentum ∈ c.C :=
      mix_mem c.convex hr.feasible.momentum_mem hr.feasible.primal_mem _
    have hq2 : SplitBrox.query (phaseK c.R s) (phaseB c.R s) s.inner =
        .inl (mix s.inner.completed s.inner.primal s.inner.momentum) := by
      simp [SplitBrox.query, not_le.mpr hn, hph]
    rw [hq2, hO.first k seed _ hz, runUpdate_first _ _ _ s hph]
    have hrank : rank s.inner + 1 ≤ rank (SplitBrox.update (phaseK c.R s) (level s) s.inner
        (.inl (c.f (mix s.inner.completed s.inner.primal s.inner.momentum),
          c.grad (mix s.inner.completed s.inner.primal s.inner.momentum)))) :=
      rank_update hn (by simp [Matches, hph])
    have hgoodt : ∀ h hL', LevelInvariant (goodModel c s h hL') (phaseK c.R s) (phaseB c.R s) c.R
        (SplitBrox.update (phaseK c.R s) (level s) s.inner
          (.inl (c.f (mix s.inner.completed s.inner.primal s.inner.momentum),
            c.grad (mix s.inner.completed s.inner.primal s.inner.momentum)))) :=
      fun h hL' => level_invariant_first (goodModel c s h hL') (hr.good h hL').1 hn hph
    by_cases hcut : c.f (mix s.inner.completed s.inner.primal s.inner.momentum) +
        ⟪c.grad (mix s.inner.completed s.inner.primal s.inner.momentum),
          s.inner.momentum - mix s.inner.completed s.inner.primal s.inner.momentum⟫ - level s ≤ 0
    · have ht := sb_first_cut (K := phaseK c.R s) (ℓ := level s) hn hph hcut
      rw [ht] at hrank hgoodt
      simp only [ht]
      rw [ite_eq_left (show s.inner.completed < s.inner.completed + 1 by omega)]
      simp only [Inv]
      refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hp.R_pos, hp.Lh_eq, hp.Lh_le, hp.shrink⟩, ?_, ?_⟩
      · unfold Count gap at *; dsimp only at *; push_cast; linarith
      · refine ⟨hr.gap_gt, by simp, ?_, ?_, ⟨hr.feasible.momentum_mem, hz, trivial⟩, rfl, hz,
          rfl, rfl, ?_⟩
        · show s.inner.completed + 1 ≤ phaseK c.R s; omega
        · show s.calls + 1 ≤ 4 * phaseK c.R s; omega
        · intro h hL'
          refine ⟨fun _ => hgoodt h hL', ?_⟩
          have := (hr.good h hL').2
          dsimp only
          omega
    · have ht := sb_first_nocut (K := phaseK c.R s) (ℓ := level s) hn hph hcut
      rw [ht] at hrank hgoodt
      simp only [ht]
      rw [ite_eq_right (show ¬ s.inner.completed < s.inner.completed by omega)]
      by_cases hcap : 4 * phaseK c.R s ≤ s.calls + 1
      · rw [ite_eq_left hcap]
        have hl : level s < c.f c.xs := by
          refine level_lt_of_cap c (fun h hL' => ⟨hgoodt h hL', ?_⟩) hL hR hn hcap
          have := (hr.good h hL').2
          dsimp only
          omega
        exact lower_transition c hv hp hc hgap (le_of_lt hcl) hl rfl rfl rfl rfl rfl rfl
      · rw [ite_eq_right hcap]
        simp only [Inv, hst]
        refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hp.R_pos, hp.Lh_eq, hp.Lh_le, hp.shrink⟩, ?_, ?_⟩
        · unfold Count gap at *; dsimp only at *; push_cast; linarith
        · refine ⟨hr.gap_gt, hn, by show s.calls + 1 < 4 * phaseK c.R s; omega,
            ⟨hr.feasible.momentum_mem, hr.feasible.primal_mem, hr.feasible.momentum_mem⟩,
            ⟨rfl, rfl, rfl⟩, ?_⟩
          intro h hL'
          refine ⟨hgoodt h hL', ?_⟩
          have := (hr.good h hL').2
          dsimp only
          omega
  | «local» g cut j prev =>
    have hfz := hr.zfacts
    rw [hph] at hfz
    obtain ⟨hzpt, hzval, hzg⟩ := hfz
    have hprev : prev ∈ c.C := by
      have := hr.feasible.previous_mem; rw [hph] at this; exact this
    obtain ⟨v, hv', hvr, hmin, he⟩ := hO.linear k seed s.inner.momentum
      (radius (phaseB c.R s) j) g hr.feasible.momentum_mem (le_of_lt (radius_pos hbpos j))
    have hq2 : SplitBrox.query (phaseK c.R s) (phaseB c.R s) s.inner =
        .inr (s.inner.momentum, radius (phaseB c.R s) j, g) := by
      simp [SplitBrox.query, not_le.mpr hn, hph]
    rw [hq2, he, runUpdate_local _ _ _ s hph]
    have hrank : rank s.inner + 1 ≤
        rank (SplitBrox.update (phaseK c.R s) (level s) s.inner (.inr v)) :=
      rank_update hn (by simp [Matches, hph])
    by_cases hcr : cut ≤ ⟪g, s.inner.momentum - v⟫
    · have ht := sb_local_cross (K := phaseK c.R s) (ℓ := level s) hn hph hcr
      have hgoodt : ∀ h hL', UpperAt c s.Lh s.zpt (mix s.inner.completed s.inner.primal v) →
          LevelInvariant (goodModel c s h hL') (phaseK c.R s) (phaseB c.R s) c.R
            (SplitBrox.update (phaseK c.R s) (level s) s.inner (.inr v)) := by
        intro h hL' hu
        have hI := (hr.good h hL').1
        have hpv := hI.phase_valid
        rw [hph] at hpv
        apply level_invariant_local (goodModel c s h hL') hI hn hbpos g cut j prev v hph hv' hvr hmin
        intro _
        have hg : g = c.grad s.zpt := by rw [hzpt]; exact hpv.1
        unfold UpperAt at hu
        rw [hg, ← hzpt]
        exact hu
      rw [ht] at hrank hgoodt
      simp only [ht]
      rw [ite_eq_left (show s.inner.completed < s.inner.completed + 1 by omega)]
      simp only [Inv]
      refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hp.R_pos, hp.Lh_eq, hp.Lh_le, hp.shrink⟩, ?_, ?_⟩
      · unfold Count gap at *; dsimp only at *; push_cast; linarith
      · have hmom : (if j = 0 then s.inner.momentum else prev) ∈ c.C := by
          split_ifs
          · exact hr.feasible.momentum_mem
          · exact hprev
        have hzm : s.zpt ∈ c.C := by
          rw [hzpt]; exact mix_mem c.convex hr.feasible.momentum_mem hr.feasible.primal_mem _
        refine ⟨hr.gap_gt, by simp, ?_, ?_,
          ⟨hmom, mix_mem c.convex hv' hr.feasible.primal_mem _, trivial⟩, rfl, hzm,
          hzval, hzg, ?_⟩
        · show s.inner.completed + 1 ≤ phaseK c.R s; omega
        · show s.calls + 1 ≤ 4 * phaseK c.R s; omega
        · intro h hL'
          refine ⟨fun hu => hgoodt h hL' hu, ?_⟩
          have := (hr.good h hL').2
          dsimp only
          omega
    · have ht := sb_local_nocross (K := phaseK c.R s) (ℓ := level s) hn hph hcr
      have hgoodt : ∀ h hL', LevelInvariant (goodModel c s h hL') (phaseK c.R s) (phaseB c.R s) c.R
          (SplitBrox.update (phaseK c.R s) (level s) s.inner (.inr v)) := fun h hL' =>
        level_invariant_local (goodModel c s h hL') (hr.good h hL').1 hn hbpos g cut j prev v hph
          hv' hvr hmin (fun hc' => absurd hc' hcr)
      rw [ht] at hrank hgoodt
      simp only [ht]
      rw [ite_eq_right (show ¬ s.inner.completed < s.inner.completed by omega)]
      by_cases hcap : 4 * phaseK c.R s ≤ s.calls + 1
      · rw [ite_eq_left hcap]
        have hl : level s < c.f c.xs := by
          refine level_lt_of_cap c (fun h hL' => ⟨hgoodt h hL', ?_⟩) hL hR hn hcap
          have := (hr.good h hL').2
          dsimp only
          omega
        exact lower_transition c hv hp hc hgap (le_of_lt hcl) hl rfl rfl rfl rfl rfl rfl
      · rw [ite_eq_right hcap]
        simp only [Inv, hst]
        refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hp.R_pos, hp.Lh_eq, hp.Lh_le, hp.shrink⟩, ?_, ?_⟩
        · unfold Count gap at *; dsimp only at *; push_cast; linarith
        · refine ⟨hr.gap_gt, hn, by show s.calls + 1 < 4 * phaseK c.R s; omega,
            ⟨hr.feasible.momentum_mem, hr.feasible.primal_mem, hv'⟩, ⟨hzpt, hzval, hzg⟩, ?_⟩
          intro h hL'
          refine ⟨hgoodt h hL', ?_⟩
          have := (hr.good h hL').2
          dsimp only
          omega

end OracleTemplate.CertifiedLevelBrox
