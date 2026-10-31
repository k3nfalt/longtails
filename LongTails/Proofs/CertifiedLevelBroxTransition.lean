import LongTails.Proofs.CertifiedLevelBroxRun

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma lower_transition (c : Ctx E) {s s' : State E} {T : ℕ} (hv : Values c s)
    (hp : Params c s) (hc : Count c s T) (hgap : 0 < gap s)
    (hcalls : s.calls ≤ 4 * phaseK c.R s) (hl : level s < c.f c.xs)
    (e_lb : s'.lb = level s) (e_ub : s'.ub = s.ub) (e_best : s'.best = s.best)
    (e_Lh : s'.Lh = s.Lh) (e_p : s'.phases = s.phases + 1) (e_d : s'.doublings = s.doublings) :
    Inv c (startPhase c.ε c.x0 s') (T + 1) := by
  have hg : gap s' = gap s / 2 := by simp only [gap, level] at *; rw [e_lb, e_ub]; ring
  apply inv_start c s' (T + 1)
  · exact ⟨by rw [e_lb]; exact le_of_lt hl, by rw [e_best]; exact hv.best_mem,
      by rw [e_ub, e_best]; exact hv.ub_eq⟩
  · intro _
    refine ⟨hp.R_pos, by rw [e_Lh, e_d]; exact hp.Lh_eq, by rw [e_Lh, e_d]; exact hp.Lh_le, ?_⟩
    rw [hg, e_p, pow_succ]
    have h := hp.shrink
    have hpos : 0 ≤ gap s * (4 / 3 : ℝ) ^ s.phases := by positivity
    nlinarith
  · intro _
    have h := count_lower c hc hgap hcalls
    rw [hg, e_Lh, e_p, e_d]
    exact h

lemma upper_transition (c : Ctx E) {s s' : State E} {T : ℕ} (hv : Values c s)
    (hp : Params c s) (hc : Count c s T)
    (hcalls : s.calls ≤ 4 * phaseK c.R s) (y : E) (hy : y ∈ c.C)
    (hval : c.f y ≤ level s + gap s / 4)
    (e_lb : s'.lb = s.lb) (e_ub : s'.ub = c.f y) (e_best : s'.best = y)
    (e_Lh : s'.Lh = s.Lh) (e_p : s'.phases = s.phases + 1) (e_d : s'.doublings = s.doublings) :
    Inv c (startPhase c.ε c.x0 s') (T + 1) := by
  have hle : gap s' ≤ 3 / 4 * gap s := by
    simp only [gap, level] at *; rw [e_lb, e_ub]; linarith
  apply inv_start c s' (T + 1)
  · exact ⟨by rw [e_lb]; exact hv.lb_le, by rw [e_best]; exact hy, by rw [e_ub, e_best]⟩
  · intro hε
    refine ⟨hp.R_pos, by rw [e_Lh, e_d]; exact hp.Lh_eq, by rw [e_Lh, e_d]; exact hp.Lh_le, ?_⟩
    rw [e_p, pow_succ]
    have h := hp.shrink
    have hpos : 0 ≤ (4 / 3 : ℝ) ^ s.phases := by positivity
    have hg' : 0 ≤ gap s' := le_trans (le_of_lt c.ε_pos) (le_of_lt hε)
    nlinarith [mul_le_mul_of_nonneg_right hle hpos]
  · intro hε
    have hg' : 0 < gap s' := lt_trans c.ε_pos hε
    have hL := hp.Lh_nonneg
    have hcost := run_cost c.R s.Lh (gap s)
    have hcr : (s.calls : ℝ) ≤ 4 * (phaseK c.R s : ℝ) := by exact_mod_cast hcalls
    have hs := potential_shrink (R := c.R) hL hg' hle
    have h3 := sqrt_four_thirds_ge
    have hn := Real.sqrt_nonneg (s.Lh * c.R ^ 2 / gap s)
    unfold Count at hc
    unfold phaseK at hcr
    rw [e_Lh, e_p, e_d]
    push_cast
    nlinarith

lemma double_transition (c : Ctx E) {s s' : State E} {T : ℕ} (hv : Values c s)
    (hp : Params c s) (hc : Count c s T)
    (hcalls : s.calls ≤ 4 * phaseK c.R s) (hLL : s.Lh ≤ c.L)
    (e_lb : s'.lb = s.lb) (e_ub : s'.ub = s.ub) (e_best : s'.best = s.best)
    (e_Lh : s'.Lh = 2 * s.Lh) (e_p : s'.phases = s.phases) (e_d : s'.doublings = s.doublings + 1) :
    Inv c (startPhase c.ε c.x0 s') (T + 1) := by
  have hg : gap s' = gap s := by simp only [gap] at *; rw [e_lb, e_ub]
  apply inv_start c s' (T + 1)
  · exact ⟨by rw [e_lb]; exact hv.lb_le, by rw [e_best]; exact hv.best_mem,
      by rw [e_ub, e_best]; exact hv.ub_eq⟩
  · intro _
    refine ⟨hp.R_pos, ?_, Or.inr (by rw [e_Lh]; linarith), ?_⟩
    · rw [e_Lh, e_d, hp.Lh_eq, pow_succ]; ring
    · rw [hg, e_p]; exact hp.shrink
  · intro _
    have hL := hp.Lh_nonneg
    have hcost := run_cost c.R s.Lh (gap s)
    have hcr : (s.calls : ℝ) ≤ 4 * (phaseK c.R s : ℝ) := by exact_mod_cast hcalls
    have h2 := sqrt_two_ge
    have hn := Real.sqrt_nonneg (s.Lh * c.R ^ 2 / gap s)
    unfold Count at hc
    unfold phaseK at hcr
    rw [hg, e_Lh, e_p, e_d, show 2 * s.Lh * c.R ^ 2 / gap s = 2 * (s.Lh * c.R ^ 2 / gap s) by ring,
      Real.sqrt_mul (by norm_num)]
    push_cast
    nlinarith

end OracleTemplate.CertifiedLevelBrox
