import LongTails.Proofs.CertifiedLevelBroxStart

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma level_lt_of_cap (c : Ctx E) {s : State E} {t : SplitBrox.State E}
    (hgood : ∀ h : c.f c.xs ≤ level s, ∀ hL : 0 ≤ s.Lh,
      LevelInvariant (goodModel c s h hL) (phaseK c.R s) (phaseB c.R s) c.R t ∧
        s.calls + 1 ≤ rank t + t.completed)
    (hL : 0 ≤ s.Lh) (hR : 0 < c.R) (hn : t.completed < phaseK c.R s)
    (hcap : 4 * phaseK c.R s ≤ s.calls + 1) : level s < c.f c.xs := by
  by_contra hle
  have h := hgood (le_of_not_gt hle) hL
  have hr := level_incomplete_rank (goodModel c s (le_of_not_gt hle) hL) h.1
    (base_pos hR) (le_of_eq (base_sq _ _ _)) hn
  have := h.2
  omega

lemma Params.Lh_nonneg {c : Ctx E} {s : State E} (hp : Params c s) : 0 ≤ s.Lh := by
  rw [hp.Lh_eq]; have := c.ε_pos; positivity

lemma count_lower (c : Ctx E) {s : State E} {T : ℕ} (hc : Count c s T)
    (hg : 0 < gap s) (hcalls : s.calls ≤ 4 * phaseK c.R s) :
    ((T + 1 : ℕ) : ℝ) ≤ 200 * Real.sqrt (s.Lh * c.R ^ 2 / (gap s / 2)) +
      9 * (((s.phases + 1 : ℕ) : ℝ) + s.doublings) + 2 := by
  have hcost := run_cost c.R s.Lh (gap s)
  have hcr : (s.calls : ℝ) ≤ 4 * (phaseK c.R s : ℝ) := by exact_mod_cast hcalls
  rw [potential_halve hg]
  have h2 := sqrt_two_ge
  have hn := Real.sqrt_nonneg (s.Lh * c.R ^ 2 / gap s)
  unfold Count at hc
  unfold phaseK at hcr
  push_cast
  nlinarith

end OracleTemplate.CertifiedLevelBrox
