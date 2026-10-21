import LongTails.Proofs.CertifiedLevelBroxInvariant

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sqrt_two_ge : (1.414 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma sqrt_forty_le : Real.sqrt 40 ≤ 6.33 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma sqrt_four_thirds_ge : (1.154 : ℝ) ≤ Real.sqrt (4 / 3) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma run_cost (R Lh g : ℝ) :
    4 * (horizon R Lh g : ℝ) + 1 ≤ 25.32 * Real.sqrt (Lh * R ^ 2 / g) + 9 := by
  have h := horizon_le R Lh g
  have he : 40 * Lh * R ^ 2 / g = 40 * (Lh * R ^ 2 / g) := by ring
  rw [he, Real.sqrt_mul (by norm_num)] at h
  have hs := sqrt_forty_le
  have hn := Real.sqrt_nonneg (Lh * R ^ 2 / g)
  nlinarith

lemma potential_halve {Lh R g : ℝ} (hg : 0 < g) :
    Real.sqrt (Lh * R ^ 2 / (g / 2)) = Real.sqrt 2 * Real.sqrt (Lh * R ^ 2 / g) := by
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1
  field_simp

lemma potential_double {Lh R g : ℝ} :
    Real.sqrt (2 * Lh * R ^ 2 / g) = Real.sqrt 2 * Real.sqrt (Lh * R ^ 2 / g) := by
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1
  ring

lemma potential_shrink {Lh R g g' : ℝ} (hL : 0 ≤ Lh) (hg' : 0 < g') (hle : g' ≤ 3 / 4 * g) :
    Real.sqrt (4 / 3) * Real.sqrt (Lh * R ^ 2 / g) ≤ Real.sqrt (Lh * R ^ 2 / g') := by
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have hg : 0 < g := by linarith
  rw [show 4 / 3 * (Lh * R ^ 2 / g) = Lh * R ^ 2 / (3 / 4 * g) by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) hg' hle

lemma inv_start (c : Ctx E) (s : State E) (T : ℕ) (hv : Values c s)
    (hp : c.ε < gap s → Params c s)
    (hc : c.ε < gap s → (T : ℝ) ≤ 200 * Real.sqrt (s.Lh * c.R ^ 2 / gap s) +
      9 * ((s.phases : ℝ) + s.doublings) + 2) :
    Inv c (startPhase c.ε c.x0 s) T := by
  by_cases h : gap s ≤ c.ε
  · simp only [startPhase, ite_eq_left h, Inv]
    exact ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, h⟩
  · have hlt : c.ε < gap s := lt_of_not_ge h
    have hP := hp hlt
    simp only [startPhase, ite_eq_right h, Inv]
    refine ⟨⟨hv.lb_le, hv.best_mem, hv.ub_eq⟩, ⟨hP.R_pos, hP.Lh_eq, hP.Lh_le, hP.shrink⟩, ?_, ?_⟩
    · have hh := hc hlt
      simp only [Count, gap] at hh ⊢
      simpa using hh
    · refine ⟨hlt, ?_, ?_, ?_, trivial, ?_⟩
      · show 0 < phaseK c.R s
        exact horizon_pos _ _ _
      · show 0 < 4 * phaseK c.R s
        have := horizon_pos c.R s.Lh (gap s)
        unfold phaseK; omega
      · exact ⟨c.x0_mem, c.x0_mem, trivial⟩
      · intro hl hL
        refine ⟨level_invariant_initial _ _ _ _ c.x0 c.x0_mem ?_, by simp⟩
        exact pow_le_pow_left₀ (norm_nonneg _) c.dist 2

end OracleTemplate.CertifiedLevelBrox
