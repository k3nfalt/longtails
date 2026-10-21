import LongTails.Proofs.CertifiedLevelBroxCheckStep
import LongTails.Proofs.CertifiedLevelBroxBudget
import LongTails.Proofs.Execution

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.CertifiedLevelBrox

open OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inv_step (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    {s : State E} {T : ℕ} (hs : Inv c s T) (k : ℕ) (seed : O.Seed k) :
    Inv c (update c.R c.ε c.x0 s (O.answer k (0, query c.R c.x0 s) seed)) (T + 1) := by
  cases hst : s.stage with
  | init0 => exact inv_init0 c hO hst hs k seed
  | init1 => exact inv_init1 c hO hst hs k seed
  | run => exact inv_run c hO hst hs k seed
  | check => exact inv_check c hO hst hs k seed
  | frozen => exact inv_frozen c hst hs k seed

lemma inv_iterate (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    let F := fun sc : State E × ℕ =>
      (update c.R c.ε c.x0 sc.1 (O.answer sc.2 (0, query c.R c.x0 sc.1) (ξ sc.2)), sc.2 + 1)
    Inv c (F^[n] ((algorithm c.R c.ε c.x0).initial (), 0)).1 n ∧
      (F^[n] ((algorithm c.R c.ε c.x0).initial (), 0)).2 = n := by
  intro F
  induction n with
  | zero => exact ⟨by simp only [Function.iterate_zero, id]; exact ⟨rfl, rfl⟩, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hi, hn⟩ := ih
    refine ⟨?_, by simp [F, hn]⟩
    have h := inv_step c hO hi (F^[n] ((algorithm c.R c.ε c.x0).initial (), 0)).2
      (ξ (F^[n] ((algorithm c.R c.ε c.x0).initial (), 0)).2)
    simpa [F, hn] using h

lemma execute_accuracy (c : Ctx E) {O : Oracle (Query E) (Reply E)} (hO : Valid c O)
    (B : ℕ) (hB : 400 * Real.sqrt (c.L * c.R ^ 2 / c.ε) +
      40 * Real.logb 2 (2 + (c.Δ + c.L * c.R ^ 2) / c.ε) + 300 ≤ B)
    (seed : (algorithm c.R c.ε c.x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    let y := execute O (algorithm c.R c.ε c.x0) (fun _ => B) seed ξ
    y ∈ c.C ∧ c.f y - c.f c.xs ≤ c.ε := by
  intro y
  have hy : y = (algorithm c.R c.ε c.x0).output ((fun sc : State E × ℕ =>
      ((algorithm c.R c.ε c.x0).update sc.1
        (O.answer sc.2 ((algorithm c.R c.ε c.x0).query sc.1) (ξ sc.2)), sc.2 + 1))^[B]
      ((algorithm c.R c.ε c.x0).initial seed, 0)).1 := execute_indexed O _ B seed ξ
  have hi := (inv_iterate c hO ξ B).1
  rw [hy]
  generalize hS : ((fun sc : State E × ℕ =>
      (update c.R c.ε c.x0 sc.1 (O.answer sc.2 (0, query c.R c.x0 sc.1) (ξ sc.2)), sc.2 + 1))^[B]
      ((algorithm c.R c.ε c.x0).initial (), 0)).1 = S at hi
  have hS' : ((fun sc : State E × ℕ =>
      ((algorithm c.R c.ε c.x0).update sc.1
        (O.answer sc.2 ((algorithm c.R c.ε c.x0).query sc.1) (ξ sc.2)), sc.2 + 1))^[B]
      ((algorithm c.R c.ε c.x0).initial seed, 0)).1 = S := hS
  rw [hS']
  have hB0 : (300 : ℝ) ≤ B := by
    have h1 := Real.sqrt_nonneg (c.L * c.R ^ 2 / c.ε)
    have hΔ : 0 ≤ c.Δ := le_trans (sub_nonneg.mpr (c.xs_min c.x0 c.x0_mem)) c.gap0
    have hY : 0 ≤ Real.logb 2 (2 + (c.Δ + c.L * c.R ^ 2) / c.ε) := by
      apply Real.logb_nonneg (by norm_num)
      have : 0 ≤ (c.Δ + c.L * c.R ^ 2) / c.ε := by
        have := c.ε_pos; have := c.L_nonneg; positivity
      linarith
    linarith
  cases hst : S.stage with
  | init0 =>
    simp only [Inv, hst] at hi
    have : (B : ℝ) = 0 := by exact_mod_cast hi.1
    linarith
  | init1 =>
    simp only [Inv, hst] at hi
    have : (B : ℝ) = 1 := by exact_mod_cast hi.1
    linarith
  | run =>
    simp only [Inv, hst] at hi
    have := running_bound c hi.2.1 hi.2.2.1 hi.2.2.2.gap_gt (le_of_lt hi.2.2.2.calls_lt)
    linarith
  | check =>
    simp only [Inv, hst] at hi
    have := running_bound c hi.2.1 hi.2.2.1 hi.2.2.2.gap_gt hi.2.2.2.calls_le
    linarith
  | frozen =>
    simp only [Inv, hst] at hi
    obtain ⟨hv, hg⟩ := hi
    refine ⟨hv.best_mem, ?_⟩
    change c.f S.best - c.f c.xs ≤ c.ε
    rw [← hv.ub_eq]
    unfold gap at hg
    linarith [hv.lb_le]

end OracleTemplate.CertifiedLevelBrox
