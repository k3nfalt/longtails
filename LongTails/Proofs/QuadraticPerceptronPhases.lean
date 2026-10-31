import LongTails.Proofs.QuadraticPerceptronCone

namespace LongTails.Proofs.QuadraticPerceptronCone

namespace Gains

variable {g : Gains}

def IsOpt2 (g : Gains) (x : State) : Prop := ¬ x.a ^ 2 ≤ x.b ^ 2 ∧ 0 ≤ g.test x

lemma Standing.cm_pos (hg : g.Standing) : 0 < g.cm := lt_min hg.c1_pos hg.c2_pos

lemma cm_le_c1 : g.cm ≤ g.c1 := min_le_left _ _

lemma cm_le_c2 : g.cm ≤ g.c2 := min_le_right _ _

lemma n_step (x : State) : x.n ≤ (g.step x).n := by
  unfold step
  split_ifs <;> simp [opt1, opt2]

lemma n_mono (x : State) {t u : ℕ} (h : t ≤ u) : (g.traj x t).n ≤ (g.traj x u).n := by
  induction u, h using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih => rw [traj_succ]; exact ih.trans (n_step _)

lemma opt1_run (x : State) (L : ℕ) (h : ∀ j < L, (g.traj x j).a ^ 2 ≤ (g.traj x j).b ^ 2) :
    (g.traj x L).a = (1 + g.c1) ^ L * x.a ∧ (g.traj x L).b = (1 - g.c1) ^ L * x.b ∧
      (g.traj x L).Z = x.Z := by
  induction L with
  | zero => simp [traj_zero]
  | succ L ih =>
      obtain ⟨ha, hb, hZ⟩ := ih (fun j hj => h j (by omega))
      rw [traj_succ, step_opt1 (h L (by omega))]
      simp only [opt1, ha, hb, hZ, pow_succ]
      exact ⟨by ring, by ring, by simp⟩

section Trajectory

variable (hg : g.Standing) {x0 : State} {N K J : ℕ} {U0 : ℝ}
  (ha0 : 0 < x0.a) (hb0 : 0 ≤ x0.b) (hZ0 : 0 < x0.Z) (hn0 : x0.n = 0)
  (hN : x0.B ^ 2 ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2)
  (hU : x0.a + x0.b + 2 * x0.Z ≤ U0)

include hg hb0 hZ0 hn0 hU in
lemma inv_start : g.Inv x0 N U0 x0 := by
  have he := hg.e_pos
  refine ⟨hb0, le_rfl, min_le_left _ _, ?_, ?_, ?_, ?_⟩
  · rw [hn0]; simp
  · rw [hn0]; simp
  · intro _; rw [hn0]; simpa using hU
  · intro h
    rw [hn0] at h
    obtain rfl : N = 0 := by omega
    rw [pow_zero, one_mul]
    linarith

include hg ha0 hb0 hZ0 hn0 hN hU in
lemma inv_traj (t : ℕ) : g.Inv x0 N U0 (g.traj x0 t) := by
  induction t with
  | zero => exact inv_start hg hb0 hZ0 hn0 hU
  | succ t ih => rw [traj_succ]; exact ih.step hg ha0 hZ0 hN

include ha0 hb0 hZ0 hU in
lemma U0_nonneg : 0 ≤ U0 := by linarith

variable (hK : (1 + g.e) ^ N * U0 < min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K)

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma no_run1 (t : ℕ) : ∃ j ≤ K, ¬ (g.traj x0 (t + j)).a ^ 2 ≤ (g.traj x0 (t + j)).b ^ 2 := by
  by_contra hc
  push Not at hc
  set y := g.traj x0 t
  have hrun := opt1_run y K (fun j hj => by rw [← traj_add]; exact hc j hj.le)
  have hI := inv_traj hg ha0 hb0 hZ0 hn0 hN hU t
  have hK' := inv_traj hg ha0 hb0 hZ0 hn0 hN hU (t + K)
  have hlast := hc K le_rfl
  rw [traj_add] at hlast hK'
  have hle := hK'.opt1_le hg ha0 hZ0 hlast
  rw [hrun.1, hrun.2.1] at hle
  have hs := hI.sum_le hg hZ0 (U0_nonneg ha0 hb0 hZ0 hU)
  have hc1 := hg.c1_pos
  have hc1' := hg.c1_le
  have hcm := hg.cm_pos
  have hpow1 : (1 + g.cm) ^ K ≤ (1 + g.c1) ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith [cm_le_c1 (g := g)]) K
  have hpow2 : (1 - g.c1) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hα := alpha_pos hg ha0 hZ0
  have ha := hI.a_ge
  have hb := hI.b_nonneg
  have h1 : min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K ≤ (1 + g.c1) ^ K * y.a := by
    rw [mul_comm]
    exact mul_le_mul hpow1 ha hα.le (by positivity)
  have h2 : (1 - g.c1) ^ K * y.b ≤ y.b := by nlinarith
  linarith

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma no_run2 (t : ℕ) : ∃ j ≤ K + 1, ¬ g.IsOpt2 (g.traj x0 (t + j)) := by
  by_contra hc
  push Not at hc
  have hc2 := hg.c2_pos
  have he := hg.e_pos
  have hcm := hg.cm_pos
  have hgrow : ∀ j ≤ K, (1 + g.c2) ^ j * (g.e * x0.Z) ≤ (g.traj x0 (t + j + 1)).b := by
    intro j hj
    induction j with
    | zero =>
        have hI := inv_traj hg ha0 hb0 hZ0 hn0 hN hU t
        have hop := hc 0 (by omega)
        simp only [add_zero] at hop ⊢
        rw [traj_succ, step_opt2 hop.1 hop.2]
        simp only [opt2, pow_zero, one_mul]
        nlinarith [hI.b_nonneg, hI.Z_ge]
    | succ j ih =>
        have hI := inv_traj hg ha0 hb0 hZ0 hn0 hN hU (t + j + 1)
        have hop := hc (j + 1) (by omega)
        have ih' := ih (by omega)
        rw [show t + (j + 1) + 1 = t + j + 1 + 1 by ring, traj_succ,
          step_opt2 (by simpa [add_assoc] using hop.1) (by simpa [add_assoc] using hop.2)]
        simp only [opt2, pow_succ]
        have hZ := hI.Z_pos hZ0
        nlinarith
  have hlast := hc (K + 1) le_rfl
  have hI := inv_traj hg ha0 hb0 hZ0 hn0 hN hU (t + (K + 1))
  have hgt := hI.opt2_gt hg ha0 hZ0 hlast.1
  have hs := hI.sum_le hg hZ0 (U0_nonneg ha0 hb0 hZ0 hU)
  have hb := hgrow K le_rfl
  rw [show t + K + 1 = t + (K + 1) by ring] at hb
  have hpow : (1 + g.cm) ^ K ≤ (1 + g.c2) ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith [cm_le_c2 (g := g)]) K
  have hα : min x0.a (g.e * x0.Z) ≤ g.e * x0.Z := min_le_right _ _
  have hα0 := alpha_pos hg ha0 hZ0
  have : min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K ≤ (1 + g.c2) ^ K * (g.e * x0.Z) := by
    rw [mul_comm]; exact mul_le_mul hpow hα hα0.le (by positivity)
  linarith [hI.b_nonneg]

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma exists_opt2 (t : ℕ) :
    g.Stopped (g.traj x0 (t + K)) ∨ ∃ j ≤ K, g.IsOpt2 (g.traj x0 (t + j)) := by
  obtain ⟨j, hj, h1⟩ := no_run1 hg ha0 hb0 hZ0 hn0 hN hU hK t
  by_cases hs : g.Stopped (g.traj x0 (t + j))
  · exact Or.inl (stopped_mono hs (by omega))
  · rcases not_stopped_cases hs with h | h
    · exact absurd h h1
    · exact Or.inr ⟨j, hj, h⟩

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma window (t : ℕ) :
    g.Stopped (g.traj x0 (t + K + 1)) ∨ (g.traj x0 t).n + 1 ≤ (g.traj x0 (t + K + 1)).n := by
  rcases exists_opt2 hg ha0 hb0 hZ0 hn0 hN hU hK t with hs | ⟨j, hj, hop⟩
  · exact Or.inl (stopped_mono hs (by omega))
  · right
    have h1 : (g.traj x0 (t + j + 1)).n = (g.traj x0 (t + j)).n + 1 := by
      rw [traj_succ, step_opt2 hop.1 hop.2]; rfl
    have h2 := n_mono (g := g) x0 (show t ≤ t + j by omega)
    have h3 := n_mono (g := g) x0 (show t + j + 1 ≤ t + K + 1 by omega)
    omega

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma phase_one (i : ℕ) :
    g.Stopped (g.traj x0 (i * (K + 1))) ∨ i ≤ (g.traj x0 (i * (K + 1))).n := by
  induction i with
  | zero => right; simp
  | succ i ih =>
      have hidx : (i + 1) * (K + 1) = i * (K + 1) + K + 1 := by ring
      rcases ih with hs | hi
      · left; exact stopped_mono hs (by nlinarith)
      · rcases window hg ha0 hb0 hZ0 hn0 hN hU hK (i * (K + 1)) with hs | hn
        · left; rw [hidx]; exact hs
        · right; rw [hidx]; omega

end Trajectory

end Gains

end LongTails.Proofs.QuadraticPerceptronCone
