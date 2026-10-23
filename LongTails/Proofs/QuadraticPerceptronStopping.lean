import LongTails.Proofs.QuadraticPerceptronPotential

namespace LongTails.Proofs.QuadraticPerceptronCone

namespace Gains

variable {g : Gains}

section Stopping

variable (hg : g.Standing) {x0 : State} {N K J : ℕ} {U0 : ℝ}
  (ha0 : 0 < x0.a) (hb0 : 0 ≤ x0.b) (hZ0 : 0 < x0.Z) (hn0 : x0.n = 0)
  (hN : x0.B ^ 2 ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2)
  (hU : x0.a + x0.b + 2 * x0.Z ≤ U0)
  (hK : (1 + g.e) ^ N * U0 < min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K)

include hg ha0 hb0 hZ0 hn0 hN hU in
lemma potential_traj_le {t u : ℕ} (hle : t ≤ u) (hn : N ≤ (g.traj x0 t).n) :
    g.potential (g.traj x0 u) ≤ g.potential (g.traj x0 t) := by
  induction u, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ u htu ih =>
      have hnu : N ≤ (g.traj x0 u).n := hn.trans (n_mono x0 htu)
      rw [traj_succ]
      exact (potential_step_le hg ha0 hZ0 hN (inv_traj hg ha0 hb0 hZ0 hn0 hN hU u) hnu).trans ih

include hg ha0 hb0 hZ0 hn0 hN hU in
lemma opt1_exit (h12 : g.c1 ≤ g.c2) {u : ℕ} (hn : N ≤ (g.traj x0 u).n)
    (hP : g.potential (g.traj x0 u) < 0) (h1 : (g.traj x0 u).a ^ 2 ≤ (g.traj x0 u).b ^ 2)
    (h2 : ¬ (g.traj x0 (u + 1)).a ^ 2 ≤ (g.traj x0 (u + 1)).b ^ 2) :
    g.Stopped (g.traj x0 (u + 1)) := by
  refine ⟨h2, ?_⟩
  have I := inv_traj hg ha0 hb0 hZ0 hn0 hN hU u
  have I1 := inv_traj hg ha0 hb0 hZ0 hn0 hN hU (u + 1)
  have hx1 : g.traj x0 (u + 1) = g.opt1 (g.traj x0 u) := by rw [traj_succ, step_opt1 h1]
  have hn1 : N ≤ (g.traj x0 (u + 1)).n := hn.trans (n_mono x0 (Nat.le_succ u))
  have hph := I1.phase hg hN hn1
  set x := g.traj x0 u
  have hab := I.opt1_le hg ha0 hZ0 h1
  have ha := I.a_pos hg ha0 hZ0
  have hb := I.b_nonneg
  have hc1 := hg.c1_pos
  have hc2 := hg.c2_pos
  have hm := hg.m_nonneg
  have hcm : g.cm = g.c1 := min_eq_left h12
  rw [hx1] at hph ⊢
  simp only [test, opt1] at hph ⊢
  unfold potential at hP
  rw [hcm] at hP
  have hω : g.m * (x.B ^ 2 - x.A ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm (by linarith)
  have hs : 0 < (1 + g.c1) * x.a + (1 - g.c1) * x.b := by nlinarith [hg.c1_le]
  have hd : g.c2 * ((1 + g.c1) * x.a - (1 - g.c1) * x.b) - 2 * g.e * x.Z < 0 := by nlinarith
  have := mul_neg_of_pos_of_neg hs hd
  nlinarith

include hg ha0 hb0 hZ0 hn0 hN hU in
lemma opt2_keep (h21 : g.c2 ≤ g.c1) {u : ℕ} (hn : N ≤ (g.traj x0 u).n)
    (hP : g.potential (g.traj x0 u) < 0) (h : g.IsOpt2 (g.traj x0 u)) :
    ¬ (g.traj x0 (u + 1)).a ^ 2 ≤ (g.traj x0 (u + 1)).b ^ 2 := by
  have I := inv_traj hg ha0 hb0 hZ0 hn0 hN hU u
  have I1 := inv_traj hg ha0 hb0 hZ0 hn0 hN hU (u + 1)
  have hw := I.window hg ha0 hZ0 hN hn h.1 h.2
  have hx1 : g.traj x0 (u + 1) = g.opt2 (g.traj x0 u) := by rw [traj_succ, step_opt2 h.1 h.2]
  have hb1 := I1.b_nonneg
  set x := g.traj x0 u
  have hcm : g.cm = g.c2 := min_eq_right h21
  have hc2 := hg.c2_pos
  unfold potential at hP
  rw [hcm] at hP
  rw [hx1] at hb1 ⊢
  simp only [opt2] at hb1 ⊢
  have hgt : (1 + g.c2) * x.b + g.e * x.Z < (1 - g.c2) * x.a + g.e * x.Z := by
    have : 0 < g.c2 * ((1 - g.c2) * x.a - (1 + g.c2) * x.b) := by nlinarith
    have := (mul_pos_iff_of_pos_left hc2).mp this
    linarith
  intro hle
  nlinarith

include hg ha0 hb0 hZ0 hn0 hN hU hK in
lemma exit_stop {t : ℕ} (hn : N ≤ (g.traj x0 t).n) (hP : g.potential (g.traj x0 t) < 0) :
    g.Stopped (g.traj x0 (t + 2 * K + 2)) := by
  have hPu : ∀ u, t ≤ u → g.potential (g.traj x0 u) < 0 := fun u hu =>
    lt_of_le_of_lt (potential_traj_le hg ha0 hb0 hZ0 hn0 hN hU hu hn) hP
  have hnu : ∀ u, t ≤ u → N ≤ (g.traj x0 u).n := fun u hu => hn.trans (n_mono x0 hu)
  rcases le_total g.c1 g.c2 with h12 | h21
  · obtain ⟨j, hj, hno⟩ := no_run2 hg ha0 hb0 hZ0 hn0 hN hU hK t
    by_cases hs : g.Stopped (g.traj x0 (t + j))
    · exact stopped_mono hs (by omega)
    have h1 : (g.traj x0 (t + j)).a ^ 2 ≤ (g.traj x0 (t + j)).b ^ 2 := by
      rcases not_stopped_cases hs with h | h
      · exact h
      · exact absurd h hno
    set u := t + j
    have hex : ∃ i, ¬ (g.traj x0 (u + 1 + i)).a ^ 2 ≤ (g.traj x0 (u + 1 + i)).b ^ 2 := by
      obtain ⟨i, _, hi⟩ := no_run1 hg ha0 hb0 hZ0 hn0 hN hU hK (u + 1)
      exact ⟨i, hi⟩
    classical
    let i0 := Nat.find hex
    have hi0 : ¬ (g.traj x0 (u + 1 + i0)).a ^ 2 ≤ (g.traj x0 (u + 1 + i0)).b ^ 2 :=
      Nat.find_spec hex
    have hi0K : i0 ≤ K := by
      obtain ⟨i, hiK, hi⟩ := no_run1 hg ha0 hb0 hZ0 hn0 hN hU hK (u + 1)
      exact (Nat.find_min' hex hi).trans hiK
    have hw : (g.traj x0 (u + i0)).a ^ 2 ≤ (g.traj x0 (u + i0)).b ^ 2 := by
      rcases Nat.eq_zero_or_pos i0 with h0 | hpos
      · rw [h0, add_zero]; exact h1
      · have hmin := Nat.find_min hex (show i0 - 1 < i0 by omega)
        push Not at hmin
        rwa [show u + 1 + (i0 - 1) = u + i0 by omega] at hmin
    have hstop := opt1_exit hg ha0 hb0 hZ0 hn0 hN hU h12 (hnu _ (by omega)) (hPu _ (by omega)) hw
      (by rwa [show u + i0 + 1 = u + 1 + i0 by ring])
    exact stopped_mono hstop (by omega)
  · rcases exists_opt2 hg ha0 hb0 hZ0 hn0 hN hU hK t with hs | ⟨j, hj, hop⟩
    · exact stopped_mono hs (by omega)
    set u := t + j
    have hchain : ∀ i, g.Stopped (g.traj x0 (u + i)) ∨ g.IsOpt2 (g.traj x0 (u + i)) := by
      intro i
      induction i with
      | zero => right; simpa using hop
      | succ i ih =>
          rcases ih with hs | ho
          · left; rw [← add_assoc, traj_succ]; exact stopped_succ hs
          · have hk := opt2_keep hg ha0 hb0 hZ0 hn0 hN hU h21 (hnu _ (by omega))
              (hPu _ (by omega)) ho
            rw [← add_assoc]
            by_cases hs : g.Stopped (g.traj x0 (u + i + 1))
            · exact Or.inl hs
            · rcases not_stopped_cases hs with h | h
              · exact absurd h hk
              · exact Or.inr h
    obtain ⟨j', hj', hno⟩ := no_run2 hg ha0 hb0 hZ0 hn0 hN hU hK u
    rcases hchain j' with hs | ho
    · exact stopped_mono hs (by omega)
    · exact absurd ho hno

variable (hJ : (1 - g.cm ^ 2) ^ J * ((1 + g.e) ^ N * U0) ≤ g.e ^ 3 * x0.Z)

include hg ha0 hb0 hZ0 hn0 hN hU hK hJ in
theorem stops : g.Stopped (g.traj x0 (N * (K + 1) + 2 * J + 3 * K + 3)) := by
  have hU0 := U0_nonneg ha0 hb0 hZ0 hU
  have hcm := hg.cm_pos
  have hcm1 : g.cm ≤ 1 := (cm_le_c1 (g := g)).trans hg.c1_le
  have he := hg.e_pos
  rcases phase_one hg ha0 hb0 hZ0 hn0 hN hU hK N with hs | hn
  · exact stopped_mono hs (by nlinarith)
  set s := N * (K + 1)
  have hnu : ∀ u, s ≤ u → N ≤ (g.traj x0 u).n := fun u hu => hn.trans (n_mono x0 hu)
  have hS : 0 ≤ (1 + g.e) ^ N * U0 := mul_nonneg (pow_nonneg (by linarith) N) hU0
  have hq : 0 ≤ 1 - g.cm ^ 2 := by nlinarith
  have iter : ∀ j, g.Stopped (g.traj x0 (s + 2 * j)) ∨
      g.potential (g.traj x0 (s + 2 * j)) ≤
        (1 - g.cm ^ 2) ^ j * max (g.potential (g.traj x0 s)) 0 := by
    intro j
    induction j with
    | zero => right; simp
    | succ j ih =>
        have hidx : s + 2 * (j + 1) = s + 2 * j + 1 + 1 := by ring
        rcases ih with hs | hp
        · left; exact stopped_mono hs (by omega)
        by_cases hs0 : g.Stopped (g.traj x0 (s + 2 * j))
        · left; exact stopped_mono hs0 (by omega)
        by_cases hs1 : g.Stopped (g.traj x0 (s + 2 * j + 1))
        · left; exact stopped_mono hs1 (by omega)
        right
        have hR : 0 ≤ (1 - g.cm ^ 2) ^ j * max (g.potential (g.traj x0 s)) 0 :=
          mul_nonneg (pow_nonneg hq j) (le_max_right _ _)
        rw [hidx, traj_succ, traj_succ]
        rw [traj_succ] at hs1
        by_cases hP : 0 ≤ g.potential (g.traj x0 (s + 2 * j))
        · have h2 := potential_two hg ha0 hZ0 hN (inv_traj hg ha0 hb0 hZ0 hn0 hN hU _)
            (hnu _ (by omega)) hs0 hs1 hP
          rw [pow_succ]
          nlinarith
        · push Not at hP
          have I1 := (inv_traj hg ha0 hb0 hZ0 hn0 hN hU (s + 2 * j)).step hg ha0 hZ0 hN
          have h1 := potential_step_le hg ha0 hZ0 hN
            (inv_traj hg ha0 hb0 hZ0 hn0 hN hU (s + 2 * j)) (hnu (s + 2 * j) (by omega))
          have h2 := potential_step_le hg ha0 hZ0 hN I1 ((hnu _ (le_add_right le_rfl)).trans
            (n_step _))
          have : 0 ≤ (1 - g.cm ^ 2) ^ (j + 1) * max (g.potential (g.traj x0 s)) 0 :=
            mul_nonneg (pow_nonneg hq _) (le_max_right _ _)
          linarith
  have hPs : max (g.potential (g.traj x0 s)) 0 ≤ (1 + g.e) ^ N * U0 := by
    refine max_le ?_ hS
    have I := inv_traj hg ha0 hb0 hZ0 hn0 hN hU s
    have hsum := I.sum_le hg hZ0 hU0
    have hc := cm_mul_le_one hg
    have hpos : 0 ≤ (g.traj x0 s).a + (g.traj x0 s).b := by
      linarith [I.a_pos hg ha0 hZ0, I.b_nonneg]
    have hZ := I.Z_pos hZ0
    unfold potential
    nlinarith
  rcases iter J with hs | hp
  · exact stopped_mono hs (by omega)
  set v := s + 2 * J
  have hPv : g.potential (g.traj x0 v) ≤ g.e ^ 3 * x0.Z := by
    have := mul_le_mul_of_nonneg_left hPs (pow_nonneg hq J)
    linarith
  rcases exists_opt2 hg ha0 hb0 hZ0 hn0 hN hU hK v with hs | ⟨j, hj, hop⟩
  · exact stopped_mono hs (by omega)
  set w := v + j
  have Iw := inv_traj hg ha0 hb0 hZ0 hn0 hN hU w
  have hPw : g.potential (g.traj x0 w) ≤ g.e ^ 3 * x0.Z :=
    (potential_traj_le hg ha0 hb0 hZ0 hn0 hN hU (show v ≤ w by omega) (hnu _ (by omega))).trans hPv
  have hdrop := potential_drift hg ha0 hZ0 hN Iw (hnu _ (by omega)) hop
  have hneg : g.potential (g.traj x0 (w + 1)) < 0 := by
    rw [traj_succ]
    by_cases hP : 0 ≤ g.potential (g.traj x0 w)
    · have hc := cm_mul_le_one hg
      have hZw := Iw.Z_ge
      have hsum : 2 * g.e * x0.Z ≤ (g.traj x0 w).a + (g.traj x0 w).b := by
        unfold potential at hP
        have hpos : 0 ≤ (g.traj x0 w).a + (g.traj x0 w).b := by
          linarith [Iw.a_pos hg ha0 hZ0, Iw.b_nonneg]
        nlinarith
      have : 2 * g.e ^ 3 * x0.Z ≤ g.e ^ 2 * ((g.traj x0 w).a + (g.traj x0 w).b) := by
        have := mul_le_mul_of_nonneg_left hsum (sq_nonneg g.e)
        nlinarith
      nlinarith [pow_pos he 3, hZ0]
    · push Not at hP
      nlinarith [sq_nonneg g.e, Iw.a_pos hg ha0 hZ0, Iw.b_nonneg]
  have hfin := exit_stop hg ha0 hb0 hZ0 hn0 hN hU hK (hnu _ (by omega)) hneg
  exact stopped_mono hfin (by omega)

end Stopping

end Gains

end LongTails.Proofs.QuadraticPerceptronCone
