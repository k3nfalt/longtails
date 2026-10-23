import LongTails.Proofs.QuadraticPerceptronPhases

namespace LongTails.Proofs.QuadraticPerceptronCone

namespace Gains

variable {g : Gains}

section Potential

variable (hg : g.Standing) {x0 : State} {N : ℕ} {U0 : ℝ}
  (ha0 : 0 < x0.a) (hZ0 : 0 < x0.Z)
  (hN : x0.B ^ 2 ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2)

include hg in
lemma cm_mul_le_one : g.c2 * g.cm ≤ 1 := by
  have := hg.cm_pos
  have := hg.c2_pos
  nlinarith [cm_le_c2 (g := g), hg.c2_le]

include hg ha0 hZ0 hN in
lemma potential_step_le {x : State} (I : g.Inv x0 N U0 x) (hn : N ≤ x.n) :
    g.potential (g.step x) ≤ g.potential x := by
  have hc1 := hg.c1_pos
  have hc2 := hg.c2_pos
  have hcm := hg.cm_pos
  have he := hg.e_pos
  by_cases hs : g.Stopped x
  · rw [step_stopped hs]
  rcases not_stopped_cases hs with h1 | ⟨h1, h2⟩
  · rw [step_opt1 h1]
    have hab := I.opt1_le hg ha0 hZ0 h1
    have : g.c2 * g.cm * (g.c1 * (x.a - x.b)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos hc1.le (by linarith))
    simp only [potential, opt1]
    nlinarith
  · rw [step_opt2 h1 h2]
    have hw := I.window hg ha0 hZ0 hN hn h1 h2
    have ha := I.a_pos hg ha0 hZ0
    have hb := I.b_nonneg
    have : 0 ≤ g.c2 * g.cm * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) :=
      mul_nonneg (by positivity) (by linarith)
    simp only [potential, opt2]
    nlinarith [sq_nonneg g.e]

include hg ha0 hZ0 hN in
lemma potential_drift {x : State} (I : g.Inv x0 N U0 x) (hn : N ≤ x.n)
    (h : g.IsOpt2 x) : g.potential (g.step x) ≤ g.potential x - g.e ^ 2 * (x.a + x.b) := by
  have hc2 := hg.c2_pos
  have hcm := hg.cm_pos
  rw [step_opt2 h.1 h.2]
  have hw := I.window hg ha0 hZ0 hN hn h.1 h.2
  have : 0 ≤ g.c2 * g.cm * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) :=
    mul_nonneg (by positivity) (by linarith)
  simp only [potential, opt2]
  nlinarith

include hg ha0 hZ0 hN in
lemma potential_two {x : State} (I : g.Inv x0 N U0 x) (hn : N ≤ x.n)
    (hs : ¬ g.Stopped x) (hs1 : ¬ g.Stopped (g.step x)) (hP : 0 ≤ g.potential x) :
    g.potential (g.step (g.step x)) ≤ (1 - g.cm ^ 2) * g.potential x := by
  have hc1 := hg.c1_pos
  have hc2 := hg.c2_pos
  have hcm := hg.cm_pos
  have he := hg.e_pos
  have hcm1 := cm_le_c1 (g := g)
  have hcm2 := cm_le_c2 (g := g)
  have ha := I.a_pos hg ha0 hZ0
  have hb := I.b_nonneg
  have hZ := I.Z_pos hZ0
  have I1 := I.step hg ha0 hZ0 hN
  have hn1 : N ≤ (g.step x).n := hn.trans (n_step x)
  have hstep2 := potential_step_le hg ha0 hZ0 hN I1 hn1
  have hPsum : g.potential x ≤ g.c2 * g.cm * (x.a + x.b) := by
    unfold potential; nlinarith
  rcases not_stopped_cases hs with h1 | ⟨h1, h2⟩
  · have hab := I.opt1_le hg ha0 hZ0 h1
    have hx1 : g.step x = g.opt1 x := step_opt1 h1
    rcases not_stopped_cases hs1 with h1' | ⟨h1', h2'⟩
    · rw [hx1] at h1'
      have hab' := (I1.opt1_le hg ha0 hZ0 (by rw [hx1]; exact h1'))
      simp only [hx1, opt1] at hab'
      have hP1 : g.potential (g.step x) = g.potential x + g.c2 * g.cm * (g.c1 * (x.a - x.b)) := by
        rw [hx1]; simp only [potential, opt1]; ring
      have hDelta : g.c1 * (x.a - x.b) ≤ -(g.c1 ^ 2 * (x.a + x.b)) := by nlinarith
      have k1 : g.c2 * g.cm * (g.c1 * (x.a - x.b)) ≤ -(g.c1 ^ 2 * (g.c2 * g.cm * (x.a + x.b))) := by
        have := mul_le_mul_of_nonneg_left hDelta (show 0 ≤ g.c2 * g.cm by positivity)
        nlinarith
      have k2 : g.cm ^ 2 * g.potential x ≤ g.c1 ^ 2 * (g.c2 * g.cm * (x.a + x.b)) := by
        have h' : g.cm ^ 2 ≤ g.c1 ^ 2 := by nlinarith
        calc g.cm ^ 2 * g.potential x ≤ g.c1 ^ 2 * g.potential x :=
              mul_le_mul_of_nonneg_right h' hP
          _ ≤ g.c1 ^ 2 * (g.c2 * g.cm * (x.a + x.b)) :=
              mul_le_mul_of_nonneg_left hPsum (by positivity)
      linarith
    · have hw := I1.window hg ha0 hZ0 hN hn1 h1' h2'
      rw [hx1] at hw
      simp only [opt1] at hw
      have hy : 0 ≤ (1 + g.c1) * x.a + (1 - g.c1) * x.b := by nlinarith [hg.c1_le]
      have hop2 : g.step (g.opt1 x) = g.opt2 (g.opt1 x) := by
        rw [← hx1]; exact step_opt2 h1' h2'
      have hP2 : g.potential (g.step (g.step x)) = g.potential x +
          g.c2 * g.cm * (g.c1 * (x.a - x.b)) -
          g.c2 * g.cm * (g.c2 * ((1 + g.c1) * x.a - (1 - g.c1) * x.b) - 2 * g.e * x.Z) -
          g.e ^ 2 * ((1 + g.c1) * x.a + (1 - g.c1) * x.b) := by
        rw [hx1, hop2]; simp only [potential, opt1, opt2]; ring
      obtain ⟨d1, hd1⟩ : ∃ d1, d1 = x.b - x.a := ⟨_, rfl⟩
      obtain ⟨D2, hD2⟩ : ∃ D2,
          D2 = g.c2 * ((1 + g.c1) * x.a - (1 - g.c1) * x.b) - 2 * g.e * x.Z := ⟨_, rfl⟩
      have hd1n : 0 ≤ d1 := by rw [hd1]; linarith
      have hD2n : 0 ≤ D2 := by rw [hD2]; linarith
      have e3 : g.potential x ≤ g.c2 * d1 + D2 := by
        have := mul_le_mul_of_nonneg_left hcm1 (mul_nonneg hc2.le (by linarith : 0 ≤ x.a + x.b))
        unfold potential
        rw [hd1, hD2]
        linarith
      have e2 : g.cm * (g.c2 * d1 + D2) ≤ g.c2 * (g.c1 * d1 + D2) := by
        have := mul_le_mul_of_nonneg_right hcm1 (mul_nonneg hc2.le hd1n)
        have := mul_le_mul_of_nonneg_right hcm2 hD2n
        linarith
      have key : g.cm * g.potential x ≤ g.c2 * (g.c1 * d1 + D2) := by
        have := mul_le_mul_of_nonneg_left e3 hcm.le
        linarith
      have key2 := mul_le_mul_of_nonneg_left key hcm.le
      have hey := mul_nonneg (sq_nonneg g.e) hy
      rw [hP2]
      have : g.c2 * g.cm * (g.c1 * (x.a - x.b)) = -(g.c2 * g.cm * (g.c1 * d1)) := by
        rw [hd1]; ring
      have : g.c2 * g.cm * (g.c2 * ((1 + g.c1) * x.a - (1 - g.c1) * x.b) - 2 * g.e * x.Z) =
          g.c2 * g.cm * D2 := by rw [hD2]
      linarith
  · have hop : g.IsOpt2 x := ⟨h1, h2⟩
    have hw := I.window hg ha0 hZ0 hN hn h1 h2
    have hx1 : g.step x = g.opt2 x := step_opt2 h1 h2
    have hdrop := potential_drift hg ha0 hZ0 hN I hn hop
    rcases not_stopped_cases hs1 with h1' | ⟨h1', h2'⟩
    · have hab' := I1.opt1_le hg ha0 hZ0 h1'
      rw [hx1] at hab'
      simp only [opt2] at hab'
      have hstep1 : g.step (g.opt2 x) = g.opt1 (g.opt2 x) := by
        rw [← hx1]; exact step_opt1 h1'
      have hP2 : g.potential (g.step (g.step x)) = g.potential x -
          g.c2 * g.cm * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) - g.e ^ 2 * (x.a + x.b) -
          g.c2 * g.cm * (g.c1 * (g.c2 * (x.a + x.b) - (x.a - x.b))) := by
        rw [hx1, hstep1]; simp only [potential, opt1, opt2]; ring
      obtain ⟨D, hD⟩ : ∃ D, D = g.c2 * (x.a - x.b) - 2 * g.e * x.Z := ⟨_, rfl⟩
      obtain ⟨d', hd'⟩ : ∃ d', d' = g.c2 * (x.a + x.b) - (x.a - x.b) := ⟨_, rfl⟩
      have hDn : 0 ≤ D := by rw [hD]; linarith
      have hd'n : 0 ≤ d' := by rw [hd']; linarith
      have e3 : g.potential x ≤ D + g.c2 * d' := by
        have := mul_le_mul_of_nonneg_left hcm2 (mul_nonneg hc2.le (by linarith : 0 ≤ x.a + x.b))
        unfold potential
        rw [hD, hd']
        linarith
      have e2 : g.cm * (D + g.c2 * d') ≤ g.c2 * (D + g.c1 * d') := by
        have := mul_le_mul_of_nonneg_right hcm2 hDn
        have := mul_le_mul_of_nonneg_right hcm1 (mul_nonneg hc2.le hd'n)
        linarith
      have key : g.cm * g.potential x ≤ g.c2 * (D + g.c1 * d') := by
        have := mul_le_mul_of_nonneg_left e3 hcm.le
        linarith
      have key2 := mul_le_mul_of_nonneg_left key hcm.le
      have hey := mul_nonneg (sq_nonneg g.e) (show 0 ≤ x.a + x.b by linarith)
      rw [hP2, ← hD, ← hd']
      linarith
    · have hw1 := I1.window hg ha0 hZ0 hN hn1 h1' h2'
      rw [hx1] at hw1
      simp only [opt2] at hw1
      have hey := mul_nonneg (sq_nonneg g.e) (show 0 ≤ x.a + x.b by linarith)
      have hD : g.c2 ^ 2 * (x.a + x.b) ≤ g.c2 * (x.a - x.b) - 2 * g.e * x.Z := by linarith
      have hP1 : g.potential (g.opt2 x) ≤
          g.potential x - g.c2 * g.cm * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) := by
        simp only [potential, opt2]; linarith
      have k1 : g.c2 * g.cm * (g.c2 ^ 2 * (x.a + x.b)) ≤
          g.c2 * g.cm * (g.c2 * (x.a - x.b) - 2 * g.e * x.Z) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      have k2 : g.cm ^ 2 * g.potential x ≤ g.c2 ^ 2 * (g.c2 * g.cm * (x.a + x.b)) := by
        have h' : g.cm ^ 2 ≤ g.c2 ^ 2 := by nlinarith
        calc g.cm ^ 2 * g.potential x ≤ g.c2 ^ 2 * g.potential x :=
              mul_le_mul_of_nonneg_right h' hP
          _ ≤ g.c2 ^ 2 * (g.c2 * g.cm * (x.a + x.b)) :=
              mul_le_mul_of_nonneg_left hPsum (by positivity)
      rw [hx1] at hstep2 ⊢
      linarith

end Potential

end Gains

end LongTails.Proofs.QuadraticPerceptronCone
