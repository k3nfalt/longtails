import LongTails.Proofs.BacktrackingCompositeRun

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

open CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def δc (Ls : ℝ) : ℝ := 1 / (4 * Real.sqrt (32 * Ls))

noncomputable def ρc (L1 R : ℝ) : ℝ := 1 / (12 + 400 * L1 * R)

lemma δc_pos {Ls : ℝ} (hLs : 0 < Ls) : 0 < δc Ls := by
  unfold δc
  have : 0 < Real.sqrt (32 * Ls) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma δc_sq {Ls : ℝ} (hLs : 0 < Ls) : δc Ls ^ 2 * (512 * Ls) = 1 := by
  unfold δc
  have hq : Real.sqrt (32 * Ls) ^ 2 = 32 * Ls := Real.sq_sqrt (by positivity)
  rw [div_pow, one_pow, mul_pow, hq]
  field_simp
  ring

lemma ρc_pos {L1 R : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) : 0 < ρc L1 R := by
  unfold ρc; positivity

lemma ρc_le {L1 R : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) : ρc L1 R ≤ 1 / 3 := by
  unfold ρc
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg hL1 hR.le]

lemma gfun_branch {Ls L1 R A : ℝ} (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) :
    1 / (32 * Ls) ≤ gfun Ls L1 R A / 2 ∨ 16 * ρc L1 R ^ 2 * A ≤ gfun Ls L1 R A / 2 := by
  have hLR : 0 ≤ L1 * R := by positivity
  have hρ : ρc L1 R = 1 / (12 + 400 * L1 * R) := rfl
  have e16 : 16 * (1 / (12 + 400 * L1 * R)) ^ 2 * A = 16 * A / (12 + 400 * L1 * R) ^ 2 := by
    field_simp
  rcases le_total (A / (4 * (1 + 32 * L1 * R) ^ 2)) (A / (8 * Ls * A + 96 * L1 ^ 2 * R ^ 2))
    with h | h
  · right
    unfold gfun
    rw [min_eq_right h, hρ, div_div, e16, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (L1 * R), mul_nonneg hA.le hLR, mul_nonneg hA.le (sq_nonneg (L1 * R))]
  · unfold gfun
    rw [min_eq_left h]
    by_cases hbig : 96 * L1 ^ 2 * R ^ 2 ≤ 8 * Ls * A
    · left
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hLs hA]
    · right
      push Not at hbig
      rw [hρ, div_div, e16, div_le_div_iff₀ (by positivity) (by positivity)]
      have hb2 := mul_lt_mul_of_pos_left hbig hA
      nlinarith [sq_nonneg (L1 * R), mul_nonneg hA.le hLR, mul_nonneg hA.le (sq_nonneg (L1 * R)),
        hb2, mul_nonneg hA.le (mul_nonneg (sq_nonneg L1) (sq_nonneg R))]

lemma good_growth {Ls L1 R A h : ℝ} (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A)
    (hh : 0 < h) (hq : gfun Ls L1 R A / 2 ≤ h) :
    Real.sqrt A + δc Ls ≤ Real.sqrt (A + stepWeight h A) ∨
      (1 + ρc L1 R) * Real.sqrt A ≤ Real.sqrt (A + stepWeight h A) := by
  have hρ := ρc_pos hL1 hR
  have hρ3 := ρc_le hL1 hR
  have hδ := δc_pos hLs
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  rcases le_or_gt h A with hle | hlt
  · have hgrow := sqrt_growth_small hh hA hle
    have hsh : Real.sqrt (gfun Ls L1 R A / 2) ≤ Real.sqrt h := Real.sqrt_le_sqrt hq
    rcases gfun_branch hLs hL1 hR hA with hb | hb
    · left
      have h1 : 4 * δc Ls ≤ Real.sqrt (gfun Ls L1 R A / 2) := by
        apply Real.le_sqrt_of_sq_le
        have := δc_sq hLs
        have hsq : δc Ls ^ 2 = 1 / (512 * Ls) := by
          rw [eq_div_iff (by positivity)]; linarith
        have e : (4 * δc Ls) ^ 2 = 1 / (32 * Ls) := by
          rw [mul_pow, hsq]; field_simp; ring
        rw [e]; exact hb
      linarith
    · right
      have h1 : 4 * ρc L1 R * Real.sqrt A ≤ Real.sqrt (gfun Ls L1 R A / 2) := by
        apply Real.le_sqrt_of_sq_le
        have e : (4 * ρc L1 R * Real.sqrt A) ^ 2 = 16 * ρc L1 R ^ 2 * A := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hA.le]; ring
        rw [e]; exact hb
      linarith
  · right
    have h2 := growth_large hh hA hlt
    have hs2 : Real.sqrt (2 * A) ≤ Real.sqrt (A + stepWeight h A) := Real.sqrt_le_sqrt h2
    have hs3 : (1 + ρc L1 R) * Real.sqrt A ≤ Real.sqrt (2 * A) := by
      rw [Real.sqrt_mul (by norm_num)]
      apply mul_le_mul_of_nonneg_right _ hsA
      exact (Real.le_sqrt (by positivity) (by norm_num)).mpr (by nlinarith)
    linarith

lemma potential_mono {δ ρ s s' : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s) (hss : s ≤ s') :
    potential δ ρ s ≤ potential δ ρ s' := by
  unfold potential
  have hcap : 0 < δ / ρ := by positivity
  have hc : 0 < (1 + ρ) / ρ := by positivity
  have hmin0 : 0 < min s (δ / ρ) := lt_min hs hcap
  have hmono : Real.log (min s (δ / ρ)) ≤ Real.log (min s' (δ / ρ)) :=
    (Real.log_le_log_iff hmin0 (lt_of_lt_of_le hmin0 (min_le_min_right _ hss))).mpr
      (min_le_min_right _ hss)
  have := mul_le_mul_of_nonneg_left hmono hc.le
  have := div_le_div_of_nonneg_right hss hδ.le
  linarith

variable {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
  {L0 L1 R G Δ : ℝ} {xs x0 : E} {h0 : ℝ}

noncomputable def pot (Ls L1 R : ℝ) (s : TState E) : ℝ :=
  potential (δc Ls) (ρc L1 R) (Real.sqrt s.A)

noncomputable def P0 (Ls L1 R Am : ℝ) : ℝ :=
  (1 + ρc L1 R) / ρc L1 R * Real.log (min (Real.sqrt Am) (δc Ls / ρc L1 R))

noncomputable def L0c (Ls Am : ℝ) : ℝ := 1 + max 0 (Real.logb 2 (1 / (16 * Ls * Am)))

lemma pot_run (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) (n : ℕ) :
    (run g prox x0 h0 n).A = 0 ∨
      (P0 (L0 + L1 * G) L1 R (Amin (L0 + L1 * G) L1 Δ h0) +
          3 / 4 * ((acc g prox x0 h0 n : ℝ) - 1 - L0c (L0 + L1 * G) (Amin (L0 + L1 * G) L1 Δ h0)) ≤
        pot (L0 + L1 * G) L1 R (run g prox x0 h0 n) ∧
        P0 (L0 + L1 * G) L1 R (Amin (L0 + L1 * G) L1 Δ h0) ≤
          pot (L0 + L1 * G) L1 R (run g prox x0 h0 n)) := by
  have hL0 := b.hyp.hL0
  have hL1 := b.hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans b.hG
  set Ls := L0 + L1 * G with hLs
  have hLs : 0 < Ls := by positivity
  have hb : 0 < hbar Ls L1 Δ := by unfold hbar; have := b.hΔ; positivity
  set Am := Amin Ls L1 Δ h0 with hAmdef
  have hAm : 0 < Am := lt_min b.hh0 (by positivity)
  have hδ := δc_pos hLs
  have hρ := ρc_pos hL1 b.hR
  have hρ3 := ρc_le hL1 b.hR
  have hcap : 0 < δc Ls / ρc L1 R := by positivity
  have hc : 0 < (1 + ρc L1 R) / ρc L1 R := by positivity
  have hL0c : 1 ≤ L0c Ls Am := by unfold L0c; linarith [le_max_left (0:ℝ) (Real.logb 2 (1 / (16 * Ls * Am)))]
  induction n with
  | zero => left; rfl
  | succ n ih =>
    have hinv := run_inv b n
    have hphase := run_phase b n
    obtain ⟨s, hsdef⟩ : ∃ s, s = run g prox x0 h0 n := ⟨_, rfl⟩
    rw [← hsdef] at hinv ih hphase
    have hh : 0 < s.h := hinv.2.2.2.2.2.2
    simp only [run, acc]
    rw [← hsdef]
    rcases hphase with ⟨hA0, hx, hz, hk, hhc⟩ | ⟨hA, hAm', hJ, hk⟩
    · by_cases hacc : Accepts g prox s
      · right
        rw [trial_accept hacc]
        simp only [hacc, ite_true, hk]
        have ha : trialA s = s.h := by simp only [trialA, hA0]; exact stepWeight_zero hh.le
        have hAm1 : Am ≤ s.h := by
          rcases hhc with h | h
          · rw [h]; exact min_le_left _ _
          · exact (min_le_right _ _).trans h.le
        have hpot : P0 Ls L1 R Am ≤ pot Ls L1 R ⟨s.A + trialA s, trialX g prox s, trialP g prox s, 2 * s.h⟩ := by
          simp only [pot, potential, P0, hA0, ha, zero_add]
          have h1 : 0 ≤ Real.sqrt s.h / δc Ls := by positivity
          have hmono : Real.log (min (Real.sqrt Am) (δc Ls / ρc L1 R)) ≤
              Real.log (min (Real.sqrt s.h) (δc Ls / ρc L1 R)) := by
            apply Real.log_le_log (lt_min (Real.sqrt_pos.mpr hAm) hcap)
            exact min_le_min_right _ (Real.sqrt_le_sqrt hAm1)
          have := mul_le_mul_of_nonneg_left hmono hc.le
          linarith
        refine ⟨?_, hpot⟩
        push_cast
        have : 3 / 4 * ((0 : ℝ) + 1 - 1 - L0c Ls Am) ≤ 0 := by nlinarith
        linarith
      · left
        rw [trial_reject hacc]; exact hA0
    · right
      rcases ih with hzero | ⟨hpot1, hpot2⟩
      · exact absurd hzero hA.ne'
      by_cases hacc : Accepts g prox s
      · rw [trial_accept hacc]
        simp only [hacc, ite_true]
        set a := trialA s with hadef
        have ha : 0 < a := stepWeight_pos hh hA.le
        have hmono : pot Ls L1 R s ≤ pot Ls L1 R ⟨s.A + a, trialX g prox s, trialP g prox s, 2 * s.h⟩ := by
          simp only [pot]
          exact potential_mono hδ hρ (Real.sqrt_pos.mpr hA) (Real.sqrt_le_sqrt (by linarith))
        by_cases hgood : gfun Ls L1 R s.A / 2 ≤ 2 ^ (acc g prox x0 h0 n) * Am
        · have hqh : gfun Ls L1 R s.A / 2 ≤ s.h := by
            refine le_trans ?_ hJ
            exact le_min hgood le_rfl
          have hgrow := good_growth hLs hL1 b.hR hA hh hqh
          have ha_eq : stepWeight s.h s.A = a := rfl
          rw [ha_eq] at hgrow
          have hstep := potential_step hδ hρ hρ3 (Real.sqrt_pos.mpr hA)
            (Real.sqrt_le_sqrt (by linarith : s.A ≤ s.A + a)) hgrow
          simp only [pot] at hpot1 hpot2 ⊢
          push_cast
          constructor
          · have : 3 / 4 * (((acc g prox x0 h0 n : ℝ) + 1) - 1 - L0c Ls Am) =
                3 / 4 * ((acc g prox x0 h0 n : ℝ) - 1 - L0c Ls Am) + 3 / 4 := by ring
            rw [this]; linarith
          · linarith
        · push Not at hgood
          have hsmall : (2 : ℝ) ^ (acc g prox x0 h0 n) * Am < 1 / (16 * Ls) := by
            have := gfun_le_inv (L1 := L1) (R := R) hLs hA
            have e : 1 / (8 * Ls) / 2 = 1 / (16 * Ls) := by field_simp; ring
            linarith
          have hlogb : (acc g prox x0 h0 n : ℝ) < Real.logb 2 (1 / (16 * Ls * Am)) := by
            have h1 : (2 : ℝ) ^ (acc g prox x0 h0 n) < 1 / (16 * Ls * Am) := by
              rw [lt_div_iff₀ (by positivity)]
              rw [lt_div_iff₀ (by positivity)] at hsmall
              linarith
            have h2 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h1
            rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
          have hk' : (acc g prox x0 h0 n : ℝ) + 1 - 1 - L0c Ls Am < 0 := by
            unfold L0c
            have := le_max_right (0:ℝ) (Real.logb 2 (1 / (16 * Ls * Am)))
            linarith
          push_cast
          constructor
          · nlinarith
          · linarith
      · rw [trial_reject hacc]
        simp only [hacc, ite_false, add_zero]
        exact ⟨hpot1, hpot2⟩

lemma run_accuracy (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) {ε K : ℝ} (hε : 0 < ε)
    (hK : 4 / 3 * (4 * Real.sqrt 32 * Real.sqrt ((L0 + L1 * G) * R ^ 2 / ε) +
      (1 + ρc L1 R) / ρc L1 R *
        Real.log (1 + δc (L0 + L1 * G) / ρc L1 R / Real.sqrt (Amin (L0 + L1 * G) L1 Δ h0))) ≤ K)
    (n : ℕ) (hn : 1 + L0c (L0 + L1 * G) (Amin (L0 + L1 * G) L1 Δ h0) + K ≤ (acc g prox x0 h0 n : ℝ)) :
    R ^ 2 / ε ≤ (run g prox x0 h0 n).A := by
  have hR := b.hR
  have hL0 := b.hyp.hL0
  have hL1 := b.hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans b.hG
  set Ls := L0 + L1 * G with hLs
  have hLs : 0 < Ls := by positivity
  have hb : 0 < hbar Ls L1 Δ := by unfold hbar; have := b.hΔ; positivity
  set Am := Amin Ls L1 Δ h0 with hAmdef
  have hAm : 0 < Am := lt_min b.hh0 (by positivity)
  have hδ := δc_pos hLs
  have hρ := ρc_pos hL1 b.hR
  have hcap : 0 < δc Ls / ρc L1 R := by positivity
  have hc : 0 < (1 + ρc L1 R) / ρc L1 R := by positivity
  have hL0c : 1 ≤ L0c Ls Am := by unfold L0c; linarith [le_max_left (0:ℝ) (Real.logb 2 (1 / (16 * Ls * Am)))]
  have hK0 : 0 ≤ K := by
    refine le_trans ?_ hK
    have : 0 ≤ Real.log (1 + δc Ls / ρc L1 R / Real.sqrt Am) := Real.log_nonneg (by
      have : 0 ≤ δc Ls / ρc L1 R / Real.sqrt Am := by positivity
      linarith)
    positivity
  have hacc1 : (1 : ℝ) ≤ acc g prox x0 h0 n := by linarith
  rcases pot_run b n with hzero | ⟨hpot, -⟩
  · exfalso
    rcases run_phase b n with ⟨-, -, -, hk, -⟩ | ⟨hA, -, -, -⟩
    · rw [hk] at hacc1; norm_num at hacc1
    · exact hA.ne' hzero
  set s := run g prox x0 h0 n
  have hA : 0 < s.A := by
    rcases run_phase b n with ⟨-, -, -, hk, -⟩ | ⟨hA, -, -, -⟩
    · rw [hk] at hacc1; norm_num at hacc1
    · exact hA
  by_contra hsmall
  push Not at hsmall
  have hsK : Real.sqrt s.A < R / Real.sqrt ε := by
    rw [Real.sqrt_lt' (by positivity), div_pow, Real.sq_sqrt hε.le]
    exact hsmall
  have hup : pot Ls L1 R s ≤ Real.sqrt s.A / δc Ls + (1 + ρc L1 R) / ρc L1 R *
      Real.log (δc Ls / ρc L1 R) := by
    simp only [pot, potential]
    have : Real.log (min (Real.sqrt s.A) (δc Ls / ρc L1 R)) ≤ Real.log (δc Ls / ρc L1 R) :=
      Real.log_le_log (lt_min (Real.sqrt_pos.mpr hA) hcap) (min_le_right _ _)
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  have hlogdiff : Real.log (δc Ls / ρc L1 R) - Real.log (min (Real.sqrt Am) (δc Ls / ρc L1 R)) ≤
      Real.log (1 + δc Ls / ρc L1 R / Real.sqrt Am) := by
    have hm : 0 < min (Real.sqrt Am) (δc Ls / ρc L1 R) := lt_min (Real.sqrt_pos.mpr hAm) hcap
    rw [← Real.log_div hcap.ne' hm.ne']
    apply Real.log_le_log (by positivity)
    rcases le_total (Real.sqrt Am) (δc Ls / ρc L1 R) with hle | hle
    · rw [min_eq_left hle]
      have : 0 < Real.sqrt Am := Real.sqrt_pos.mpr hAm
      linarith
    · rw [min_eq_right hle, div_self hcap.ne']
      have : 0 ≤ δc Ls / ρc L1 R / Real.sqrt Am := by positivity
      linarith
  have hsδ : Real.sqrt s.A / δc Ls < 4 * Real.sqrt 32 * Real.sqrt (Ls * R ^ 2 / ε) := by
    have hs32 : 0 < Real.sqrt 32 := by positivity
    have hsLs : 0 < Real.sqrt Ls := Real.sqrt_pos.mpr hLs
    have e : Real.sqrt s.A / δc Ls = 4 * Real.sqrt 32 * Real.sqrt Ls * Real.sqrt s.A := by
      unfold δc; rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 32)]; field_simp
    rw [e, Real.sqrt_div (by positivity), Real.sqrt_mul hLs.le, Real.sqrt_sq b.hR.le]
    have hpos : 0 < 4 * Real.sqrt 32 * Real.sqrt Ls := by positivity
    calc 4 * Real.sqrt 32 * Real.sqrt Ls * Real.sqrt s.A
        < 4 * Real.sqrt 32 * Real.sqrt Ls * (R / Real.sqrt ε) := by gcongr
      _ = 4 * Real.sqrt 32 * (Real.sqrt Ls * R / Real.sqrt ε) := by ring
  simp only [P0] at hpot
  have hmain : 3 / 4 * K ≤ pot Ls L1 R s - (1 + ρc L1 R) / ρc L1 R *
      Real.log (min (Real.sqrt Am) (δc Ls / ρc L1 R)) := by
    have : 3 / 4 * K ≤ 3 / 4 * ((acc g prox x0 h0 n : ℝ) - 1 - L0c Ls Am) := by linarith
    linarith
  have := mul_le_mul_of_nonneg_left hlogdiff hc.le
  nlinarith

end OracleTemplate.CompositeParameterFree
