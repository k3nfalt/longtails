import LongTails.Proofs.EscapeChainBounds

namespace LongTails.Proofs.EscapeChainGeometry

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds RelativeHessianArctan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

def dead (u v : ℕ → E) (l : ℕ) (x : E) : Prop :=
  ⟪u l, x⟫ ≤ 1 / 2 ∧ ⟪v l, x⟫ ^ 2 ≤ 513 / 2097152

structure Calm (K : ℕ) (R g : ℝ) (u v : ℕ → E) (x : E) : Prop where
  grad : ∀ e : E, ‖e‖ = 1 → |D (objective K R u v) x e| ≤ g
  curv : ∀ e : E, ‖e‖ = 1 → -(1 / 10) ≤ Q (objective K R u v) x e

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma _root_.LongTails.Proofs.EscapeChainCoordinates.Frame.norm_u (fr : Frame K u v) {m : ℕ}
    (hm : m < K) : ‖u m‖ = 1 := by
  have h := fr.uu m m hm hm
  rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (u m), sq_nonneg (‖u m‖ - 1)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma _root_.LongTails.Proofs.EscapeChainCoordinates.Frame.norm_v (fr : Frame K u v) {m : ℕ}
    (hm : m < K) : ‖v m‖ = 1 := by
  have h := fr.vv m m hm hm
  rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (v m), sq_nonneg (‖v m‖ - 1)]

lemma calm_grad (_fr : Frame K u v) {R g : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R)
    (hc : Calm K R g u v x) {e : E} (he : ‖e‖ = 1) :
    |D (hidden K u v) x e + ⟪e, x⟫| ≤ g := by
  have h := hc.grad e he
  rw [(objective_inside K hR u v x hx e).1, real_inner_comm] at h
  exact h

lemma calm_curv (_fr : Frame K u v) {R g : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R)
    (hc : Calm K R g u v x) {e : E} (he : ‖e‖ = 1) :
    -(1 / 10) ≤ Q (hidden K u v) x e + 1 := by
  have h := hc.curv e he
  rw [(objective_inside K hR u v x hx e).2, he] at h
  simpa using h

lemma strength_pos : (0 : ℝ) < strength := by unfold strength; positivity

lemma step_one (fr : Frame K u v) {R g : ℝ} (hR : 0 < R) (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30)
    {x : E} (hx : ‖x‖ ≤ R) (hc : Calm K R g u v x) {i : ℕ} (hi : i < K)
    (hdead : ∀ l, i ≤ l → l < K → dead u v l x) : prevGam u i x < 1 / 2 := by
  set W := tail u v i x with hWdef
  have hA : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2 := fun m h1 h2 => (hdead m h1 h2).1
  have hDW := hidden_tail fr hi x hA
  have hWn := tail_norm fr hi x
  rw [← hWdef] at hDW hWn
  have hai : ⟪u i, x⟫ = ⟪u i, W⟫ := by rw [hWdef, tail_u fr hi hi, ite_eq_left le_rfl]
  have hai_le : |⟪u i, x⟫| ≤ ‖W‖ := by
    rw [hai]
    calc |⟪u i, W⟫| ≤ ‖u i‖ * ‖W‖ := abs_real_inner_le_norm _ _
      _ = ‖W‖ := by rw [fr.norm_u hi, one_mul]
  obtain ⟨hlam, hlam2⟩ := lam_dead (hdead i le_rfl hi).2
  obtain ⟨p0, p1⟩ := prevPsi_bounds u i x
  obtain ⟨d0, d1⟩ := density_bounds ⟪u i, x⟫
  have hl0 := (lam_bounds ⟪v i, x⟫).1
  obtain ⟨k0, -⟩ := kappa_bounds fr x (n := i + 1) (by omega)
  have hmu := strength_pos
  have hmuL : strength * (1 / (24 * 2 ^ 28)) = 1 / 384 := by unfold strength; norm_num
  have hWsmall : ‖W‖ ≤ g + 1 / 384 := by
    rcases eq_or_lt_of_le (norm_nonneg W) with h0 | hpos
    · rw [← h0]; linarith
    have hunit : ‖(‖W‖⁻¹) • W‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hpos.ne']
    have hgr := calm_grad fr hR hx hc hunit
    have hlin : D (hidden K u v) x ((‖W‖⁻¹) • W) + ⟪(‖W‖⁻¹) • W, x⟫ =
        ‖W‖⁻¹ * (D (hidden K u v) x W + ⟪W, x⟫) := by
      unfold D; rw [inner_smul_right, real_inner_smul_left]; ring
    rw [hlin, abs_mul, abs_inv, abs_norm] at hgr
    have hupper : D (hidden K u v) x W + ⟪W, x⟫ ≤ g * ‖W‖ := by
      have := (le_abs_self _).trans ((inv_mul_le_iff₀ hpos).1 hgr)
      linarith
    rw [hDW, real_inner_comm x W, ← hWn] at hupper
    have hprod : lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫ ≤ 1 / (24 * 2 ^ 28) := by
      have h1 := mul_le_mul hlam p1 p0 (by positivity)
      have h2 := mul_le_mul h1 d1 d0.le (by positivity)
      linarith
    have hprod0 : 0 ≤ lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫ := by positivity
    have hterm : -strength * (lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫) * ⟪u i, x⟫ ≥
        -(1 / 384) * ‖W‖ := by
      have h1 : |strength * (lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫) * ⟪u i, x⟫| ≤
          (1 / 384) * ‖W‖ := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        calc _ ≤ (strength * (1 / (24 * 2 ^ 28))) * ‖W‖ := by gcongr
          _ = _ := by rw [hmuL]
      have := le_abs_self (strength * (lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫) * ⟪u i, x⟫)
      linarith
    have hk : 0 ≤ (∑ l ∈ Finset.range (i + 1), weight u v l x) * ‖W‖ ^ 2 := by positivity
    have : ‖W‖ ^ 2 ≤ (g + 1 / 384) * ‖W‖ := by nlinarith
    nlinarith
  have hres := resid_tail fr hi x
  have hci := (hdead i le_rfl hi).2
  have hq : quarter u v i x ≤ 1 := by
    unfold quarter
    rw [hres]
    have hg' : g + 1 / 384 ≤ 1 / 100 := by
      have : (1 : ℝ) / 2 ^ 30 ≤ 1 / 1000 := by norm_num
      linarith
    have hw2 : ‖W‖ ^ 2 ≤ (1 / 100) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hWsmall.trans hg') 2
    nlinarith
  obtain ⟨hloc, hloc1, hloc2, -⟩ := loc_one hq
  have hwin : window u v i x = 1 := hloc
  obtain ⟨-, -, hs2, -⟩ := sad_jets_inner (show ⟪v i, x⟫ ^ 2 ≤ 1 / 1536 by linarith)
  have hcurv := calm_curv fr hR hx hc (fr.norm_v hi)
  rw [hidden_qv fr hi x, hwin, hloc1, hs2] at hcurv
  have hext := extras_bound fr x (n := i + 1) (by omega) (t := ⟪v i, x⟫ ^ 2) (sq_nonneg _)
    (by linarith)
  have hlink : 0 ≤ strength * (prevPsi u i x * profile ⟪u i, x⟫ * lam2 ⟪v i, x⟫) := by
    have := (profile_bounds ⟪u i, x⟫).1
    positivity
  have hsum := (abs_le.1 hext).2
  nlinarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma pulls (_fr : Frame K u v) {i : ℕ} (_hi : i < K) (x : E) (hdi : dead u v i x) (a : ℝ) :
    |-strength * (lam ⟪v i, x⟫ * profile ⟪u i, x⟫ * psi1 a)| ≤ 6 / 100 ∧
      |sad ⟪v i, x⟫ * window u v i x * gam1 a| ≤ 1 / 100 := by
  obtain ⟨hlam, -⟩ := lam_dead hdi.2
  have hl0 := (lam_bounds ⟪v i, x⟫).1
  obtain ⟨f0, f1⟩ := profile_bounds ⟪u i, x⟫
  obtain ⟨-, -, q0, q1, -, -⟩ := ag_bounds (show (0 : ℝ) ≤ 8 by norm_num) (-4) a
  obtain ⟨-, -, r0, r1, -, -⟩ := ag_bounds (show (0 : ℝ) ≤ 20 by norm_num) (-12) a
  obtain ⟨w0, w1, -⟩ := loc_bounds (quarter u v i x)
  have hs := sad_abs_le ⟪v i, x⟫
  have hpi := Real.pi_lt_four
  have hs0 := strength_pos
  constructor
  · rw [abs_mul, abs_neg, abs_of_pos strength_pos, abs_of_nonneg (by positivity)]
    calc strength * (lam ⟪v i, x⟫ * profile ⟪u i, x⟫ * psi1 a)
        ≤ strength * ((1 / (24 * 2 ^ 28)) * 4 * (2 / 3 * 8)) := by
          gcongr
          first | exact hlam | exact q1 | linarith
      _ ≤ 6 / 100 := by unfold strength; norm_num
  · rw [abs_mul, abs_mul]
    have hw : |window u v i x| ≤ 1 := by
      rw [show window u v i x = loc (quarter u v i x) from rfl, abs_of_nonneg w0]; exact w1
    calc |sad ⟪v i, x⟫| * |window u v i x| * |gam1 a|
        ≤ (2 * (513 / 2097152)) * 1 * (2 / 3 * 20) := by
          gcongr
          · exact hs.trans (by linarith [hdi.2])
          · rw [abs_of_nonneg r0]; exact r1
      _ ≤ 1 / 100 := by norm_num

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma pull_nonpos (u v : ℕ → E) (i : ℕ) (x : E) (a : ℝ) :
    -strength * (lam ⟪v i, x⟫ * profile ⟪u i, x⟫ * psi1 a) ≤ 0 ∧
      sad ⟪v i, x⟫ * window u v i x * gam1 a ≤ 0 := by
  have h1 := (lam_bounds ⟪v i, x⟫).1
  have h2 := (profile_bounds ⟪u i, x⟫).1
  have h3 := (ag_bounds (show (0 : ℝ) ≤ 8 by norm_num) (-4) a).2.2.1
  have h4 := sad_nonpos ⟪v i, x⟫
  have h5 := (loc_bounds (quarter u v i x)).1
  have h6 := (ag_bounds (show (0 : ℝ) ≤ 20 by norm_num) (-12) a).2.2.1
  have hs := strength_pos
  constructor
  · have : 0 ≤ lam ⟪v i, x⟫ * profile ⟪u i, x⟫ * psi1 a := by positivity
    nlinarith
  · have hw : 0 ≤ window u v i x := h5
    have : 0 ≤ window u v i x * gam1 a := mul_nonneg hw h6
    have := mul_nonpos_of_nonpos_of_nonneg h4 this
    linarith [show sad ⟪v i, x⟫ * window u v i x * gam1 a = sad ⟪v i, x⟫ * (window u v i x * gam1 a)
      by ring]

set_option maxHeartbeats 4000000 in
lemma step_two (fr : Frame K u v) {R g : ℝ} (hR : 0 < R) (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30)
    {x : E} (hx : ‖x‖ ≤ R) (hc : Calm K R g u v x) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < K)
    (hdead : ∀ l, i ≤ l → l < K → dead u v l x) (hG : prevGam u i x < 1 / 2) :
    dead u v (i - 1) x := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hjK : j < K := by omega
  have hdi := hdead (j + 1) le_rfl hi
  have hg1 : g ≤ 1 / 1000 := hg.trans (by norm_num)
  have hs := strength_pos
  set a := ⟪u j, x⟫ with ha_def
  set c := ⟪v j, x⟫ with hc_def
  have haj : a < 4 / 5 := by
    by_contra h
    push Not at h
    have := (gam_full h).1
    rw [prevGam_succ] at hG
    linarith
  have hEu := calm_grad fr hR hx hc (fr.norm_u hjK)
  rw [hidden_u fr hjK x, ite_eq_left hi] at hEu
  obtain ⟨pl1, pl2⟩ := pulls fr hi x hdi a
  obtain ⟨ps1, ps2⟩ := pull_nonpos u v (j + 1) x a
  obtain ⟨k0, k1⟩ := kappa_bounds fr x (n := j + 1) (by omega)
  set κ := ∑ l ∈ Finset.range (j + 1), weight u v l x with hκ
  set P := prevPsi u j x with hP
  obtain ⟨P0, P1⟩ := prevPsi_bounds u j x
  have hl0 := (lam_bounds c).1
  have hl1 := (lam_bounds c).2
  set L := strength * (lam c * P * density a) with hL
  have hL0 : 0 ≤ L := by
    have := (density_bounds a).1
    positivity
  set p1 := -strength * (lam ⟪v (j + 1), x⟫ * profile ⟪u (j + 1), x⟫ * psi1 a) with hp1
  set p2 := sad ⟪v (j + 1), x⟫ * window u v (j + 1) x * gam1 a with hp2
  have hEu' : |-L + (p1 + p2) + κ * a + a| ≤ g := by
    have : -strength * (lam c * P * density a) = -L := by rw [hL]; ring
    rw [← this]; exact hEu
  obtain ⟨hEl, hEr⟩ := abs_le.1 hEu'
  have ha0 : -g ≤ a := by
    by_contra h
    push Not at h
    have : κ * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos k0 (by linarith)
    linarith
  have hLb : L ≤ 9 / 10 := by
    have : κ * a ≤ (1 / 10) * (4 / 5) := by
      rcases le_or_gt 0 a with h | h
      · exact mul_le_mul k1 haj.le h (by norm_num)
      · have : κ * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos k0 h.le
        linarith
    linarith
  have hdens : 3 / 5 ≤ density a := density_lower (by linarith) haj.le
  have hlamP : strength * (lam c * P) ≤ 3 / 2 := by
    have : strength * (lam c * P) * (3 / 5) ≤ L := by
      rw [hL]
      have : 0 ≤ strength * (lam c * P) := by positivity
      nlinarith
    linarith
  by_cases hcd : c ^ 2 ≤ 513 / 2097152
  · refine ⟨?_, hcd⟩
    obtain ⟨hlt, -⟩ := lam_dead hcd
    have hLs : L ≤ 1 / 384 := by
      rw [hL]
      have hd1 := (density_bounds a).2
      calc strength * (lam c * P * density a) ≤ strength * ((1 / (24 * 2 ^ 28)) * 1 * 1) := by
            gcongr
        _ = 1 / 384 := by unfold strength; norm_num
    have hp1' := (abs_le.1 pl1).1
    have hp2' := (abs_le.1 pl2).1
    rcases le_or_gt a 0 with h | h
    · linarith
    · have : 0 ≤ κ * a := mul_nonneg k0 h.le
      linarith
  exfalso
  push Not at hcd
  have hEv := calm_grad fr hR hx hc (fr.norm_v hjK)
  rw [hidden_v fr hjK x] at hEv
  set Gj := prevGam u j x with hGj
  obtain ⟨G0, G1⟩ := prevGam_bounds u j x
  obtain ⟨w0, w1, -⟩ := loc_bounds (quarter u v j x)
  have hw0 : 0 ≤ window u v j x := w0
  have hpred : 1 / 60 ≤ P ∨ ∃ j', j = j' + 1 ∧ ⟪u j', x⟫ < 3 / 5 := by
    rcases j with _ | j'
    · left; rw [hP, prevPsi_zero]; norm_num
    · by_cases h : ⟪u j', x⟫ < 3 / 5
      · exact Or.inr ⟨j', rfl, h⟩
      · left; rw [hP, prevPsi_succ]; exact psi_of_gt (le_of_not_gt h)
  have hbig : (2 : ℝ) ^ 24 = strength := rfl
  by_cases hA : 1 / 2048 ≤ c ^ 2
  · obtain ⟨hl, hl1, -, -⟩ := lam_full hA
    have hPs : strength * P ≤ 3 / 2 := by rw [hl, one_mul] at hlamP; exact hlamP
    rcases hpred with h | ⟨j', rfl, h⟩
    · have : strength * (1 / 60) ≤ 3 / 2 := le_trans (by gcongr) hPs
      unfold strength at this; norm_num at this
    · have hGz : Gj = 0 := by rw [hGj, prevGam_succ]; exact (gam_flat h.le).1
      rw [hGz, hl1] at hEv
      have : |(1 + κ) * c| ≤ g := by
        have he : -strength * (P * profile a * 0) + 0 * window u v (j' + 1) x * sad1 c + κ * c + c =
          (1 + κ) * c := by ring
        rw [he] at hEv; exact hEv
      rw [abs_mul, abs_of_pos (by linarith)] at this
      have hc1 : |c| ≤ g := le_trans (le_mul_of_one_le_left (abs_nonneg c) (by linarith)) this
      have : c ^ 2 ≤ g ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg c) hc1 2
      have hgg : g ^ 2 ≤ (1 / 2 ^ 30) ^ 2 := pow_le_pow_left₀ hg0.le hg 2
      norm_num at hgg
      linarith
  push Not at hA
  have hc1536 : c ^ 2 ≤ 1 / 1536 := by linarith
  obtain ⟨-, hs1, -, -⟩ := sad_jets_inner hc1536
  have hcabs : |c| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; linarith
  have hcE : |-strength * (P * profile a * (lam1 c * c)) + Gj * window u v j x * (sad1 c * c) +
      (1 + κ) * c ^ 2| ≤ g := by
    have he : -strength * (P * profile a * (lam1 c * c)) + Gj * window u v j x * (sad1 c * c) +
        (1 + κ) * c ^ 2 = c * (-strength * (P * profile a * lam1 c) + Gj * window u v j x * sad1 c +
          κ * c + c) := by ring
    rw [he, abs_mul]
    calc |c| * |-strength * (P * profile a * lam1 c) + Gj * window u v j x * sad1 c + κ * c + c|
        ≤ 1 * g := mul_le_mul hcabs hEv (abs_nonneg _) (by norm_num)
      _ = g := one_mul g
  obtain ⟨hcEl, hcEr⟩ := abs_le.1 hcE
  have hsc : Gj * window u v j x * (sad1 c * c) ≤ 0 := by
    rw [hs1]
    have : 0 ≤ Gj * window u v j x := mul_nonneg G0 hw0
    nlinarith [sq_nonneg c]
  have hprof : 3 / 4 ≤ profile a := profile_lower (by linarith)
  rcases hpred with hP60 | ⟨j', rfl, hj'⟩
  · have hlsmall : lam c < 1 / 24 := by
      have : strength * (lam c * (1 / 60)) ≤ 3 / 2 :=
        le_trans (by gcongr) hlamP
      unfold strength at this
      linarith
    have hslope := lam_slope_lower hcd hlsmall
    have hpush : strength * ((1 / 60) * (3 / 4) * (1 / (6 * 2 ^ 18))) ≤
        strength * (P * profile a * (lam1 c * c)) := by
      gcongr
    have hnum : strength * ((1 / 60) * (3 / 4) * (1 / (6 * 2 ^ 18))) = 2 / 15 := by
      unfold strength; norm_num
    have hκc : κ * c ^ 2 ≤ 1 / 10 * c ^ 2 := mul_le_mul_of_nonneg_right k1 (sq_nonneg c)
    linarith
  · have hGz : Gj = 0 := by rw [hGj, prevGam_succ]; exact (gam_flat hj'.le).1
    rw [hGz] at hcEl hcEr
    simp only [zero_mul, add_zero] at hcEl hcEr
    rcases le_or_gt ⟪u j', x⟫ (1 / 2) with hj2 | hj2
    · have hPz : P = 0 := by rw [hP, prevPsi_succ]; exact (psi_flat hj2).1
      rw [hPz] at hcEr
      simp at hcEr
      nlinarith
    have hbal : c ^ 2 - g ≤ strength * (P * profile a * (lam1 c * c)) := by nlinarith
    rcases le_or_gt (16384 * c ^ 2 - 4) (19 / 10) with hw | hw
    · obtain ⟨hcur, hl1c⟩ := lam_curvature hcd hw
      have hQv := calm_curv fr hR hx hc (fr.norm_v hjK)
      rw [hidden_qv fr hjK x, ← hGj, hGz] at hQv
      have hext := extras_bound fr x (n := j' + 1 + 1) (by omega) (t := c ^ 2) (sq_nonneg _)
        (by linarith)
      have hext' := (abs_le.1 hext).2
      have hS : strength * (P * profile a * lam2 c) ≤ 6 / 5 := by nlinarith
      have hSc : 3 * (c ^ 2 - g) ≤ strength * (P * profile a * lam2 c) * c ^ 2 := by
        have h0 : 0 ≤ strength * (P * profile a) := by positivity
        have := mul_le_mul_of_nonneg_left hcur h0
        nlinarith
      have : strength * (P * profile a * lam2 c) * c ^ 2 ≤ 6 / 5 * c ^ 2 :=
        mul_le_mul_of_nonneg_right hS (sq_nonneg c)
      nlinarith
    · obtain ⟨hlp, hratio⟩ := lam_plateau hw
      set a' := ⟪u j', x⟫ with ha'
      have hPs : strength * P ≤ 15 / 4 := by
        have : strength * P * (2 / 5) ≤ strength * (lam c * P) := by
          have : 0 ≤ strength * P := by positivity
          nlinarith
        linarith
      set B := strength * P * profile a * lam c with hB
      have hB0 : 1 / 53000 ≤ B := by
        have h1 : 5 * (c ^ 2 - g) ≤ 8 * (32768 * c ^ 2) * B := by
          have h0 : 0 ≤ strength * (P * profile a) := by positivity
          have := mul_le_mul_of_nonneg_left hratio h0
          rw [hB]; nlinarith
        have hc2 : 513 / 2097152 < c ^ 2 := hcd
        nlinarith
      obtain ⟨hon, hon2⟩ := psi_onset (a := a') hj2.le (by linarith)
      have hsq := psi_onset_sq (a := a') hj2.le (by linarith)
      have hPdef : P = psi a' := by rw [hP, prevPsi_succ]
      set A := strength * (lam c * profile a * psi2 a') with hA'
      have hA0 : 0 ≤ A := by
        rw [hA', hon2]
        have := (lam_bounds c).1
        have := (profile_bounds a).1
        positivity
      have hA2 : A ^ 2 = 24576 * (strength * lam c * profile a) * B := by
        rw [hA', hB, mul_pow, mul_pow, mul_pow, hsq, ← hPdef]; ring
      have hM : strength * B ≤ 15 / 4 * (strength * lam c * profile a) := by
        have h0 : 0 ≤ strength * lam c * profile a := by
          have := (profile_bounds a).1
          positivity
        have : strength * B = (strength * P) * (strength * lam c * profile a) := by rw [hB]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hPs h0
      have hA6 : 6 ≤ A := by
        have h1 : 24576 * (strength * B) * B ≤ 24576 * (15 / 4 * (strength * lam c * profile a)) * B :=
          by gcongr
        have h2 : 24576 * (strength * (1 / 53000)) * (1 / 53000) ≤ 24576 * (strength * B) * B := by
          gcongr
        have h3 : (36 : ℝ) * (15 / 4) ≤ 24576 * (strength * (1 / 53000)) * (1 / 53000) := by
          unfold strength; norm_num
        have e1 : 24576 * (strength * B) * B ≤ 15 / 4 * A ^ 2 := by
          rw [hA2]; linarith only [h1]
        have hA36 : 36 ≤ A ^ 2 := by linarith only [e1, h2, h3]
        nlinarith only [hA36, hA0]
      have hj'K : j' < K := by omega
      have hEu2 := calm_grad fr hR hx hc (fr.norm_u hj'K)
      rw [hidden_u fr hj'K x, ite_eq_left (by omega)] at hEu2
      obtain ⟨qs1, qs2⟩ := pull_nonpos u v (j' + 1) x a'
      obtain ⟨k0', k1'⟩ := kappa_bounds fr x (n := j' + 1) (by omega)
      have hd' := density_lower' hj2.le hj'.le
      obtain ⟨d0', -⟩ := density_bounds a'
      have hlam' := (lam_bounds ⟪v j', x⟫).1
      obtain ⟨P0', -⟩ := prevPsi_bounds u j' x
      have hL' : strength * (lam ⟪v j', x⟫ * prevPsi u j' x) ≤ 19 / 20 := by
        have hEl2 := (abs_le.1 hEu2).1
        have hk : (∑ l ∈ Finset.range (j' + 1), weight u v l x) * a' ≤ (1 / 10) * (3 / 5) :=
          mul_le_mul k1' hj'.le (by linarith) (by norm_num)
        have h0 : 0 ≤ strength * (lam ⟪v j', x⟫ * prevPsi u j' x) := by positivity
        have : strength * (lam ⟪v j', x⟫ * prevPsi u j' x) * (7 / 10) ≤
            strength * (lam ⟪v j', x⟫ * prevPsi u j' x * density a') := by
          have : strength * (lam ⟪v j', x⟫ * prevPsi u j' x * density a') =
            strength * (lam ⟪v j', x⟫ * prevPsi u j' x) * density a' := by ring
          rw [this]; exact mul_le_mul_of_nonneg_left hd' h0
        nlinarith
      have hQu := calm_curv fr hR hx hc (fr.norm_u hj'K)
      rw [hidden_qu fr hj'K x, ite_eq_left (by omega), (gam_flat hj'.le).2.2.1] at hQu
      have hext := extras_bound fr x (n := j' + 1) (by omega) (t := a' ^ 2) (sq_nonneg _)
        (by nlinarith)
      have hext' := (abs_le.1 hext).2
      have hds := (RelativeHessianArctan.profile_jet_bounds a').2.1
      have hfirst : -strength * (lam ⟪v j', x⟫ * prevPsi u j' x * densitySlope a') ≤ 19 / 10 := by
        have h0 : 0 ≤ strength * (lam ⟪v j', x⟫ * prevPsi u j' x) := by positivity
        have : |strength * (lam ⟪v j', x⟫ * prevPsi u j' x * densitySlope a')| ≤ 19 / 20 * 2 := by
          rw [show strength * (lam ⟪v j', x⟫ * prevPsi u j' x * densitySlope a') =
            strength * (lam ⟪v j', x⟫ * prevPsi u j' x) * densitySlope a' by ring, abs_mul,
            abs_of_nonneg h0]
          exact mul_le_mul hL' hds (abs_nonneg _) (by norm_num)
        have := neg_abs_le (strength * (lam ⟪v j', x⟫ * prevPsi u j' x * densitySlope a'))
        linarith
      have hAe : -strength * (lam ⟪v (j' + 1), x⟫ * profile ⟪u (j' + 1), x⟫ * psi2 a') = -A := by
        rw [hA']; ring
      rw [hAe] at hQu
      nlinarith

theorem no_calm (fr : Frame K u v) {R g : ℝ} (hR : 0 < R) (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30)
    {x : E} (hx : ‖x‖ ≤ R) {k : ℕ} (hk : k < K)
    (hclean : ∀ l, k ≤ l → l < K → dead u v l x) : ¬ Calm K R g u v x := by
  intro hc
  have hind : ∀ n, n ≤ k → ∀ l, k - n ≤ l → l < K → dead u v l x := by
    intro n
    induction n with
    | zero => intro _ l hl hlK; exact hclean l (by omega) hlK
    | succ n ih =>
      intro hn l hl hlK
      have hprev := ih (by omega)
      by_cases hle : k - n ≤ l
      · exact hprev l hle hlK
      have hl' : l = k - n - 1 := by omega
      have hG := step_one fr hR hg0 hg hx hc (i := k - n) (by omega) hprev
      have := step_two fr hR hg0 hg hx hc (i := k - n) (by omega) (by omega) hprev hG
      rw [hl']; exact this
  have h0 := hind k le_rfl
  have hG := step_one fr hR hg0 hg hx hc (i := 0) (by omega) (fun l _ hl => h0 l (by omega) hl)
  rw [prevGam_zero] at hG
  norm_num at hG

end LongTails.Proofs.EscapeChainGeometry
