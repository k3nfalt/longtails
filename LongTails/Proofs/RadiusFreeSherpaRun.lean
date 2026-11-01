import LongTails.Proofs.RadiusFreeSherpaSearch
import LongTails.Proofs.RadiusFreeSherpaCount
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.unusedSectionVars false

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def bigB (q : ℝ) : ℝ :=
  q + 2 * Real.sqrt 14 * Real.sqrt 48 * q +
    14 * theta q * (theta q + 1 + Real.log (336 * (1 + q) ^ 2)) + 1

noncomputable def probeCap (q : ℝ) : ℕ := ⌈Real.logb 2 (3200 * (1 + q) ^ 2)⌉₊

def coreOf (ph : Phase E) : Core E :=
  match ph with
  | .queryX c => c
  | .queryV c _ => c
  | .probe c _ _ _ _ => c

lemma gap_lower {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (x : E) (hx : threshold L0 L1 < ‖g x‖) :
    L0 / (96 * L1 ^ 2) < f x - f u := by
  have hL0 := H.L0_pos
  have hd := descent_step H hL1 x
  have hmin : f u ≤ f (x - (1 / (4 * localCurvature L0 L1 ‖g x‖)) • g x) := H.min (mem_univ _)
  set G := ‖g x‖ with hG
  have hGpos : L0 / (4 * L1) < G := hx
  have hL : 0 < localCurvature L0 L1 G := localCurvature_pos hL0 hL1.le (norm_nonneg _)
  have hkey : L0 / (96 * L1 ^ 2) < 5 * G ^ 2 / (24 * localCurvature L0 L1 G) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    unfold localCurvature
    have h1 : L0 < 4 * L1 * G := by rw [div_lt_iff₀ (by positivity)] at hGpos; linarith
    have hGpos' : 0 < G := lt_trans (by positivity) hGpos
    have hLG : 0 < L1 * G := mul_pos hL1 hGpos'
    have hp : 0 < 4 * L1 * G + L0 := by linarith
    have h2 : L0 ^ 2 < 16 * L1 ^ 2 * G ^ 2 := by nlinarith [mul_pos (sub_pos.mpr h1) hp]
    have h3 : L0 * (L1 * G) < 4 * L1 ^ 2 * G ^ 2 := by nlinarith [mul_lt_mul_of_pos_right h1 hLG]
    nlinarith
  linarith

lemma omega_bound {L0 L1 q R A S : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hq : q = L1 * R)
    (hR : 0 < R) (hS : S ≤ R ^ 2) (hAq : L0 * A ≤ 48 * q ^ 2) :
    omega L0 L1 q A S + ind L0 q A ≤ bigB q := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hθ := theta_pos hqpos.le
  have hθsq := theta_sq hqpos.le
  unfold omega bigB
  have h1 : L1 ^ 2 / theta q ^ 2 * S ≤ q := by
    rw [hθsq, hq]
    have : L1 ^ 2 / (1 + L1 * R) * S ≤ L1 ^ 2 / (1 + L1 * R) * R ^ 2 :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h2 : L1 ^ 2 / (1 + L1 * R) * R ^ 2 ≤ L1 * R := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_pos hL1 hR]
    linarith
  have h2 : 2 * Real.sqrt 14 * Real.sqrt (L0 * A) ≤ 2 * Real.sqrt 14 * Real.sqrt 48 * q := by
    have : Real.sqrt (L0 * A) ≤ Real.sqrt 48 * q := by
      rw [← Real.sqrt_sq hqpos.le, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hAq
    have h14 : 0 ≤ 2 * Real.sqrt 14 := by positivity
    calc 2 * Real.sqrt 14 * Real.sqrt (L0 * A) ≤ 2 * Real.sqrt 14 * (Real.sqrt 48 * q) :=
          mul_le_mul_of_nonneg_left this h14
      _ = 2 * Real.sqrt 14 * Real.sqrt 48 * q := by ring
  have h3 : lnm L0 q A ≤ theta q + 1 + Real.log (336 * (1 + q) ^ 2) := by
    unfold lnm
    have hamin := aMin_pos (q := q) hL0
    have hA_le : A ≤ 48 * q ^ 2 / L0 := by rw [le_div_iff₀ hL0]; linarith
    rcases le_or_gt A (aMin L0 q) with hcase | hcase
    · rw [max_eq_right hcase]
      have hlog : 0 ≤ Real.log (336 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
      linarith [theta_pos hqpos.le]
    · rw [max_eq_left hcase.le]
      have hApos : 0 < A := lt_trans hamin hcase
      rw [← Real.log_div hApos.ne' hamin.ne']
      unfold aMin
      have hratio : A / (Real.exp (-theta q - 1) / (7 * L0)) ≤
          336 * (1 + q) ^ 2 * Real.exp (theta q + 1) := by
        rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        have he : Real.exp (-theta q - 1) * Real.exp (theta q + 1) = 1 := by
          rw [← Real.exp_add, show -theta q - 1 + (theta q + 1) = 0 by ring, Real.exp_zero]
        have h48 : A * (7 * L0) ≤ 336 * q ^ 2 := by nlinarith [hAq]
        have hq2 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
        calc A * (7 * L0) ≤ 336 * q ^ 2 := h48
          _ ≤ 336 * (1 + q) ^ 2 := by nlinarith
          _ = 336 * (1 + q) ^ 2 * (Real.exp (theta q + 1) * Real.exp (-theta q - 1)) := by
              rw [mul_comm (Real.exp (theta q + 1)), he, mul_one]
          _ = 336 * (1 + q) ^ 2 * Real.exp (theta q + 1) * Real.exp (-theta q - 1) := by ring
      have hpos : 0 < A / (Real.exp (-theta q - 1) / (7 * L0)) := by positivity
      calc Real.log (A / (Real.exp (-theta q - 1) / (7 * L0))) ≤
            Real.log (336 * (1 + q) ^ 2 * Real.exp (theta q + 1)) :=
            Real.log_le_log hpos hratio
        _ = Real.log (336 * (1 + q) ^ 2) + (theta q + 1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
        _ = theta q + 1 + Real.log (336 * (1 + q) ^ 2) := by ring
  have h3' : 14 * theta q * lnm L0 q A ≤ 14 * theta q * (theta q + 1 + Real.log (336 * (1 + q) ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : ind L0 q A ≤ 1 := ind_le_one
  linarith

def SubInv (f : E → ℝ) (g : E → E) (L0 L1 q : ℝ) (u : E) (ph : Phase E) (j : ℕ) : Prop :=
  match ph with
  | .queryX _ => j = 0
  | .queryV c gx => gx = g c.x ∧ threshold L0 L1 < ‖gx‖ ∧ j = 1
  | .probe c gx gv tm tp => gx = g c.x ∧ gv = g c.v ∧ threshold L0 L1 < ‖gx‖ ∧
      threshold L0 L1 < ‖gv‖ ∧ PInv f g L0 L1 u c tm tp ∧ threshold L0 L1 < ‖g (seg c tp)‖ ∧
      ∃ m : ℕ, j = 2 + m ∧ tp - tm = (1 / 2) ^ m ∧ m + 1 ≤ probeCap q

def PhInv (f : E → ℝ) (g : E → E) (L0 L1 q R : ℝ) (u : E) (n : ℕ) (ph : Phase E) : Prop :=
  ∃ (S : ℝ) (k j : ℕ), Inv f u R (coreOf ph) S ∧
    (k : ℝ) ≤ omega L0 L1 q (coreOf ph).A S + ind L0 q (coreOf ph).A ∧
    (k : ℝ) ≤ bigB q + 1 ∧
    (n : ℝ) ≤ k * (2 + probeCap q) + j ∧ SubInv f g L0 L1 q u ph j

def GoodExit (g : E → E) (L0 L1 R : ℝ) (u : E) (z : E) : Prop :=
  ‖z - u‖ ≤ R ∧ ‖g z‖ ≤ threshold L0 L1

lemma GoodExit.gap {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    {z : E} (h : GoodExit g L0 L1 R u z) : f z - f u ≤ L0 * R / (4 * L1) := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hc := OracleTemplate.Gradient.convex_support H.convex H.grad z u
  have hn : ‖u - z‖ = ‖z - u‖ := norm_sub_rev _ _
  have h1 : ‖g z‖ * ‖u - z‖ ≤ threshold L0 L1 * R := by
    rw [hn]
    exact mul_le_mul h.2 h.1 (norm_nonneg _) (by unfold threshold; positivity)
  unfold threshold at h1
  have : ⟪g z, u - z⟫ ≥ -(L0 / (4 * L1) * R) := by
    have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (g z) (u - z))
    linarith
  have e : L0 / (4 * L1) * R = L0 * R / (4 * L1) := by ring
  linarith


noncomputable def T (L0 L1 : ℝ) (g : E → E) (s : State E) : State E :=
  stateUpdate L0 L1 s (g (stateQuery s))

omit [CompleteSpace E] in
lemma T_first (L0 L1 : ℝ) (g : E → E) (ph : Phase E) :
    T L0 L1 g (.first ph) = phaseUpdate L0 L1 ph (g (phaseQuery ph)) := rfl

omit [CompleteSpace E] in
lemma T_second (L0 L1 : ℝ) (g : E → E) (s : ParameterFreeGeneralized.State E) :
    T L0 L1 g (.second s) = .second (secondUpdate s (g (secondQuery s))) := rfl

lemma probeCap_ge {q : ℝ} (hq : 0 < q) {m : ℕ} (hm : (2 : ℝ) ^ m < 3200 * q ^ 2) :
    m + 1 ≤ probeCap q := by
  unfold probeCap
  have h1 : (2 : ℝ) ^ m < 3200 * (1 + q) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 3200 * (1 + q) ^ 2 := by positivity
  have hlog : (m : ℝ) < Real.logb 2 (3200 * (1 + q) ^ 2) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos]
    simpa using h1
  have hceil := Nat.le_ceil (Real.logb 2 (3200 * (1 + q) ^ 2))
  have : (m : ℝ) < (⌈Real.logb 2 (3200 * (1 + q) ^ 2)⌉₊ : ℝ) := lt_of_lt_of_le hlog hceil
  exact Nat.succ_le_of_lt (by exact_mod_cast this)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma d_le {f : E → ℝ} {u : E} {R : ℝ} {c : Core E} {S : ℝ} (hR : 0 ≤ R)
    (hmin : IsMinOn f univ u) (hI : Inv f u R c S) : ‖c.x - c.v‖ ≤ 2 * R := by
  have h1 := hI.x_dist
  have h2 := hI.v_dist hR hmin
  calc ‖c.x - c.v‖ = ‖(c.x - u) - (c.v - u)‖ := by congr 1; abel
    _ ≤ ‖c.x - u‖ + ‖c.v - u‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith

lemma width_cap {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (hq : q = L1 * R) (hR : 0 < R) {c : Core E} {S : ℝ} (hI : Inv f u R c S)
    {tm tp : ℝ} (hP : PInv f g L0 L1 u c tm tp) (hG : threshold L0 L1 < ‖g (seg c tp)‖)
    {m : ℕ} (hm : tp - tm = (1 / 2) ^ m) : m + 1 ≤ probeCap q := by
  have hw := hP.width_bound H hL1 hG hm (d_le hR.le H.min hI)
  have hqpos : 0 < q := by rw [hq]; positivity
  apply probeCap_ge hqpos
  have : (L1 * (2 * R)) ^ 2 = 4 * q ^ 2 := by rw [hq]; ring
  rw [this] at hw
  linarith

lemma accept_ledger {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (hq : q = L1 * R) (hR : 0 < R) {c : Core E} {S : ℝ} (hI : Inv f u R c S)
    {k j n : ℕ} (hk : (k : ℝ) ≤ omega L0 L1 q c.A S + ind L0 q c.A)
    (hn : (n : ℝ) ≤ k * (2 + probeCap q) + j) (hj : (j : ℝ) + 1 ≤ 2 + probeCap q)
    (hgx : threshold L0 L1 < ‖g c.x‖)
    {y : E} (hy : 0 < ‖g y‖) (hyd : ‖y - u‖ ≤ R) (hfy : f y ≤ f c.x)
    (hB : ⟪g y, y - c.v⟫ ≤ ‖g y‖ ^ 2 / (16 * localCurvature L0 L1 ‖g y‖)) :
    PhInv f g L0 L1 q R u (n + 1) (accept L0 L1 c y (g y)) := by
  have hL0 := H.L0_pos
  have hqpos : 0 < q := by rw [hq]; positivity
  have hI' := accept_inv H hL1 hI hy hyd hfy hB
  have hinc := iteration_increment (q := q) (S := S) hL0 hL1 hqpos.le hI.A_nonneg hy
  have hgap := gap_lower H hL1 c.x hgx
  have hgap0 : 0 < f c.x - f u := lt_trans (by positivity) hgap
  have hpot := hI.potential
  have hvn : 0 ≤ ‖c.v - u‖ ^ 2 / 2 := by positivity
  have hSle : S ≤ R ^ 2 := by nlinarith [mul_nonneg hI.A_nonneg hgap0.le, hI.S_nonneg]
  have hAgap : c.A * (f c.x - f u) ≤ R ^ 2 / 2 := by linarith [hI.S_nonneg]
  have hAq : L0 * c.A ≤ 48 * q ^ 2 := by
    have h1 : c.A * (L0 / (96 * L1 ^ 2)) ≤ R ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hgap.le hI.A_nonneg
      linarith
    rw [hq]
    have h2 : c.A * (L0 / (96 * L1 ^ 2)) = L0 * c.A / (96 * L1 ^ 2) := by ring
    rw [h2, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have hkB : (k : ℝ) ≤ bigB q :=
    hk.trans (omega_bound hL0 hL1 hq hR hSle hAq)
  refine ⟨S + weight L0 L1 c.A ‖g y‖ ^ 2 * ‖g y‖ ^ 2, k + 1, 0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [accept_eq]; exact hI'
  · rw [accept_eq]; simp only [coreOf]; push_cast; linarith
  · push_cast; linarith
  · push_cast
    have hM : (0 : ℝ) ≤ probeCap q := by positivity
    nlinarith
  · rw [accept_eq]; exact rfl

theorem phase_step {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (hq : q = L1 * R) (hR : 0 < R) {n : ℕ} {ph : Phase E}
    (hinv : PhInv f g L0 L1 q R u n ph) :
    (∃ ph', T L0 L1 g (.first ph) = .first ph' ∧ PhInv f g L0 L1 q R u (n + 1) ph') ∨
    (∃ z, T L0 L1 g (.first ph) = exitState L0 z ∧ GoodExit g L0 L1 R u z) := by
  classical
  have hL0 := H.L0_pos
  have hqpos : 0 < q := by rw [hq]; positivity
  have hτ : 0 < threshold L0 L1 := by unfold threshold; positivity
  obtain ⟨S, k, j, hI, hk, hkB, hn, hsub⟩ := hinv
  rw [T_first]
  cases ph with
  | queryX c =>
    simp only [coreOf] at hI hk
    simp only [SubInv] at hsub
    subst hsub
    simp only [phaseQuery, phaseUpdate]
    unfold stepX
    split_ifs with hexit
    · right
      exact ⟨c.x, rfl, hI.x_dist, hexit⟩
    · left
      push Not at hexit
      refine ⟨_, rfl, S, k, 1, hI, hk, hkB, ?_, rfl, hexit, rfl⟩
      push_cast at hn ⊢; linarith
  | queryV c gx =>
    simp only [coreOf] at hI hk
    obtain ⟨hgx, hgxτ, hj⟩ := hsub
    subst hgx hj
    simp only [phaseQuery, phaseUpdate]
    unfold stepV
    have hgxpos : 0 < ‖g c.x‖ := lt_trans hτ hgxτ
    split_ifs with hexit hv hx
    · right
      exact ⟨c.v, rfl, hI.v_dist hR.le H.min, hexit⟩
    · left
      push Not at hexit
      refine ⟨_, rfl, ?_⟩
      have hs0 : 0 ≤ slope g c 0 := by unfold slope; rw [seg_zero]; exact hv
      have hfy : f c.v ≤ f c.x := by
        have := seg_f_le H c (t := 0) (by norm_num) hs0
        rwa [seg_zero] at this
      have hB : ⟪g c.v, c.v - c.v⟫ ≤ ‖g c.v‖ ^ 2 / (16 * localCurvature L0 L1 ‖g c.v‖) := by
        rw [sub_self, inner_zero_right]; unfold localCurvature; positivity
      exact accept_ledger H hL1 hq hR hI hk hn (by push_cast; linarith [(Nat.cast_nonneg (probeCap q) : (0:ℝ) ≤ probeCap q)])
        hgxτ (lt_trans hτ hexit) (hI.v_dist hR.le H.min) hfy hB
    · left
      push Not at hexit hv
      refine ⟨_, rfl, ?_⟩
      exact accept_ledger H hL1 hq hR hI hk hn (by push_cast; linarith [(Nat.cast_nonneg (probeCap q) : (0:ℝ) ≤ probeCap q)])
        hgxτ hgxpos hI.x_dist le_rfl hx
    · left
      push Not at hexit hv hx
      have hP : PInv f g L0 L1 u c 0 1 := by
        refine ⟨le_rfl, by norm_num, le_rfl, ?_, ?_⟩
        · unfold slope; rw [seg_zero]; exact hv
        · unfold slope; rw [seg_one]; intro hc; rw [one_mul] at hc; exact absurd hc (not_le.mpr hx)
      have hG1 : threshold L0 L1 < ‖g (seg c 1)‖ := by rw [seg_one]; exact hgxτ
      have hcap := width_cap H hL1 hq hR hI hP hG1 (m := 0) (by norm_num)
      refine ⟨_, rfl, S, k, 2, hI, hk, hkB, ?_, rfl, rfl, hgxτ, hexit, hP, hG1, 0, rfl, by norm_num, hcap⟩
      push_cast at hn ⊢; linarith
  | probe c gx gv tm tp =>
    simp only [coreOf] at hI hk
    obtain ⟨hgx, hgv, hgxτ, hgvτ, hP, hGtp, m, hj, hm, hmcap⟩ := hsub
    subst hgx hgv hj
    simp only [phaseQuery, phaseUpdate]
    unfold stepProbe
    simp only
    rw [probePoint_eq]
    set t := (tm + tp) / 2 with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith [hP.tm_nonneg, hP.lt]
    have ht1 : t ≤ 1 := by rw [ht]; linarith [hP.tp_le, hP.lt]
    have htmt : tm < t := by rw [ht]; linarith [hP.lt]
    have http : t < tp := by rw [ht]; linarith [hP.lt]
    have hzd : ‖seg c t - u‖ ≤ R := hI.segment_dist hR.le H.min ht0 ht1
    split_ifs with hexit hneg hacc
    · right
      exact ⟨seg c t, rfl, hzd, hexit⟩
    · left
      push Not at hexit
      have hP' : PInv f g L0 L1 u c t tp := ⟨ht0, http, hP.tp_le, hneg, hP.fail⟩
      have hm' : tp - t = (1 / 2) ^ (m + 1) := by
        rw [pow_succ, ← hm, ht]; ring
      have hcap := width_cap H hL1 hq hR hI hP' hGtp hm'
      refine ⟨_, rfl, S, k, 2 + (m + 1), hI, hk, hkB, ?_, rfl, rfl, hgxτ, hgvτ, hP', hGtp, m + 1, rfl, hm', hcap⟩
      push_cast at hn ⊢; linarith
    · left
      push Not at hexit hneg
      refine ⟨_, rfl, ?_⟩
      have hs : 0 ≤ slope g c t := hneg
      have hfy : f (seg c t) ≤ f c.x := seg_f_le H c ht1 hs
      have hB : ⟪g (seg c t), seg c t - c.v⟫ ≤
          ‖g (seg c t)‖ ^ 2 / (16 * localCurvature L0 L1 ‖g (seg c t)‖) := by
        rw [seg_inner_v]; exact hacc
      have hj1 : ((2 + m : ℕ) : ℝ) + 1 ≤ 2 + probeCap q := by
        have : (m + 1 : ℝ) ≤ probeCap q := by exact_mod_cast hmcap
        push_cast; linarith
      exact accept_ledger H hL1 hq hR hI hk hn hj1 hgxτ (lt_trans hτ hexit) hzd hfy hB
    · left
      push Not at hexit hneg
      have hP' : PInv f g L0 L1 u c tm t := ⟨hP.tm_nonneg, htmt, ht1, hP.neg, hacc⟩
      have hm' : t - tm = (1 / 2) ^ (m + 1) := by
        rw [pow_succ, ← hm, ht]; ring
      have hcap := width_cap H hL1 hq hR hI hP' hexit hm'
      refine ⟨_, rfl, S, k, 2 + (m + 1), hI, hk, hkB, ?_, rfl, rfl, hgxτ, hgvτ, hP', hexit, m + 1, rfl, hm', hcap⟩
      push_cast at hn ⊢; linarith


noncomputable def phaseSteps (q : ℝ) : ℝ := (bigB q + 1) * (2 + probeCap q) + 1 + probeCap q

omit [CompleteSpace E] in
lemma PhInv.steps_le {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u : E} {n : ℕ} {ph : Phase E}
    (hinv : PhInv f g L0 L1 q R u n ph) : (n : ℝ) ≤ phaseSteps q := by
  obtain ⟨S, k, j, _, _, hkB, hn, hsub⟩ := hinv
  have hj : (j : ℝ) ≤ 1 + probeCap q := by
    cases ph with
    | queryX c =>
      simp only [SubInv] at hsub; subst hsub
      have : (0:ℝ) ≤ probeCap q := Nat.cast_nonneg _
      push_cast; linarith
    | queryV c gx =>
      obtain ⟨_, _, hj⟩ := hsub; subst hj
      have : (0:ℝ) ≤ probeCap q := Nat.cast_nonneg _
      push_cast; linarith
    | probe c gx gv tm tp =>
      obtain ⟨_, _, _, _, _, _, m, hj, _, hm⟩ := hsub
      subst hj
      have : (m + 1 : ℝ) ≤ probeCap q := by exact_mod_cast hm
      push_cast; linarith
  have hM : (0 : ℝ) ≤ probeCap q := by positivity
  unfold phaseSteps
  nlinarith

def initState (x0 : E) : State E := .first (.queryX ⟨0, x0, x0⟩)

lemma init_inv {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u x0 : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (hq : q = L1 * R) (hR : 0 < R) (hdist : ‖x0 - u‖ ≤ R) :
    PhInv f g L0 L1 q R u 0 (.queryX ⟨0, x0, x0⟩) := by
  have hL0 := H.L0_pos
  have hqpos : 0 < q := by rw [hq]; positivity
  refine ⟨0, 0, 0, ⟨le_rfl, le_rfl, ?_, hdist⟩, ?_, ?_, by simp, rfl⟩
  · simp only [coreOf, zero_mul, zero_div, zero_add]
    have : ‖x0 - u‖ ^ 2 ≤ R ^ 2 := by
      have := norm_nonneg (x0 - u)
      nlinarith
    linarith
  · simp only [coreOf, omega, ind, lnm, Nat.cast_zero]
    have hamin := aMin_pos (q := q) hL0
    simp [max_eq_right hamin.le, not_le.mpr hamin]
  · have hB : 0 ≤ bigB q := by
      unfold bigB
      have := theta_pos hqpos.le
      have hlog : 0 ≤ Real.log (336 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
      positivity
    push_cast; linarith

theorem run_dichotomy {f : E → ℝ} {g : E → E} {L0 L1 q R : ℝ} {u x0 : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (hq : q = L1 * R) (hR : 0 < R) (hdist : ‖x0 - u‖ ≤ R) (n : ℕ) :
    (∃ ph, (T L0 L1 g)^[n] (initState x0) = .first ph ∧ PhInv f g L0 L1 q R u n ph) ∨
    (∃ z c1, c1 ≤ n ∧ GoodExit g L0 L1 R u z ∧ (c1 : ℝ) ≤ phaseSteps q + 1 ∧
      (T L0 L1 g)^[n] (initState x0) = (T L0 L1 g)^[n - c1] (exitState L0 z)) := by
  induction n with
  | zero =>
    left
    exact ⟨_, rfl, init_inv H hL1 hq hR hdist⟩
  | succ n ih =>
    rcases ih with ⟨ph, hstate, hinv⟩ | ⟨z, c1, hc1, hz, hc1le, hstate⟩
    · rw [Function.iterate_succ_apply', hstate]
      rcases phase_step H hL1 hq hR hinv with ⟨ph', hstep, hinv'⟩ | ⟨z, hstep, hz⟩
      · left; exact ⟨ph', hstep, hinv'⟩
      · right
        refine ⟨z, n + 1, le_rfl, hz, ?_, ?_⟩
        · have := hinv.steps_le; push_cast; linarith
        · rw [hstep, Nat.sub_self]; rfl
    · right
      refine ⟨z, c1, by omega, hz, hc1le, ?_⟩
      rw [Function.iterate_succ_apply', hstate, ← Function.iterate_succ_apply' (T L0 L1 g),
        show n + 1 - c1 = (n - c1) + 1 by omega]

noncomputable def S2 (g : E → E) (st : ParameterFreeGeneralized.State E) :
    ParameterFreeGeneralized.State E :=
  secondUpdate st (g (secondQuery st))

omit [CompleteSpace E] in
lemma T_second_iterate (L0 L1 : ℝ) (g : E → E) (st : ParameterFreeGeneralized.State E) (r : ℕ) :
    (T L0 L1 g)^[r] (.second st) = .second ((S2 g)^[r] st) := by
  induction r generalizing st with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_second]
    exact ih _

omit [CompleteSpace E] in
lemma S2_two (g : E → E) (s : ParameterFreeGeneralized.Core E) :
    (S2 g)^[2] (.ready s) = .ready (ParameterFreeGeneralized.trial g s) := rfl

omit [CompleteSpace E] in
lemma S2_even (g : E → E) (s : ParameterFreeGeneralized.Core E) (i : ℕ) :
    (S2 g)^[2 * i] (.ready s) = .ready ((ParameterFreeGeneralized.trial g)^[i] s) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 + 2 * i by omega, Function.iterate_add_apply, ih, S2_two,
      Function.iterate_succ_apply']

omit [CompleteSpace E] in
lemma output_second (g : E → E) (s : ParameterFreeGeneralized.Core E) (r : ℕ) :
    stateOutput (E := E) (.second ((S2 g)^[r] (.ready s))) =
      ((ParameterFreeGeneralized.trial g)^[r / 2] s).x := by
  obtain ⟨i, hi⟩ : ∃ i, r = 2 * i ∨ r = 2 * i + 1 := ⟨r / 2, by omega⟩
  rcases hi with h | h
  · subst h
    rw [S2_even, show 2 * i / 2 = i by omega]
    rfl
  · subst h
    rw [Function.iterate_succ_apply', S2_even, show (2 * i + 1) / 2 = i by omega]
    rfl

end OracleTemplate.RadiusFreeSherpa
