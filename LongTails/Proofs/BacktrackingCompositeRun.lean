import LongTails.Proofs.BacktrackingCompositeStep
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

open CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def gfun (Ls L1 R A : ℝ) : ℝ :=
  min (A / (8 * Ls * A + 96 * L1 ^ 2 * R ^ 2)) (A / (4 * (1 + 32 * L1 * R) ^ 2))

lemma gfun_pos {Ls L1 R A : ℝ} (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) :
    0 < gfun Ls L1 R A := by
  unfold gfun
  exact lt_min (by positivity) (by positivity)

lemma gfun_mono {Ls L1 R A B : ℝ} (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A)
    (hAB : A ≤ B) : gfun Ls L1 R A ≤ gfun Ls L1 R B := by
  unfold gfun
  have hB : 0 < B := hA.trans_le hAB
  apply min_le_min
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 96) (sq_nonneg L1)) (sq_nonneg R)]
  · exact div_le_div_of_nonneg_right hAB (by positivity)

lemma gfun_double {Ls L1 R A B : ℝ} (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hB0 : 0 < B) : gfun Ls L1 R B ≤ 2 * gfun Ls L1 R A := by
  have h1 := gfun_mono hLs hL1 hR hB0 hB
  refine h1.trans ?_
  unfold gfun
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  apply min_le_min
  · calc 2 * A / (8 * Ls * (2 * A) + 96 * L1 ^ 2 * R ^ 2)
        ≤ 2 * A / (8 * Ls * A + 96 * L1 ^ 2 * R ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [mul_pos hLs hA])
      _ = 2 * (A / (8 * Ls * A + 96 * L1 ^ 2 * R ^ 2)) := by ring
  · rw [mul_div_assoc']

lemma gfun_le_quarter {Ls L1 R A : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 ≤ A) :
    gfun Ls L1 R A ≤ A / 4 := by
  unfold gfun
  refine (min_le_right _ _).trans ?_
  apply div_le_div_of_nonneg_left hA (by norm_num)
  nlinarith [mul_nonneg hL1 hR.le]

lemma gfun_le_inv {Ls L1 R A : ℝ} (hLs : 0 < Ls) (hA : 0 < A) :
    gfun Ls L1 R A ≤ 1 / (8 * Ls) := by
  unfold gfun
  refine (min_le_left _ _).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 96) (sq_nonneg L1)) (sq_nonneg R)]

lemma gfun_le_cap {Ls L1 R A : ℝ} :
    gfun Ls L1 R A ≤ A / (4 * (1 + 32 * L1 * R) ^ 2) := min_le_right _ _

lemma gfun_le_curv {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R G : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) (hG : ‖g xs‖ ≤ G) {s : TState E}
    (hs : InvT f ψ Q xs R s) (hA : 0 < s.A) :
    gfun (L0 + L1 * G) L1 R s.A ≤ 1 / (4 * (L0 + L1 * ‖g s.x‖)) := by
  have hcurv := curvature_bound hyp hxs hmin hG (inv_of_invT hs hA)
  simp only at hcurv
  have hL0 := hyp.hL0
  have hL1 := hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  unfold gfun
  refine (min_le_left _ _).trans ?_
  have hM : 0 < L0 + L1 * ‖g s.x‖ := by positivity
  have hden : 0 < 8 * (L0 + L1 * G) * s.A + 96 * L1 ^ 2 * R ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have h1 : 4 * (L0 + L1 * ‖g s.x‖) * s.A ≤ 8 * (L0 + L1 * G) * s.A + 96 * L1 ^ 2 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right hcurv hA.le
    rw [add_mul (2 * (L0 + L1 * G)) (24 * (L1 ^ 2 * R ^ 2) / s.A) s.A,
      div_mul_cancel₀ _ hA.ne'] at this
    nlinarith
  nlinarith

lemma reject_gt {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R G : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) (hG : ‖g xs‖ ≤ G) {s : TState E}
    (hs : InvT f ψ Q xs R s) (hA : 0 < s.A) (hrej : ¬ Accepts g prox s) :
    gfun (L0 + L1 * G) L1 R s.A < s.h := by
  by_contra hle
  push Not at hle
  apply hrej
  refine accepts_of_small hyp hR hxs hmin hs hA (hle.trans ?_) (hle.trans ?_)
  · exact gfun_le_curv hyp hxs hmin hG hs hA
  · exact gfun_le_cap

noncomputable def run (g : E → E) (prox : ℝ → E → E → E) (x0 : E) (h0 : ℝ) : ℕ → TState E
  | 0 => ⟨0, x0, x0, h0⟩
  | n + 1 => trial g prox (run g prox x0 h0 n)

open Classical in
noncomputable def acc (g : E → E) (prox : ℝ → E → E → E) (x0 : E) (h0 : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => acc g prox x0 h0 n + if Accepts g prox (run g prox x0 h0 n) then 1 else 0

omit [CompleteSpace E] in
lemma acc_le (g : E → E) (prox : ℝ → E → E → E) (x0 : E) (h0 : ℝ) (n : ℕ) :
    acc g prox x0 h0 n ≤ n := by
  induction n with
  | zero => simp [acc]
  | succ n ih => simp only [acc]; split_ifs <;> omega

omit [CompleteSpace E] in
lemma run_h_mul (g : E → E) (prox : ℝ → E → E → E) (x0 : E) (h0 : ℝ) (n : ℕ) :
    (run g prox x0 h0 n).h * 2 ^ n = h0 * 4 ^ (acc g prox x0 h0 n) := by
  induction n with
  | zero => simp [run, acc]
  | succ n ih =>
    simp only [run, acc]
    by_cases hacc : Accepts g prox (run g prox x0 h0 n)
    · rw [trial_accept hacc]; simp only [hacc, ite_true, pow_succ]
      linear_combination 4 * ih
    · rw [trial_reject hacc]; simp only [hacc, ite_false, add_zero, pow_succ]
      linear_combination ih


structure Base (f ψ : E → ℝ) (g : E → E) (Q : Set E) (prox : ℝ → E → E → E)
    (L0 L1 R G Δ : ℝ) (xs x0 : E) (h0 : ℝ) : Prop where
  hyp : Hyp f ψ g Q prox L0 L1
  hR : 0 < R
  hG : ‖g xs‖ ≤ G
  hΔ : 0 < Δ
  hh0 : 0 < h0
  hxs : xs ∈ Q
  hmin : IsMinOn (fun x => f x + ψ x) Q xs
  hx0 : x0 ∈ Q
  hdist : ‖x0 - xs‖ ≤ R
  hgap : f x0 + ψ x0 - (f xs + ψ xs) ≤ Δ

variable {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
  {L0 L1 R G Δ : ℝ} {xs x0 : E} {h0 : ℝ}

lemma run_inv (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) (n : ℕ) :
    InvT f ψ Q xs R (run g prox x0 h0 n) := by
  induction n with
  | zero =>
    unfold InvT
    simp only [run]
    refine ⟨le_rfl, b.hx0, b.hx0, ?_, by linarith [b.hdist, b.hR], by linarith [b.hdist, b.hR],
      b.hh0⟩
    simp only [zero_mul, zero_add]
    have := b.hdist
    nlinarith [norm_nonneg (x0 - xs)]
  | succ n ih => exact trial_inv b.hyp b.hR b.hxs b.hmin ih

noncomputable def hbar (Ls L1 Δ : ℝ) : ℝ := 1 / (12 * Ls + 176 * L1 ^ 2 * Δ)

noncomputable def Amin (Ls L1 Δ h0 : ℝ) : ℝ := min h0 (hbar Ls L1 Δ / 2)

noncomputable def hlow (Ls L1 R Δ h0 : ℝ) : ℝ :=
  min (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0)) / 2

def Phase0 (x0 : E) (h0 hb : ℝ) (s : TState E) (k : ℕ) : Prop :=
  s.A = 0 ∧ s.x = x0 ∧ s.z = x0 ∧ k = 0 ∧ (s.h = h0 ∨ hb / 2 < s.h)

def Phase1 (Ls L1 R Am : ℝ) (s : TState E) (k : ℕ) : Prop :=
  0 < s.A ∧ Am ≤ s.A ∧ min (2 ^ k * Am) (gfun Ls L1 R s.A / 2) ≤ s.h ∧ 1 ≤ k

lemma run_phase (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) (n : ℕ) :
    Phase0 x0 h0 (hbar (L0 + L1 * G) L1 Δ) (run g prox x0 h0 n) (acc g prox x0 h0 n) ∨
      Phase1 (L0 + L1 * G) L1 R (Amin (L0 + L1 * G) L1 Δ h0) (run g prox x0 h0 n)
        (acc g prox x0 h0 n) := by
  have hL0 := b.hyp.hL0
  have hL1 := b.hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans b.hG
  set Ls := L0 + L1 * G with hLs
  have hLs : 0 < Ls := by positivity
  have hb : 0 < hbar Ls L1 Δ := by unfold hbar; have := b.hΔ; positivity
  have hAm : 0 < Amin Ls L1 Δ h0 := lt_min b.hh0 (by positivity)
  induction n with
  | zero => left; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
  | succ n ih =>
    have hinv := run_inv b n
    obtain ⟨s, hsdef⟩ : ∃ s, s = run g prox x0 h0 n := ⟨_, rfl⟩
    rw [← hsdef] at hinv ih
    have hh : 0 < s.h := hinv.2.2.2.2.2.2
    simp only [run, acc]
    rw [← hsdef]
    rcases ih with ⟨hA0, hx, hz, hk, hhc⟩ | ⟨hA, hAm', hJ, hk⟩
    · by_cases hacc : Accepts g prox s
      · right
        rw [trial_accept hacc]
        simp only [hacc, ite_true, hk]
        have ha : trialA s = s.h := by simp only [trialA, hA0]; exact stepWeight_zero hh.le
        rw [hA0, ha, zero_add]
        have hAm1 : Amin Ls L1 Δ h0 ≤ s.h := by
          rcases hhc with h | h
          · rw [h]; exact min_le_left _ _
          · exact (min_le_right _ _).trans h.le
        refine ⟨hh, hAm1, ?_, by norm_num⟩
        refine (min_le_right _ _).trans ?_
        have := gfun_le_quarter (Ls := Ls) hL1 b.hR hh.le
        linarith
      · left
        rw [trial_reject hacc]
        simp only [hacc, ite_false, add_zero]
        refine ⟨hA0, hx, hz, hk, Or.inr ?_⟩
        have hgt : hbar Ls L1 Δ < s.h := by
          by_contra hle
          push Not at hle
          apply hacc
          refine accepts_first b.hyp b.hxs b.hmin b.hG b.hΔ hinv hA0 ?_ ?_
          · rw [hz]; exact b.hgap
          · simpa [hbar] using hle
        linarith
    · right
      by_cases hacc : Accepts g prox s
      · rw [trial_accept hacc]
        simp only [hacc, ite_true]
        set a := trialA s with hadef
        have ha : 0 < a := stepWeight_pos hh hA.le
        have hA' : 0 < s.A + a := by positivity
        refine ⟨hA', by linarith, ?_, by omega⟩
        have hJ2 : min (2 ^ (acc g prox x0 h0 n + 1) * Amin Ls L1 Δ h0) (gfun Ls L1 R s.A) ≤
            2 * s.h := by
          have := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ) ≤ 2)
          rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at this
          convert this using 2
          · rw [pow_succ]; ring
          · ring
        by_cases hcase : s.A + a ≤ 2 * s.A
        · have hg := gfun_double hLs hL1 b.hR hA hcase hA'
          refine le_trans ?_ hJ2
          apply min_le_min le_rfl
          linarith
        · push Not at hcase
          have hgt : s.A < a := by linarith
          have ha2 : a ≤ 2 * s.h := stepWeight_le_two_mul hh.le hA.le hgt
          have h8 := gfun_le_quarter (Ls := Ls) hL1 b.hR hA'.le
          refine (min_le_right _ _).trans ?_
          linarith
      · rw [trial_reject hacc]
        simp only [hacc, ite_false, add_zero]
        refine ⟨hA, hAm', ?_, hk⟩
        have := reject_gt b.hyp b.hR b.hxs b.hmin b.hG hinv hA hacc
        refine (min_le_right _ _).trans ?_
        linarith

lemma run_h_ge (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) (n : ℕ) :
    hlow (L0 + L1 * G) L1 R Δ h0 ≤ (run g prox x0 h0 n).h := by
  have hL0 := b.hyp.hL0
  have hL1 := b.hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans b.hG
  set Ls := L0 + L1 * G with hLs
  have hLs : 0 < Ls := by positivity
  have hb : 0 < hbar Ls L1 Δ := by unfold hbar; have := b.hΔ; positivity
  have hAm : 0 < Amin Ls L1 Δ h0 := lt_min b.hh0 (by positivity)
  have hg : 0 < gfun Ls L1 R (Amin Ls L1 Δ h0) := gfun_pos hLs hL1 b.hR hAm
  rcases run_phase b n with ⟨-, -, -, -, hhc⟩ | ⟨hA, hAm', hJ, hk⟩
  · rcases hhc with h | h
    · rw [h]
      unfold hlow
      have h1 : gfun Ls L1 R (Amin Ls L1 Δ h0) ≤ h0 := by
        have := gfun_le_quarter (Ls := Ls) hL1 b.hR hAm.le
        have h2 : Amin Ls L1 Δ h0 ≤ h0 := min_le_left _ _
        linarith
      have := min_le_right (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0))
      linarith
    · unfold hlow
      have := min_le_left (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0))
      linarith
  · refine le_trans ?_ hJ
    unfold hlow
    apply le_min
    · have h1 : (1 : ℝ) ≤ 2 ^ (acc g prox x0 h0 n) := one_le_pow₀ (by norm_num)
      have := min_le_right (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0))
      have h8 := gfun_le_quarter (Ls := Ls) hL1 b.hR hAm.le
      nlinarith
    · have := min_le_right (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0))
      have hmono := gfun_mono hLs hL1 b.hR hAm hAm'
      linarith

lemma rej_bound (b : Base f ψ g Q prox L0 L1 R G Δ xs x0 h0) (n : ℕ) :
    (n : ℝ) ≤ 2 * acc g prox x0 h0 n +
      Real.logb 2 (h0 / hlow (L0 + L1 * G) L1 R Δ h0) := by
  have hL0 := b.hyp.hL0
  have hL1 := b.hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans b.hG
  set Ls := L0 + L1 * G with hLs
  have hLs : 0 < Ls := by positivity
  have hb : 0 < hbar Ls L1 Δ := by unfold hbar; have := b.hΔ; positivity
  have hAm : 0 < Amin Ls L1 Δ h0 := lt_min b.hh0 (by positivity)
  have hg : 0 < gfun Ls L1 R (Amin Ls L1 Δ h0) := gfun_pos hLs hL1 b.hR hAm
  have hlow0 : 0 < hlow Ls L1 R Δ h0 := by unfold hlow; positivity
  have hmul := run_h_mul g prox x0 h0 n
  have hge := run_h_ge b n
  have hh : 0 < (run g prox x0 h0 n).h := (run_inv b n).2.2.2.2.2.2
  set k := acc g prox x0 h0 n
  have hpow : hlow Ls L1 R Δ h0 * 2 ^ n ≤ h0 * 4 ^ k := by
    rw [← hmul]; exact mul_le_mul_of_nonneg_right hge (by positivity)
  have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [h4] at hpow
  have hratio : (2 : ℝ) ^ n / 2 ^ (2 * k) ≤ h0 / hlow Ls L1 R Δ h0 := by
    rw [div_le_div_iff₀ (by positivity) hlow0]
    linarith
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hratio
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hlog
  push_cast at hlog
  linarith

end OracleTemplate.CompositeParameterFree
