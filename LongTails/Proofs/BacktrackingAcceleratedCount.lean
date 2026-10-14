import LongTails.Proofs.BacktrackingAcceleratedStep
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ParameterFreeGeneralized

open LongTails.Setups.GeneralizedSmoothParameterFree

lemma growth_geometric {A h a σ : ℝ} (hA : 0 < A) (ha : 0 < a) (hσ : 0 < σ)
    (hsq : a ^ 2 = h * (A + a)) (hh : A ≤ h * σ ^ 2) : A ≤ a * σ := by
  by_contra hcon
  push Not at hcon
  have h1 : (a * σ) ^ 2 < A ^ 2 := pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
  have h2 : A * (A + a) ≤ h * σ ^ 2 * (A + a) :=
    mul_le_mul_of_nonneg_right hh (by positivity)
  have h3 : (a * σ) ^ 2 = h * σ ^ 2 * (A + a) := by
    rw [mul_pow, hsq]
    ring
  have h4 := mul_pos hA ha
  nlinarith

lemma growth_sqrt {A h a c : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hc : 0 < c)
    (hsq : a ^ 2 = h * (A + a)) (hh : c ≤ h) :
    Real.sqrt A + Real.sqrt c / 2 ≤ Real.sqrt (A + a) := by
  have hr : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hk : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hr0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hk0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  have hge : c * (A + a) ≤ a ^ 2 := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hh (by positivity)
  have key : Real.sqrt A * Real.sqrt c + c / 4 ≤ a := by
    by_contra hcon
    push Not at hcon
    rcases le_or_gt (c / 2) a with h1 | h1
    · have h2 : a - c / 2 < Real.sqrt A * Real.sqrt c := by linarith
      have h3 : (a - c / 2) ^ 2 < (Real.sqrt A * Real.sqrt c) ^ 2 :=
        pow_lt_pow_left₀ h2 (by linarith) two_ne_zero
      have h4 : (Real.sqrt A * Real.sqrt c) ^ 2 = A * c := by rw [mul_pow, hr, hk]
      nlinarith
    · have h2 : c * a ≤ a ^ 2 := by nlinarith [mul_nonneg hc.le hA]
      have h3 : 0 < a * (c - a) := mul_pos ha (by linarith)
      nlinarith
  apply Real.le_sqrt_of_sq_le
  nlinarith

noncomputable def sigma (L1 R : ℝ) : ℝ := 2 + 13 * (L1 * R)

noncomputable def cap (L0 : ℝ) : ℝ := 1 / (64 * L0)

noncomputable def progress (σ c η A : ℝ) : ℝ :=
  (1 + σ) * (Real.log (min A (c * σ ^ 2)) - Real.log (min η (c * σ ^ 2))) +
    2 * (Real.sqrt A - Real.sqrt η) / Real.sqrt c + (if c * σ ^ 2 ≤ A then 1 else 0)

lemma progress_nonneg {σ c η A : ℝ} (hσ : 2 ≤ σ) (hc : 0 < c) (hη : 0 < η) (hηA : η ≤ A) :
    0 ≤ progress σ c η A := by
  unfold progress
  have hX : 0 < c * σ ^ 2 := by positivity
  have h1 : Real.log (min η (c * σ ^ 2)) ≤ Real.log (min A (c * σ ^ 2)) :=
    Real.log_le_log (lt_min hη hX) (min_le_min hηA le_rfl)
  have h2 : Real.sqrt η ≤ Real.sqrt A := Real.sqrt_le_sqrt hηA
  have h3 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h4 : 0 ≤ 2 * (Real.sqrt A - Real.sqrt η) / Real.sqrt c :=
    div_nonneg (by linarith) h3.le
  have h5 : (0 : ℝ) ≤ if c * σ ^ 2 ≤ A then 1 else 0 := by split_ifs <;> norm_num
  have h6 : 0 ≤ (1 + σ) * (Real.log (min A (c * σ ^ 2)) - Real.log (min η (c * σ ^ 2))) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

lemma progress_le {σ c η A : ℝ} (hσ : 2 ≤ σ) (hc : 0 < c) (hη : 0 < η) (hA : 0 < A) :
    progress σ c η A ≤
      (1 + σ) * Real.log (1 + c * σ ^ 2 / η) + 2 * Real.sqrt A / Real.sqrt c + 1 := by
  unfold progress
  have hX : 0 < c * σ ^ 2 := by positivity
  have h3 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h1 : Real.log (min A (c * σ ^ 2)) - Real.log (min η (c * σ ^ 2)) ≤
      Real.log (1 + c * σ ^ 2 / η) := by
    have hup : Real.log (min A (c * σ ^ 2)) ≤ Real.log (c * σ ^ 2) :=
      Real.log_le_log (lt_min hA hX) (min_le_right _ _)
    have hq : 0 < c * σ ^ 2 / η := by positivity
    rcases le_total η (c * σ ^ 2) with h | h
    · rw [min_eq_left h]
      have : Real.log (c * σ ^ 2) - Real.log η = Real.log (c * σ ^ 2 / η) :=
        (Real.log_div hX.ne' hη.ne').symm
      have h5 : Real.log (c * σ ^ 2 / η) ≤ Real.log (1 + c * σ ^ 2 / η) :=
        Real.log_le_log hq (by linarith)
      linarith
    · rw [min_eq_right h]
      have : 0 ≤ Real.log (1 + c * σ ^ 2 / η) := Real.log_nonneg (by linarith)
      linarith
  have h2 : 2 * (Real.sqrt A - Real.sqrt η) / Real.sqrt c ≤ 2 * Real.sqrt A / Real.sqrt c := by
    apply div_le_div_of_nonneg_right _ h3.le
    linarith [Real.sqrt_nonneg η]
  have h5 : (if c * σ ^ 2 ≤ A then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h6 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 + σ)
  linarith

lemma progress_accept {σ c η A h a : ℝ} (hσ : 2 ≤ σ) (hc : 0 < c) (hη : 0 < η)
    (hηA : η ≤ A) (ha : 0 < a) (hsq : a ^ 2 = h * (A + a))
    (hθ : min c (A / σ ^ 2) ≤ h) :
    progress σ c η A + 1 ≤ progress σ c η (A + a) := by
  have hA : 0 < A := hη.trans_le hηA
  have hσ0 : 0 < σ := by linarith
  have hX : 0 < c * σ ^ 2 := by positivity
  have h3 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsqrt : Real.sqrt A ≤ Real.sqrt (A + a) := Real.sqrt_le_sqrt (by linarith)
  unfold progress
  rcases le_or_gt (c * σ ^ 2) A with hXA | hXA
  · have hcA : c ≤ A / σ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact hXA
    have hch : c ≤ h := by
      rw [min_eq_left hcA] at hθ
      exact hθ
    have hg := growth_sqrt hA.le ha hc hsq hch
    rw [ite_eq_left hXA, ite_eq_left (by linarith : c * σ ^ 2 ≤ A + a), min_eq_right hXA,
      min_eq_right (by linarith : c * σ ^ 2 ≤ A + a)]
    have h5 : 1 ≤ 2 * (Real.sqrt (A + a) - Real.sqrt A) / Real.sqrt c := by
      rw [le_div_iff₀ h3]
      linarith
    have e : 2 * (Real.sqrt (A + a) - Real.sqrt η) / Real.sqrt c =
        2 * (Real.sqrt A - Real.sqrt η) / Real.sqrt c +
          2 * (Real.sqrt (A + a) - Real.sqrt A) / Real.sqrt c := by ring
    linarith
  · have hAc : A / σ ^ 2 < c := by
      rw [div_lt_iff₀ (by positivity)]
      exact hXA
    have hAh : A ≤ h * σ ^ 2 := by
      rw [min_eq_right hAc.le] at hθ
      rwa [div_le_iff₀ (by positivity)] at hθ
    have hgeo := growth_geometric hA ha hσ0 hsq hAh
    rw [ite_eq_right (not_le.mpr hXA), min_eq_left hXA.le]
    have hsq2 : 2 * (Real.sqrt A - Real.sqrt η) / Real.sqrt c ≤
        2 * (Real.sqrt (A + a) - Real.sqrt η) / Real.sqrt c :=
      div_le_div_of_nonneg_right (by linarith) h3.le
    rcases le_or_gt (c * σ ^ 2) (A + a) with hXA' | hXA'
    · rw [ite_eq_left hXA', min_eq_right hXA']
      have hlog : Real.log A ≤ Real.log (c * σ ^ 2) := Real.log_le_log hA hXA.le
      have := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hlog (Real.log (min η (c * σ ^ 2)))) (by linarith : 0 ≤ 1 + σ)
      linarith
    · rw [ite_eq_right (not_le.mpr hXA'), min_eq_left hXA'.le]
      have hAa : 0 < A + a := by linarith
      have hratio : A / (A + a) ≤ σ / (σ + 1) := by
        rw [div_le_div_iff₀ hAa (by linarith)]
        nlinarith
      have hl := Real.log_le_sub_one_of_pos (div_pos hA hAa)
      rw [Real.log_div hA.ne' hAa.ne'] at hl
      have hσ1 : σ + 1 ≠ 0 := by linarith
      have hs1 : σ / (σ + 1) - 1 = -(1 / (σ + 1)) := by
        field_simp
        ring
      have hdiff : 1 / (σ + 1) ≤ Real.log (A + a) - Real.log A := by linarith
      have hmul := mul_le_mul_of_nonneg_left hdiff (by linarith : 0 ≤ 1 + σ)
      have hone : (1 + σ) * (1 / (σ + 1)) = 1 := by
        field_simp
        ring
      linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def eta (g : E → E) (x0 : E) (L0 L1 h0 : ℝ) : ℝ :=
  min h0 (1 / (8 * (L0 + L1 * ‖g x0‖)))

structure Progress (f : E → ℝ) (g : E → E) (u x0 : E) (L0 L1 R h0 : ℝ) (n : ℕ)
    (s : Core E) : Prop where
  inv : Inv f u R s
  count : ∃ acc rej : ℕ, acc + rej = n ∧ s.h * 2 ^ rej = h0 * 2 ^ acc ∧
    ((s.A = 0 ∧ acc = 0 ∧ s.v = x0 ∧ eta g x0 L0 L1 h0 ≤ s.h) ∨
      (eta g x0 L0 L1 h0 ≤ s.A ∧ min (cap L0) (s.A / sigma L1 R ^ 2) ≤ s.h ∧
        (acc : ℝ) ≤ 1 + progress (sigma L1 R) (cap L0) (eta g x0 L0 L1 h0) s.A))

lemma progress_step {f : E → ℝ} {g : E → E} {L0 L1 R h0 : ℝ} {u x0 : E}
    (H : Hyp f g L0 L1 u) (hR : 0 < R) (hh0 : 0 < h0) {n : ℕ} {s : Core E}
    (hP : Progress f g u x0 L0 L1 R h0 n s) :
    Progress f g u x0 L0 L1 R h0 (n + 1) (trial g s) := by
  obtain ⟨hI, acc, rej, hn, hpow, hcase⟩ := hP
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hσ : 2 ≤ sigma L1 R := by
    unfold sigma
    have := mul_nonneg hL1 hR.le
    linarith
  have hσ0 : 0 < sigma L1 R := by linarith
  have hσ2 : 4 ≤ sigma L1 R ^ 2 := by nlinarith
  have hσ3 : 1 + sigma L1 R ≤ sigma L1 R ^ 2 := by nlinarith
  have hc : 0 < cap L0 := by
    unfold cap
    positivity
  have hnorm : 0 < L0 + L1 * ‖g x0‖ := by positivity
  have hη : 0 < eta g x0 L0 L1 h0 := lt_min hh0 (by positivity)
  have hh := hI.h_pos
  by_cases hacc : Accepted g s
  · refine ⟨accept_inv H hR.le hI hacc, acc + 1, rej, by omega, ?_, ?_⟩
    · rw [trial_accepted hacc]
      change 2 * s.h * 2 ^ rej = h0 * 2 ^ (acc + 1)
      rw [pow_succ]
      linarith
    · right
      rw [trial_accepted hacc]
      change eta g x0 L0 L1 h0 ≤ s.A + stepWeight s ∧
        min (cap L0) ((s.A + stepWeight s) / sigma L1 R ^ 2) ≤ 2 * s.h ∧
        ((acc + 1 : ℕ) : ℝ) ≤
          1 + progress (sigma L1 R) (cap L0) (eta g x0 L0 L1 h0) (s.A + stepWeight s)
      rcases hcase with ⟨hA0, hacc0, -, hηh⟩ | ⟨hηA, hθ, hcount⟩
      · rw [stepWeight_zero hA0 hh, hA0, zero_add]
        refine ⟨hηh, ?_, ?_⟩
        · refine (min_le_right _ _).trans ?_
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        · subst hacc0
          have := progress_nonneg hσ hc hη hηh
          push_cast
          linarith
      · have hApos : 0 < s.A := hη.trans_le hηA
        have ha := stepWeight_pos hh
        have hsq := stepWeight_sq hApos.le hh
        refine ⟨by linarith, ?_, ?_⟩
        · rcases le_or_gt (cap L0) (2 * s.h) with hc2 | hc2
          · exact (min_le_left _ _).trans hc2
          · have hAh : s.A ≤ s.h * sigma L1 R ^ 2 := by
              rcases min_le_iff.mp hθ with h | h
              · linarith
              · rwa [div_le_iff₀ (by positivity)] at h
            have haσ : stepWeight s ≤ s.h * (1 + sigma L1 R) := by
              by_contra hcon
              push Not at hcon
              have e1 := mul_lt_mul_of_pos_left hcon ha
              have e2 := mul_lt_mul_of_pos_left hcon
                (by positivity : 0 < s.h * sigma L1 R)
              have e3 := mul_le_mul_of_nonneg_left hAh hh.le
              have e4 : 0 ≤ s.h * s.h * sigma L1 R := by positivity
              nlinarith
            refine (min_le_right _ _).trans ?_
            rw [div_le_iff₀ (by positivity)]
            have := mul_le_mul_of_nonneg_left hσ3 hh.le
            linarith
        · have := progress_accept hσ hc hη hηA ha hsq hθ
          push_cast
          linarith
  · refine ⟨reject_inv hI hacc, acc, rej + 1, by omega, ?_, ?_⟩
    · rw [trial_rejected hacc]
      change s.h / 2 * 2 ^ (rej + 1) = h0 * 2 ^ acc
      rw [pow_succ]
      linarith
    · rw [trial_rejected hacc]
      rcases hcase with ⟨hA0, hacc0, hv, -⟩ | ⟨hηA, -, hcount⟩
      · left
        refine ⟨hA0, hacc0, hv, ?_⟩
        change eta g x0 L0 L1 h0 ≤ s.h / 2
        have hnot : ¬(4 * (L0 + L1 * ‖g s.v‖) * s.h ≤ 1) :=
          fun h => hacc (pass_zero H hA0 hh h)
        push Not at hnot
        rw [hv] at hnot
        refine (min_le_right _ _).trans ?_
        rw [div_le_iff₀ (by positivity)]
        linarith
      · right
        refine ⟨hηA, ?_, hcount⟩
        change min (cap L0) (s.A / sigma L1 R ^ 2) ≤ s.h / 2
        have hApos : 0 < s.A := hη.trans_le hηA
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2⟩ := lt_min_iff.mp hcon
        apply hacc
        apply pass_pos H hR hI hApos
        · unfold cap at h1
          rw [lt_div_iff₀ (by positivity)] at h1
          linarith
        · rw [lt_div_iff₀ (by positivity)] at h2
          unfold sigma at h2
          linarith

lemma progress_iterate {f : E → ℝ} {g : E → E} {L0 L1 R h0 : ℝ} {u x0 : E}
    (H : Hyp f g L0 L1 u) (hR : 0 < R) (hh0 : 0 < h0) (hdist : ‖x0 - u‖ ≤ R) (n : ℕ) :
    Progress f g u x0 L0 L1 R h0 n ((trial g)^[n] ⟨0, x0, x0, h0⟩) := by
  induction n with
  | zero =>
    refine ⟨⟨le_rfl, hh0, ?_, hdist⟩, 0, 0, rfl, by simp, Or.inl ⟨rfl, rfl, rfl, min_le_left _ _⟩⟩
    change 0 * (f x0 - f u) + 1 / 2 * ‖x0 - u‖ ^ 2 ≤ R ^ 2 / 2
    have := pow_le_pow_left₀ (norm_nonneg (x0 - u)) hdist 2
    linarith
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact progress_step H hR hh0 ih

lemma trial_accuracy {f : E → ℝ} {g : E → E} {L0 L1 R h0 ε : ℝ} {u x0 : E}
    (H : Hyp f g L0 L1 u) (hR : 0 < R) (hh0 : 0 < h0) (hε : 0 < ε)
    (hdist : ‖x0 - u‖ ≤ R) (n : ℕ)
    (hn : 2 * (2 + (1 + sigma L1 R) *
          Real.log (1 + cap L0 * sigma L1 R ^ 2 / eta g x0 L0 L1 h0) +
        2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0)) +
      Real.logb 2 (h0 / min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2)) < n) :
    f ((trial g)^[n] ⟨0, x0, x0, h0⟩).x - f u ≤ ε := by
  obtain ⟨hI, acc, rej, hsum, hpow, hcase⟩ := progress_iterate H hR hh0 hdist n
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hσ : 2 ≤ sigma L1 R := by
    unfold sigma
    have := mul_nonneg hL1 hR.le
    linarith
  have hσ0 : 0 < sigma L1 R := by linarith
  have hσ2 : 1 ≤ sigma L1 R ^ 2 := by nlinarith
  have hc : 0 < cap L0 := by
    unfold cap
    positivity
  have hnorm : 0 < L0 + L1 * ‖g x0‖ := by positivity
  have hη : 0 < eta g x0 L0 L1 h0 := lt_min hh0 (by positivity)
  have hsc : 0 < Real.sqrt (cap L0) := Real.sqrt_pos.mpr hc
  have hlog0 : 0 ≤ Real.log (1 + cap L0 * sigma L1 R ^ 2 / eta g x0 L0 L1 h0) :=
    Real.log_nonneg (by have : 0 < cap L0 * sigma L1 R ^ 2 / eta g x0 L0 L1 h0 := by positivity
                        linarith)
  have hsqrt0 : 0 ≤ 2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0) := by positivity
  generalize hs : (trial g)^[n] ⟨0, x0, x0, h0⟩ = s at hI hpow hcase ⊢
  by_contra hgap
  push Not at hgap
  have hminpos : 0 < min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2) :=
    lt_min hc (by positivity)
  have hstep : min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2) ≤ s.h := by
    rcases hcase with ⟨-, -, -, hηh⟩ | ⟨hηA, hθ, -⟩
    · refine (min_le_right _ _).trans ((div_le_self hη.le hσ2).trans hηh)
    · exact (min_le_min le_rfl (div_le_div_of_nonneg_right hηA (by positivity))).trans hθ
  have hrej : (rej : ℝ) ≤
      Real.logb 2 (h0 / min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2)) + acc := by
    have h2 : (0 : ℝ) < 2 ^ rej := by positivity
    have hle : (2 : ℝ) ^ rej ≤
        h0 / min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2) * 2 ^ acc := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hminpos]
      calc
        (2 : ℝ) ^ rej * min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2) ≤ 2 ^ rej * s.h :=
          mul_le_mul_of_nonneg_left hstep h2.le
        _ = h0 * 2 ^ acc := by rw [mul_comm, hpow]
    have hlb := Real.logb_le_logb_of_le (b := 2) (by norm_num) h2 hle
    rw [Real.logb_mul (div_pos hh0 hminpos).ne' (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)] at hlb
    linarith
  have hacc : (acc : ℝ) ≤ 2 + (1 + sigma L1 R) *
        Real.log (1 + cap L0 * sigma L1 R ^ 2 / eta g x0 L0 L1 h0) +
      2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0) := by
    rcases hcase with ⟨-, hacc0, -, -⟩ | ⟨hηA, -, hcount⟩
    · subst hacc0
      have := mul_nonneg (by linarith : 0 ≤ 1 + sigma L1 R) hlog0
      push_cast
      linarith
    · have hApos : 0 < s.A := hη.trans_le hηA
      have hple := progress_le hσ hc hη hApos
      have hAε : s.A ≤ R ^ 2 / (2 * ε) := by
        rw [le_div_iff₀ (by positivity)]
        have hp := hI.potential
        have := sq_nonneg ‖s.v - u‖
        have := mul_lt_mul_of_pos_left hgap hApos
        linarith
      have hsq : Real.sqrt s.A ≤ Real.sqrt (R ^ 2 / (2 * ε)) := Real.sqrt_le_sqrt hAε
      have hdiv : 2 * Real.sqrt s.A / Real.sqrt (cap L0) ≤
          2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0) :=
        div_le_div_of_nonneg_right (by linarith) hsc.le
      linarith
  have hnle : (n : ℝ) = acc + rej := by
    rw [← hsum]
    push_cast
    ring
  linarith

end OracleTemplate.ParameterFreeGeneralized
