import LongTails.Algorithms.CovarianceSoftCut
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutSelection

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut

lemma segmentDirection_scale (q : Params) (ends : Space q × Space q) :
    ‖ends.2-ends.1‖ • segmentDirection q ends = ends.2-ends.1 := by
  by_cases h : ends.2-ends.1 = 0
  · simp [segmentDirection, h]
  · rw [segmentDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

lemma segmentMid_sub_left (q : Params) (ends : Space q × Space q) :
    segmentMid q ends - ends.1 = (1 / 2 : ℝ) • (ends.2-ends.1) := by
  unfold segmentMid
  module

lemma right_sub_segmentMid (q : Params) (ends : Space q × Space q) :
    ends.2 - segmentMid q ends = (1 / 2 : ℝ) • (ends.2-ends.1) := by
  unfold segmentMid
  module

lemma segmentMid_width_left (q : Params) (ends : Space q × Space q) :
    ‖segmentMid q ends - ends.1‖ = ‖ends.2-ends.1‖ / 2 := by
  rw [segmentMid_sub_left, norm_smul]
  norm_num
  ring

lemma segmentMid_width_right (q : Params) (ends : Space q × Space q) :
    ‖ends.2 - segmentMid q ends‖ = ‖ends.2-ends.1‖ / 2 := by
  rw [right_sub_segmentMid, norm_smul]
  norm_num
  ring

lemma bisectUpdate_width (q : Params) (a estimate : ℝ) (ends : Space q × Space q) :
    ‖(bisectUpdate q a ends estimate).2 - (bisectUpdate q a ends estimate).1‖ ≤ ‖ends.2-ends.1‖ / 2 := by
  unfold bisectUpdate
  split_ifs
  · exact (segmentMid_width_left q ends).le
  · exact (segmentMid_width_right q ends).le
  · simp only [sub_self, norm_zero]
    positivity

lemma midpoint_function_bounds (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (ends : Space q × Space q) :
    f (segmentMid q ends) ≤ f ends.1 + ‖ends.2-ends.1‖ / 2 *
      ⟪v (segmentMid q ends), segmentDirection q ends⟫ ∧
    f (segmentMid q ends) ≤ f ends.2 - ‖ends.2-ends.1‖ / 2 *
      ⟪v (segmentMid q ends), segmentDirection q ends⟫ := by
  have hl := hg (segmentMid q ends) ends.1
  have hr := hg (segmentMid q ends) ends.2
  have hvec := segmentDirection_scale q ends
  have hlv : ends.1 - segmentMid q ends = -(1 / 2 : ℝ) • (ends.2-ends.1) := by
    unfold segmentMid
    module
  rw [hlv, ← hvec, smul_smul, inner_smul_right] at hl
  rw [right_sub_segmentMid, ← hvec, smul_smul, inner_smul_right] at hr
  constructor <;> nlinarith

def endpointPotential (q : Params) (f : Space q → ℝ) (a : ℝ) (ends : Space q × Space q) : ℝ :=
  min (f ends.1) (f ends.2) + (3 * a / 2) * ‖ends.2-ends.1‖

lemma bisectUpdate_potential (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (a : ℝ) (ha : 0 ≤ a) (ends : Space q × Space q) (estimate : ℝ)
    (herr : |estimate - ⟪v (segmentMid q ends), segmentDirection q ends⟫| ≤ a) :
    endpointPotential q f a (bisectUpdate q a ends estimate) ≤ endpointPotential q f a ends := by
  obtain ⟨hl, hr⟩ := midpoint_function_bounds q f v hg ends
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herr
  have hw := norm_nonneg (ends.2-ends.1)
  unfold bisectUpdate
  split_ifs with hpos hneg
  · have hd : 0 ≤ ⟪v (segmentMid q ends), segmentDirection q ends⟫ := by linarith
    have hf : f (segmentMid q ends) ≤ f ends.2 := by nlinarith
    have hm := min_le_min_left (f ends.1) hf
    unfold endpointPotential
    simp only [segmentMid_width_left]
    nlinarith
  · have hd : ⟪v (segmentMid q ends), segmentDirection q ends⟫ ≤ 0 := by linarith
    have hf : f (segmentMid q ends) ≤ f ends.1 := by nlinarith
    have hm := min_le_min_right (f ends.2) hf
    unfold endpointPotential
    simp only [segmentMid_width_right]
    nlinarith
  · have hdlo : -(3*a) ≤ ⟪v (segmentMid q ends), segmentDirection q ends⟫ := by linarith
    have hdhi : ⟪v (segmentMid q ends), segmentDirection q ends⟫ ≤ 3*a := by linarith
    have hfl : f (segmentMid q ends) ≤ f ends.1 + (3*a/2)*‖ends.2-ends.1‖ := by nlinarith
    have hfr : f (segmentMid q ends) ≤ f ends.2 + (3*a/2)*‖ends.2-ends.1‖ := by nlinarith
    unfold endpointPotential
    simp only [min_self, sub_self, norm_zero, mul_zero, add_zero]
    rcases le_total (f ends.1) (f ends.2) with h | h
    · simpa only [min_eq_left h] using hfl
    · simpa only [min_eq_right h] using hfr

lemma bisectRun_width (q : Params) (a : ℝ) (initial : Space q × Space q)
    (estimates : ℕ → ℝ) (n : ℕ) :
    ‖(bisectRun q a initial estimates n).2 - (bisectRun q a initial estimates n).1‖ ≤
      ‖initial.2-initial.1‖ / (2 : ℝ)^n := by
  induction n with
  | zero => simp [bisectRun]
  | succ n ih =>
    apply (bisectUpdate_width q a (estimates n) (bisectRun q a initial estimates n)).trans
    calc
      ‖(bisectRun q a initial estimates n).2 - (bisectRun q a initial estimates n).1‖ / 2 ≤
          (‖initial.2-initial.1‖ / (2 : ℝ)^n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = ‖initial.2-initial.1‖ / (2 : ℝ)^(n+1) := by rw [div_div, pow_succ]

lemma bisectRun_potential (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (a : ℝ) (ha : 0 ≤ a) (initial : Space q × Space q) (estimates : ℕ → ℝ) (n : ℕ)
    (herr : ∀ t, t < n → |estimates t -
      ⟪v (segmentMid q (bisectRun q a initial estimates t)),
        segmentDirection q (bisectRun q a initial estimates t)⟫| ≤ a) :
    endpointPotential q f a (bisectRun q a initial estimates n) ≤ endpointPotential q f a initial := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    exact (bisectUpdate_potential q f v hg a ha _ _ (herr n (Nat.lt_succ_self n))).trans
      (ih (fun t ht => herr t (Nat.lt_trans ht (Nat.lt_succ_self n))))

lemma midpoint_lipschitz_bound (q : Params) (f : Space q → ℝ) (L : ℝ)
    (hlip : ∀ x y, |f x-f y| ≤ L * ‖x-y‖) (ends : Space q × Space q) :
    f (segmentMid q ends) ≤ min (f ends.1) (f ends.2) + L * ‖ends.2-ends.1‖ / 2 := by
  have hl := (le_abs_self (f (segmentMid q ends)-f ends.1)).trans (hlip _ _)
  rw [segmentMid_width_left] at hl
  have hr := (le_abs_self (f (segmentMid q ends)-f ends.2)).trans (hlip _ _)
  rw [norm_sub_rev, segmentMid_width_right] at hr
  rcases le_total (f ends.1) (f ends.2) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

lemma bisectRun_accuracy (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ x y, |f x-f y| ≤ L * ‖x-y‖)
    (a : ℝ) (ha : 0 ≤ a) (initial : Space q × Space q) (estimates : ℕ → ℝ) (n : ℕ)
    (herr : ∀ t, t < n → |estimates t -
      ⟪v (segmentMid q (bisectRun q a initial estimates t)),
        segmentDirection q (bisectRun q a initial estimates t)⟫| ≤ a) :
    f (segmentMid q (bisectRun q a initial estimates n)) ≤
      min (f initial.1) (f initial.2) + (3*a/2)*‖initial.2-initial.1‖ +
        L * ‖initial.2-initial.1‖ / (2 * (2 : ℝ)^n) := by
  have hp := bisectRun_potential q f v hg a ha initial estimates n herr
  have hw := bisectRun_width q a initial estimates n
  have hf := midpoint_lipschitz_bound q f L hlip (bisectRun q a initial estimates n)
  have hn : 0 ≤ (3*a/2)*‖(bisectRun q a initial estimates n).2 - (bisectRun q a initial estimates n).1‖ := by positivity
  have hwidth : L * ‖(bisectRun q a initial estimates n).2 - (bisectRun q a initial estimates n).1‖ / 2 ≤
      L * ‖initial.2-initial.1‖ / (2 * (2 : ℝ)^n) := by
    calc
      _ ≤ L * (‖initial.2-initial.1‖ / (2 : ℝ)^n) / 2 := by gcongr
      _ = _ := by ring
  unfold endpointPotential at hp
  linarith

lemma norm_segmentDirection_le (q : Params) (ends : Space q × Space q) :
    ‖segmentDirection q ends‖ ≤ 1 := by
  by_cases h : ends.2-ends.1 = 0
  · simp [segmentDirection, h]
  · simp [segmentDirection, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma norm_segmentMid_le (q : Params) (ends : Space q × Space q) (R : ℝ)
    (hl : ‖ends.1‖ ≤ R) (hr : ‖ends.2‖ ≤ R) : ‖segmentMid q ends‖ ≤ R := by
  unfold segmentMid
  rw [norm_smul]
  norm_num
  have h := norm_add_le ends.1 ends.2
  linarith

lemma bisectUpdate_radius (q : Params) (a estimate R : ℝ) (ends : Space q × Space q)
    (hl : ‖ends.1‖ ≤ R) (hr : ‖ends.2‖ ≤ R) :
    ‖(bisectUpdate q a ends estimate).1‖ ≤ R ∧ ‖(bisectUpdate q a ends estimate).2‖ ≤ R := by
  have hm := norm_segmentMid_le q ends R hl hr
  unfold bisectUpdate
  split_ifs <;> exact ⟨by assumption, by assumption⟩

lemma bisectRun_radius (q : Params) (a R : ℝ) (initial : Space q × Space q)
    (hl : ‖initial.1‖ ≤ R) (hr : ‖initial.2‖ ≤ R) (estimates : ℕ → ℝ) (n : ℕ) :
    ‖(bisectRun q a initial estimates n).1‖ ≤ R ∧ ‖(bisectRun q a initial estimates n).2‖ ≤ R := by
  induction n with
  | zero => exact ⟨hl, hr⟩
  | succ n ih => exact bisectUpdate_radius q a (estimates n) R _ ih.1 ih.2

lemma bisectRun_tuned_accuracy (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (L R τ : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hτ : 0 < τ)
    (hlip : ∀ x y, |f x-f y| ≤ L * ‖x-y‖)
    (initial : Space q × Space q) (hl : ‖initial.1‖ ≤ 2*R) (hr : ‖initial.2‖ ≤ 2*R)
    (estimates : ℕ → ℝ) (n : ℕ) (hpower : 4*L*R ≤ τ*(2 : ℝ)^n)
    (herr : ∀ t, t < n → |estimates t -
      ⟪v (segmentMid q (bisectRun q (τ/(12*R)) initial estimates t)),
        segmentDirection q (bisectRun q (τ/(12*R)) initial estimates t)⟫| ≤ τ/(12*R)) :
    f (segmentMid q (bisectRun q (τ/(12*R)) initial estimates n)) ≤ min (f initial.1) (f initial.2) + τ := by
  have h := bisectRun_accuracy q f v hg L hL hlip (τ/(12*R)) (by positivity) initial estimates n herr
  have hw : ‖initial.2-initial.1‖ ≤ 4*R := by
    have hn := norm_sub_le initial.2 initial.1
    linarith
  have hnoise : (3*(τ/(12*R))/2)*‖initial.2-initial.1‖ ≤ τ/2 := by
    calc
      _ ≤ (3*(τ/(12*R))/2)*(4*R) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = τ/2 := by field_simp; ring
  have htail : L*‖initial.2-initial.1‖ / (2*(2 : ℝ)^n) ≤ τ/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(2 : ℝ)^n)).2
    have hh := mul_le_mul_of_nonneg_left hw hL
    nlinarith
  linarith

end LongTails.Proofs.CovarianceSoftCutSelection


