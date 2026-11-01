import LongTails.Proofs.ScheduleBlockScalar
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OracleTemplate.ScheduleBlock

open Finset

def respP (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, η s * pr η lam s

lemma resp_eq_respP (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) : resp η lam t = respP η lam t := by
  induction t with
  | zero => simp [resp, respP]
  | succ t ih =>
    have h := lam_mul_resp η lam t
    rw [resp_succ, ih]
    rw [ih] at h
    unfold respP at h ⊢
    rw [Finset.sum_range_succ]
    linear_combination (-(η t)) * h

lemma win_neg_bounds {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {m : ℝ} (hm : 0 ≤ m) (s : ℕ) :
    ∀ t, s ≤ t → 1 ≤ win η (-m) s t ∧ win η (-m) s t ≤ win η (-m) 0 t := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base =>
    rw [win_self]
    refine ⟨le_rfl, ?_⟩
    induction s with
    | zero => simp [win]
    | succ s ih =>
      rw [win_succ_right η (-m) (Nat.zero_le s)]
      have h1 : 1 ≤ 1 - η s * -m := by nlinarith [hη s]
      nlinarith
  | succ t hst ih =>
    rw [win_succ_right η (-m) hst, win_succ_right η (-m) (Nat.zero_le t)]
    have h1 : 1 ≤ 1 - η t * -m := by have := hη t; nlinarith
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · nlinarith
    · exact mul_le_mul_of_nonneg_right ih2 (by linarith)

lemma pr_neg_ge {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {m : ℝ} (hm : 0 ≤ m) (t : ℕ) :
    1 + m * ssum η t ≤ pr η (-m) t := by
  induction t with
  | zero => simp [pr, win, ssum]
  | succ t ih =>
    rw [pr_succ, ssum_succ]
    have h0 : 1 ≤ pr η (-m) t := (win_neg_bounds hη hm 0 t (Nat.zero_le t)).1
    have := hη t
    nlinarith [mul_nonneg hm (hη t)]

lemma pr_neg_le_exp {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {m : ℝ} (hm : 0 ≤ m) (t : ℕ) :
    pr η (-m) t ≤ Real.exp (m * ssum η t) := by
  induction t with
  | zero => simp [pr, win, ssum]
  | succ t ih =>
    rw [pr_succ, ssum_succ, mul_add, Real.exp_add]
    have h1 : 1 - η t * -m ≤ Real.exp (m * η t) := by
      have := Real.add_one_le_exp (m * η t); linarith
    have h0 : 0 ≤ pr η (-m) t := by
      have := (win_neg_bounds hη hm 0 t (Nat.zero_le t)).1
      unfold pr; linarith
    exact mul_le_mul ih h1 (by have := hη t; nlinarith) (Real.exp_pos _).le

lemma resp_neg_bounds {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {m : ℝ} (hm : 0 ≤ m) (t : ℕ) :
    ssum η t ≤ resp η (-m) t ∧ resp η (-m) t ≤ pr η (-m) t * ssum η t := by
  unfold resp ssum
  rw [Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro s hs
    have := (win_neg_bounds hη hm (s + 1) t (Finset.mem_range.mp hs)).1
    nlinarith [hη s]
  · apply Finset.sum_le_sum
    intro s hs
    have := (win_neg_bounds hη hm (s + 1) t (Finset.mem_range.mp hs)).2
    unfold pr
    nlinarith [hη s]

lemma errResp_neg_le {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {m : ℝ} (hm : 0 ≤ m) (ξ : ℕ → ℝ)
    (t : ℕ) : |errResp η (-m) ξ t| ≤ pr η (-m) t * ∑ s ∈ range t, η s * |ξ s| := by
  unfold errResp
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro s hs
  obtain ⟨h1, h2⟩ := win_neg_bounds hη hm (s + 1) t (Finset.mem_range.mp hs)
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ win η (-m) (s + 1) t),
    abs_of_nonneg (hη s)]
  unfold pr
  have : 0 ≤ η s * |ξ s| := mul_nonneg (hη s) (abs_nonneg _)
  nlinarith

lemma errResp_pos_le {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {lam K : ℝ} (ξ : ℕ → ℝ) (t : ℕ)
    (hW : ∀ s, s < t → |win η lam (s + 1) t| ≤ K) :
    |errResp η lam ξ t| ≤ K * ∑ s ∈ range t, η s * |ξ s| := by
  unfold errResp
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro s hs
  rw [abs_mul, abs_mul, abs_of_nonneg (hη s)]
  have := hW s (Finset.mem_range.mp hs)
  have : 0 ≤ η s * |ξ s| := mul_nonneg (hη s) (abs_nonneg _)
  nlinarith

lemma lam_errResp_le {η : ℕ → ℝ} {lam K : ℝ} (ξ : ℕ → ℝ) (t : ℕ)
    (hW : ∀ s, s ≤ t → |win η lam s t| ≤ K) :
    |lam * errResp η lam ξ t| ≤ 2 * K * ∑ s ∈ range t, |ξ s| := by
  unfold errResp
  rw [Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro s hs
  have hst := Finset.mem_range.mp hs
  have e : lam * (win η lam (s + 1) t * η s * ξ s) =
      (win η lam (s + 1) t - win η lam s t) * ξ s := by
    rw [← lam_eta_win η lam hst]; ring
  rw [e, abs_mul]
  have h1 := hW (s + 1) hst
  have h2 := hW s hst.le
  have : |win η lam (s + 1) t - win η lam s t| ≤ 2 * K := by
    calc _ ≤ |win η lam (s + 1) t| + |win η lam s t| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  have : 0 ≤ |ξ s| := abs_nonneg _
  nlinarith

lemma resp_pos_bounds {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {lam : ℝ} (t : ℕ)
    (hP : ∀ s, s ≤ t → |pr η lam s| ≤ 1) :
    |resp η lam t| ≤ ssum η t := by
  rw [resp_eq_respP]
  unfold respP ssum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro s hs
  rw [abs_mul, abs_of_nonneg (hη s)]
  have := hP s (Finset.mem_range.mp hs).le
  nlinarith [hη s]

lemma resp_pos_nonneg {η : ℕ → ℝ} (hη : ∀ j, 0 ≤ η j) {lam : ℝ} (hlam : 0 ≤ lam) (t : ℕ)
    (hP : |pr η lam t| ≤ 1) : 0 ≤ resp η lam t := by
  rcases hlam.lt_or_eq with hlam | rfl
  · have h := lam_mul_resp η lam t
    have : 0 ≤ 1 - pr η lam t := by linarith [(abs_le.mp hP).2]
    by_contra hc
    have hc' := lt_of_not_ge hc
    nlinarith
  · unfold resp win
    apply Finset.sum_nonneg
    intro s _
    simp [hη s]

end OracleTemplate.ScheduleBlock
