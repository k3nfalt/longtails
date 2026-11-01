import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace OracleTemplate.ScheduleBlock

open Finset

def win (η : ℕ → ℝ) (lam : ℝ) (s t : ℕ) : ℝ := ∏ j ∈ Ico s t, (1 - η j * lam)

def pr (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) : ℝ := win η lam 0 t

def ssum (η : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, η s

def resp (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, η s * win η lam (s + 1) t

def traj (η : ℕ → ℝ) (lam γ : ℝ) (ξ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η t * lam) * traj η lam γ ξ t - η t * (γ + ξ t)

def errResp (η : ℕ → ℝ) (lam : ℝ) (ξ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ range t, win η lam (s + 1) t * η s * ξ s

lemma win_self (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) : win η lam t t = 1 := by simp [win]

lemma win_succ_right (η : ℕ → ℝ) (lam : ℝ) {s t : ℕ} (h : s ≤ t) :
    win η lam s (t + 1) = win η lam s t * (1 - η t * lam) := by
  unfold win
  rw [Finset.prod_Ico_succ_top h]

lemma win_succ_left (η : ℕ → ℝ) (lam : ℝ) {s t : ℕ} (h : s < t) :
    win η lam s t = (1 - η s * lam) * win η lam (s + 1) t := by
  unfold win
  rw [Finset.prod_eq_prod_Ico_succ_bot h]

lemma resp_succ (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) :
    resp η lam (t + 1) = (1 - η t * lam) * resp η lam t + η t := by
  unfold resp
  rw [Finset.sum_range_succ, win_self, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [win_succ_right η lam (by simpa using Finset.mem_range.mp hs)]
  ring

lemma errResp_succ (η : ℕ → ℝ) (lam : ℝ) (ξ : ℕ → ℝ) (t : ℕ) :
    errResp η lam ξ (t + 1) = (1 - η t * lam) * errResp η lam ξ t + η t * ξ t := by
  unfold errResp
  rw [Finset.sum_range_succ, win_self, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [win_succ_right η lam (by simpa using Finset.mem_range.mp hs)]
  ring

lemma pr_succ (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) :
    pr η lam (t + 1) = pr η lam t * (1 - η t * lam) :=
  win_succ_right η lam (Nat.zero_le t)

lemma lam_mul_resp (η : ℕ → ℝ) (lam : ℝ) (t : ℕ) :
    lam * resp η lam t = 1 - pr η lam t := by
  induction t with
  | zero => simp [resp, pr, win]
  | succ t ih => rw [resp_succ, pr_succ]; linear_combination (1 - η t * lam) * ih

lemma traj_eq (η : ℕ → ℝ) (lam γ : ℝ) (ξ : ℕ → ℝ) (t : ℕ) :
    traj η lam γ ξ t = -(resp η lam t * γ) - errResp η lam ξ t := by
  induction t with
  | zero => simp [traj, resp, errResp]
  | succ t ih => rw [traj, ih, resp_succ, errResp_succ]; ring

lemma model_grad_eq (η : ℕ → ℝ) (lam γ : ℝ) (ξ : ℕ → ℝ) (t : ℕ) :
    γ + lam * traj η lam γ ξ t = pr η lam t * γ - lam * errResp η lam ξ t := by
  rw [traj_eq]
  have := lam_mul_resp η lam t
  linear_combination (-γ) * this

lemma lam_eta_win (η : ℕ → ℝ) (lam : ℝ) {s t : ℕ} (h : s < t) :
    lam * η s * win η lam (s + 1) t = win η lam (s + 1) t - win η lam s t := by
  rw [win_succ_left η lam h]; ring

lemma ssum_succ (η : ℕ → ℝ) (t : ℕ) : ssum η (t + 1) = ssum η t + η t := by
  simp [ssum, Finset.sum_range_succ]

end OracleTemplate.ScheduleBlock
