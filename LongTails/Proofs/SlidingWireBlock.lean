import LongTails.Proofs.SlidingWireChain
import Mathlib.Algebra.Order.Chebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.SlidingWireBlock

open SlidingWireChain

structure Block where
  r : ℕ
  δ : ℝ
  ux : ℝ
  uz : ℝ
  y : ℕ → ℝ

namespace Block

variable (B : Block)

def n : ℕ := B.r ^ 2

noncomputable def e0 : ℝ := -7 * B.ux + B.r * B.y 1

noncomputable def e (j : ℕ) : ℝ := (B.r : ℝ) ^ 2 * (B.y j - B.y (j + 1))

noncomputable def en : ℝ := B.r * B.y B.n - 7 / 2 * B.uz

noncomputable def S0 : ℝ := spS B.δ B.e0

noncomputable def S (j : ℕ) : ℝ := spS B.δ (B.e j)

noncomputable def Sn : ℝ := spS B.δ B.en

noncomputable def g (j : ℕ) : ℝ :=
  (if j = 1 then (B.r : ℝ) * B.S0 else -((B.r : ℝ) ^ 2) * B.S (j - 1)) +
    (if j = B.n then (B.r : ℝ) * B.Sn else (B.r : ℝ) ^ 2 * B.S j)

lemma prefix_sum (j : ℕ) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ B.n) :
    ∑ k ∈ Finset.Icc 1 j, B.g k = B.r * B.S0 + (B.r : ℝ) ^ 2 * B.S j := by
  induction j with
  | zero => omega
  | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, g, ite_true]
        rw [ite_eq_right (by omega)]
      · rw [Finset.sum_Icc_succ_top (by omega), ih h0 (by omega)]
        simp only [g]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [Nat.add_sub_cancel]
        ring

lemma total_sum (hr : 1 ≤ B.r) :
    ∑ k ∈ Finset.Icc 1 B.n, B.g k = B.r * B.S0 + B.r * B.Sn := by
  have hn : 1 ≤ B.n := by unfold n; nlinarith
  rcases Nat.eq_or_lt_of_le hn with h1 | h1
  · rw [← h1]
    simp only [Finset.Icc_self, Finset.sum_singleton, g, ite_true]
    rw [ite_eq_left h1]
  · have hs : B.n = (B.n - 1) + 1 := by omega
    rw [hs, Finset.sum_Icc_succ_top (by omega), prefix_sum B (B.n - 1) (by omega) (by omega)]
    simp only [g]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ← hs]
    ring

lemma sum_e (hn : 1 ≤ B.n) :
    ∑ j ∈ Finset.Icc 1 (B.n - 1), B.e j = (B.r : ℝ) ^ 2 * (B.y 1 - B.y B.n) := by
  have key : ∀ m : ℕ, m + 1 ≤ B.n →
      ∑ j ∈ Finset.Icc 1 m, B.e j = (B.r : ℝ) ^ 2 * (B.y 1 - B.y (m + 1)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
        simp only [e]
        ring
  have := key (B.n - 1) (by omega)
  rwa [show B.n - 1 + 1 = B.n by omega] at this

lemma cs_prefix (j : ℕ) (hj : j ≤ B.n) :
    (∑ k ∈ Finset.Icc 1 j, B.g k) ^ 2 ≤ B.n * ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 j) (f := B.g)
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at h1
  have h2 : ∑ k ∈ Finset.Icc 1 j, B.g k ^ 2 ≤ ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hj)
      (fun _ _ _ => sq_nonneg _)
  have h3 : (j : ℝ) ≤ B.n := by exact_mod_cast hj
  have h4 : 0 ≤ ∑ k ∈ Finset.Icc 1 j, B.g k ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc _ ≤ (j : ℝ) * ∑ k ∈ Finset.Icc 1 j, B.g k ^ 2 := by exact_mod_cast h1
    _ ≤ B.n * ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 := by
        apply mul_le_mul h3 h2 h4 (Nat.cast_nonneg _)

lemma abs_prefix (hr : 1 ≤ B.r) (j : ℕ) (hj : j ≤ B.n)
    (hτ : ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 ≤ 1 / 16) :
    |∑ k ∈ Finset.Icc 1 j, B.g k| ≤ B.r / 4 := by
  have h := cs_prefix B j hj
  have hn : (B.n : ℝ) = (B.r : ℝ) ^ 2 := by unfold n; push_cast; ring
  rw [hn] at h
  have hr0 : (0 : ℝ) ≤ B.r := Nat.cast_nonneg _
  have : (∑ k ∈ Finset.Icc 1 j, B.g k) ^ 2 ≤ ((B.r : ℝ) / 4) ^ 2 := by
    calc _ ≤ (B.r : ℝ) ^ 2 * ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 := h
      _ ≤ (B.r : ℝ) ^ 2 * (1 / 16) := mul_le_mul_of_nonneg_left hτ (sq_nonneg _)
      _ = _ := by ring
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]
  exact this

lemma force (hr : 1 ≤ B.r) (hδ : 0 ≤ B.δ) (hrδ : B.r * B.δ ≤ 1 / 4)
    (hτ : ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 ≤ 1 / 16)
    (hx : 7 / 2 ≤ 7 * (B.ux - B.uz / 2)) : B.S0 ≤ -(2 / 7) := by
  by_contra hc
  push Not at hc
  have hr1 : (1 : ℝ) ≤ B.r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < B.r := by linarith
  have hn : 1 ≤ B.n := by unfold n; nlinarith
  have hnr : (B.n : ℝ) = (B.r : ℝ) ^ 2 := by unfold n; push_cast; ring
  have hSj : ∀ j, 1 ≤ j → j + 1 ≤ B.n → B.S j ≤ (1 / 4 + 2 / 7) / B.r := by
    intro j hj1 hjn
    have hp := prefix_sum B j hj1 hjn
    have ha := abs_prefix B hr j (by omega) hτ
    have hle := (abs_le.mp ha).2
    rw [le_div_iff₀ hr0]
    have : (B.r : ℝ) ^ 2 * B.S j ≤ B.r / 4 + B.r * (2 / 7) := by nlinarith
    nlinarith
  have hSn : B.Sn ≤ 1 / 4 + 2 / 7 := by
    have hp := total_sum B hr
    have ha := abs_prefix B hr B.n le_rfl hτ
    have hle := (abs_le.mp ha).2
    have : (B.r : ℝ) * B.Sn ≤ B.r / 4 + B.r * (2 / 7) := by nlinarith
    nlinarith
  have hej : ∀ j ∈ Finset.Icc 1 (B.n - 1), B.e j ≤ B.δ + (1 / 4 + 2 / 7) / B.r := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h1 := hSj j hj.1 (by omega)
    have h2 : (1 / 4 + 2 / 7) / (B.r : ℝ) ≤ 1 / 4 + 2 / 7 := by
      rw [div_le_iff₀ hr0]; nlinarith
    have := spS_upper hδ (show B.S j < 1 by linarith)
    unfold S at h1
    linarith
  have hen : B.en ≤ B.δ + (1 / 4 + 2 / 7) := by
    have := spS_upper hδ (show B.Sn < 1 by linarith)
    unfold Sn at hSn
    linarith
  have he0 : -B.e0 ≤ B.δ + 2 / 7 := by
    have := spS_lower hδ (show -1 < B.S0 by linarith)
    unfold S0 at hc
    linarith
  have hsum : ∑ j ∈ Finset.Icc 1 (B.n - 1), B.e j ≤
      ((B.n - 1 : ℕ) : ℝ) * (B.δ + (1 / 4 + 2 / 7) / B.r) := by
    have := Finset.sum_le_sum hej
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
    convert this using 2
    push_cast
    ring
  have hid : 7 * (B.ux - B.uz / 2) =
      (1 / (B.r : ℝ)) * ∑ j ∈ Finset.Icc 1 (B.n - 1), B.e j - B.e0 + B.en := by
    rw [sum_e B hn]
    unfold e0 en
    field_simp
    ring
  have hcnt : ((B.n - 1 : ℕ) : ℝ) ≤ (B.r : ℝ) ^ 2 := by
    rw [Nat.cast_sub hn]; push_cast; rw [hnr]; linarith
  have hpart : (1 / (B.r : ℝ)) * ∑ j ∈ Finset.Icc 1 (B.n - 1), B.e j ≤
      B.r * B.δ + (1 / 4 + 2 / 7) := by
    have hq : 0 ≤ B.δ + (1 / 4 + 2 / 7) / B.r := by positivity
    have h1 : ((B.n - 1 : ℕ) : ℝ) * (B.δ + (1 / 4 + 2 / 7) / B.r) ≤
        (B.r : ℝ) ^ 2 * (B.δ + (1 / 4 + 2 / 7) / B.r) := mul_le_mul_of_nonneg_right hcnt hq
    have h2 : (1 / (B.r : ℝ)) * ((B.r : ℝ) ^ 2 * (B.δ + (1 / 4 + 2 / 7) / B.r)) =
        B.r * B.δ + (1 / 4 + 2 / 7) := by field_simp
    calc _ ≤ (1 / (B.r : ℝ)) * ((B.r : ℝ) ^ 2 * (B.δ + (1 / 4 + 2 / 7) / B.r)) := by
          apply mul_le_mul_of_nonneg_left (hsum.trans h1) (by positivity)
      _ = _ := h2
  have hδ1 : B.δ ≤ 1 / 4 := by nlinarith
  linarith

def neg : Block := ⟨B.r, B.δ, -B.ux, -B.uz, fun j => -B.y j⟩

lemma spS_neg (δ t : ℝ) : spS δ (-t) = -spS δ t := by unfold spS; ring_nf

lemma neg_S0 : B.neg.S0 = -B.S0 := by
  simp only [S0, e0, neg]; rw [← spS_neg]; congr 1; ring

lemma neg_S (j : ℕ) : B.neg.S j = -B.S j := by
  simp only [S, e, neg]; rw [← spS_neg]; congr 1; ring

lemma neg_Sn : B.neg.Sn = -B.Sn := by
  simp only [Sn, en, neg, n]; rw [← spS_neg]; congr 1; ring

lemma neg_g (j : ℕ) : B.neg.g j = -B.g j := by
  have hn : B.neg.n = B.n := rfl
  simp only [g, hn, neg_S0, neg_S, neg_Sn]
  have hr : B.neg.r = B.r := rfl
  rw [hr]
  split_ifs <;> ring

lemma force_neg (hr : 1 ≤ B.r) (hδ : 0 ≤ B.δ) (hrδ : B.r * B.δ ≤ 1 / 4)
    (hτ : ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 ≤ 1 / 16)
    (hx : 7 * (B.ux - B.uz / 2) ≤ -(7 / 2)) : 2 / 7 ≤ B.S0 := by
  have h := force B.neg hr hδ hrδ (by
    have hn : B.neg.n = B.n := rfl
    simp only [hn, neg_g, neg_sq]
    exact hτ) (by simp only [neg]; linarith)
  rw [neg_S0] at h
  linarith

end Block

end LongTails.Proofs.SlidingWireBlock
