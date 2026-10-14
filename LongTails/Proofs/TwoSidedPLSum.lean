import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Finset MeasureTheory

namespace OracleTemplate.TwoSidedPL

lemma potential_contract {V D ns M N : ℕ → ℝ} {Φs C : ℝ} (hC : 1 ≤ C)
    (hstep : ∀ t, D t - ns t + M t ≤ V t - V (t + 1))
    (hpl : ∀ t, V t - Φs ≤ C * D t + N t) (t : ℕ) :
    V (t + 1) - Φs ≤ (1 - 1 / C) * (V t - Φs) + (N t / C + ns t - M t) := by
  have hC0 : 0 < C := by linarith
  have h1 := hstep t
  have h2 := hpl t
  have h3 : (V t - Φs - N t) / C ≤ D t := by
    rw [div_le_iff₀ hC0]; linarith
  have e : (1 - 1 / C) * (V t - Φs) + (N t / C + ns t - M t) =
      V t - Φs - (V t - Φs - N t) / C + ns t - M t := by field_simp; ring
  rw [e]
  linarith

lemma potential_unroll {V D ns M N : ℕ → ℝ} {Φs C : ℝ} (hC : 1 ≤ C)
    (hstep : ∀ t, D t - ns t + M t ≤ V t - V (t + 1))
    (hpl : ∀ t, V t - Φs ≤ C * D t + N t) (n : ℕ) :
    V n - Φs ≤ (1 - 1 / C) ^ n * (V 0 - Φs) +
      ∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) * (N t / C + ns t - M t) := by
  have hρ : 0 ≤ 1 - 1 / C := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hC
  induction n with
  | zero => simp
  | succ n ih =>
    have h := potential_contract hC hstep hpl n
    rw [sum_range_succ, pow_succ]
    have hs : ∑ t ∈ range n, (1 - 1 / C) ^ (n + 1 - 1 - t) * (N t / C + ns t - M t) =
        (1 - 1 / C) * ∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) * (N t / C + ns t - M t) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t ht
      have ht' : t < n := mem_range.1 ht
      have : n + 1 - 1 - t = (n - 1 - t) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hs, show n + 1 - 1 - n = 0 by omega, pow_zero, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left ih hρ]

lemma window_sum {V D ns M Nab ab : ℕ → ℝ} {Φs C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ t, D t - ns t + M t ≤ V t - V (t + 1)) (hlow : ∀ t, Φs ≤ V t)
    (hab : ∀ t, ab t ≤ 2 * C * D t + Nab t) (n w : ℕ) :
    ∑ s ∈ Ico n (n + w), ab s ≤
      2 * C * ((V n - Φs) + ∑ s ∈ Ico n (n + w), (ns s - M s)) + ∑ s ∈ Ico n (n + w), Nab s := by
  have htel : ∑ s ∈ Ico n (n + w), D s ≤ V n - V (n + w) + ∑ s ∈ Ico n (n + w), (ns s - M s) := by
    induction w with
    | zero => simp
    | succ w ih =>
      rw [← add_assoc, sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
      have := hstep (n + w)
      linarith
  have h1 : ∑ s ∈ Ico n (n + w), ab s ≤ ∑ s ∈ Ico n (n + w), (2 * C * D s + Nab s) :=
    sum_le_sum fun s _ => hab s
  rw [sum_add_distrib, ← mul_sum] at h1
  have := hlow (n + w)
  nlinarith [mul_le_mul_of_nonneg_left htel (by linarith : (0 : ℝ) ≤ 2 * C)]

lemma integral_window_rhs {X : Type*} [MeasurableSpace X] {P : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure P] {a b ρ C bN bns bNab : ℝ} (n : ℕ)
    (N ns M Nab : ℕ → X → ℝ) (hN : ∀ t, MeasureTheory.Integrable (N t) P)
    (hns : ∀ t, MeasureTheory.Integrable (ns t) P) (hM : ∀ t, MeasureTheory.Integrable (M t) P)
    (hNab : ∀ t, MeasureTheory.Integrable (Nab t) P)
    (hbN : ∀ t, ∫ x, N t x ∂P ≤ bN) (hbns : ∀ t, ∫ x, ns t x ∂P ≤ bns)
    (hM0 : ∀ t, ∫ x, M t x ∂P = 0) (hbNab : ∀ t, ∫ x, Nab t x ∂P ≤ bNab)
    (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hC : 0 < C) :
    ∫ x, (a * (ρ ^ n * b + ∑ t ∈ range n, ρ ^ (n - 1 - t) * (N t x / C + ns t x - M t x) +
        ∑ t ∈ Ico n (n + (n + 1)), (ns t x - M t x)) + ∑ t ∈ Ico n (n + (n + 1)), Nab t x) ∂P ≤
      a * (ρ ^ n * b + ∑ t ∈ range n, ρ ^ (n - 1 - t) * (bN / C + bns) + (n + 1) * bns) +
        (n + 1) * bNab := by
  have hT : ∀ t, Integrable (fun x => ρ ^ (n - 1 - t) * (N t x / C + ns t x - M t x)) P :=
    fun t => (((hN t).div_const C).add (hns t) |>.sub (hM t)).const_mul _
  have hW : ∀ t, Integrable (fun x => ns t x - M t x) P := fun t => (hns t).sub (hM t)
  have hS1 : Integrable (fun x => ∑ t ∈ range n, ρ ^ (n - 1 - t) * (N t x / C + ns t x - M t x)) P :=
    integrable_finsetSum _ fun t _ => hT t
  have hS2 : Integrable (fun x => ∑ t ∈ Ico n (n + (n + 1)), (ns t x - M t x)) P :=
    integrable_finsetSum _ fun t _ => hW t
  have hS3 : Integrable (fun x => ∑ t ∈ Ico n (n + (n + 1)), Nab t x) P :=
    integrable_finsetSum _ fun t _ => hNab t
  have hA0 : Integrable (fun x => ρ ^ n * b + ∑ t ∈ range n, ρ ^ (n - 1 - t) *
      (N t x / C + ns t x - M t x)) P := (integrable_const _).add hS1
  have hA : Integrable (fun x => ρ ^ n * b + ∑ t ∈ range n, ρ ^ (n - 1 - t) *
      (N t x / C + ns t x - M t x) + ∑ t ∈ Ico n (n + (n + 1)), (ns t x - M t x)) P := hA0.add hS2
  have hA' : Integrable (fun x => a * (ρ ^ n * b + ∑ t ∈ range n, ρ ^ (n - 1 - t) *
      (N t x / C + ns t x - M t x) + ∑ t ∈ Ico n (n + (n + 1)), (ns t x - M t x))) P := hA.const_mul a
  rw [integral_add hA' hS3, integral_const_mul, integral_add hA0 hS2,
    integral_add (integrable_const _) hS1, integral_const, integral_finsetSum _ fun t _ => hT t,
    integral_finsetSum _ fun t _ => hW t, integral_finsetSum _ fun t _ => hNab t]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have e1 : ∀ t, ∫ x, ρ ^ (n - 1 - t) * (N t x / C + ns t x - M t x) ∂P ≤
      ρ ^ (n - 1 - t) * (bN / C + bns) := by
    intro t
    have hNs : Integrable (fun x => N t x / C + ns t x) P := ((hN t).div_const C).add (hns t)
    rw [integral_const_mul, integral_sub hNs (hM t),
      integral_add ((hN t).div_const C) (hns t), integral_div, hM0 t]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ _)
    have := hbN t
    have := hbns t
    have : (∫ x, N t x ∂P) / C ≤ bN / C := div_le_div_of_nonneg_right (hbN t) hC.le
    linarith
  have e2 : ∀ t, ∫ x, (ns t x - M t x) ∂P ≤ bns := by
    intro t; rw [integral_sub (hns t) (hM t), hM0 t]; linarith [hbns t]
  have s1 := Finset.sum_le_sum fun t (_ : t ∈ range n) => e1 t
  have s2 := Finset.sum_le_sum fun t (_ : t ∈ Ico n (n + (n + 1))) => e2 t
  have s3 := Finset.sum_le_sum fun t (_ : t ∈ Ico n (n + (n + 1))) => hbNab t
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at s2 s3
  have hc : ((n + (n + 1) - n : ℕ) : ℝ) = n + 1 := by
    rw [show n + (n + 1) - n = n + 1 by omega]; push_cast; ring
  rw [hc] at s2 s3
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add_left s1 (ρ ^ n * b)) s2) ha]

lemma geometric_window_le {ρ C : ℝ} (hC : 1 ≤ C) (hρ : ρ = 1 - 1 / C) (n : ℕ) :
    ∑ t ∈ range n, ρ ^ (n - 1 - t) ≤ C := by
  have hC0 : 0 < C := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ, sub_nonneg, div_le_one hC0]; exact hC
  have hρ1 : ρ < 1 := by
    have : 0 < 1 / C := by positivity
    rw [hρ]; linarith
  have e : ∑ t ∈ range n, ρ ^ (n - 1 - t) = ∑ t ∈ range n, ρ ^ t := by
    rw [← Finset.sum_range_reflect]
    apply sum_congr rfl
    intro t ht
    rw [mem_range] at ht
    congr 1
    omega
  rw [e, geom_sum_eq (ne_of_lt hρ1)]
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : (ρ ^ n - 1) / (ρ - 1) = (1 - ρ ^ n) / (1 - ρ) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [h2, div_le_iff₀ h1]
  have : 1 - ρ = 1 / C := by rw [hρ]; ring
  rw [this]
  have := pow_nonneg hρ0 n
  rw [mul_one_div_cancel hC0.ne']
  linarith

end OracleTemplate.TwoSidedPL
