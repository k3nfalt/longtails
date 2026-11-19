import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators

namespace LongTails.Proofs.SampleLossMixture

def blend (a s b : ℝ) : ℝ := (1 - a) * s + a * b

def variation (a da s b ds db : ℝ) : ℝ := blend a ds db + da * (b - s)

def mixture (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => blend (a n) (mixture a b n) (b n)

def tangent (a b da db : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => variation (a n) (da n) (mixture a b n) (b n) (tangent a b da db n) (db n)

lemma abs_blend_le {a s b : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    |blend a s b| ≤ (1 - a) * |s| + a * |b| := by
  unfold blend
  simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr ha')] using
    abs_add_le ((1 - a) * s) (a * b)

lemma abs_mixture_le (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, |b i| ≤ 1)
    (n : ℕ) : |mixture a b n| ≤ 1 := by
  induction n with
  | zero => simp [mixture]
  | succ n ih =>
    apply (abs_blend_le (ha n).1 (ha n).2).trans
    nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (ha n).2),
      mul_le_mul_of_nonneg_left (hb n) (ha n).1]

private lemma survival_sqrt {a V r : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (hV : 0 ≤ V) :
    (1 - a) * Real.sqrt V + Real.sqrt a * r ≤ Real.sqrt (V + r ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have ht : (1 - a) ^ 2 + Real.sqrt a ^ 2 ≤ 1 := by
    rw [Real.sq_sqrt ha]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha')]
  have hc := mul_le_mul_of_nonneg_right ht (add_nonneg hV (sq_nonneg r))
  nlinarith [sq_nonneg ((1 - a) * r - Real.sqrt a * Real.sqrt V), Real.sq_sqrt hV,
    show (Real.sqrt V) ^ 2 * (1 - a) ^ 2 = V * (1 - a) ^ 2 by rw [Real.sq_sqrt hV],
    show (Real.sqrt V) ^ 2 * (Real.sqrt a) ^ 2 = V * (Real.sqrt a) ^ 2 by rw [Real.sq_sqrt hV]]

lemma mixture_model (a b a' b' da db r : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (ha' : ∀ i, 0 ≤ a' i ∧ a' i ≤ 1)
    (hb : ∀ i, |b i| ≤ 1) (hb' : ∀ i, |b' i| ≤ 1) (hr : ∀ i, 0 ≤ r i)
    (hda : ∀ i, |da i| ≤ Real.sqrt (a i) * r i)
    (hA : ∀ i, |a' i - a i - da i| ≤ r i ^ 2)
    (hlip : ∀ i, |b' i - b i| ≤ r i)
    (hB : ∀ i, |b' i - b i - db i| ≤ r i ^ 2) (n : ℕ) :
    let V := ∑ i ∈ Finset.range n, r i ^ 2
    |mixture a' b' n - mixture a b n| ≤ 3 * Real.sqrt V + 2 * V ∧
      |mixture a' b' n - mixture a b n - tangent a b da db n| ≤ 16 * V := by
  induction n with
  | zero => simp [mixture, tangent]
  | succ n ih =>
    let V := ∑ i ∈ Finset.range n, r i ^ 2
    let s := mixture a b n
    let s' := mixture a' b' n
    let ds := tangent a b da db n
    have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg _
    obtain ⟨hD, hE⟩ := ih
    change |s' - s| ≤ 3 * Real.sqrt V + 2 * V at hD
    change |s' - s - ds| ≤ 16 * V at hE
    have hs := abs_mixture_le a b ha hb n
    have hs' := abs_mixture_le a' b' ha' hb' n
    change |s| ≤ 1 at hs
    change |s'| ≤ 1 at hs'
    have hD2 : |s' - s| ≤ 2 := (abs_sub _ _).trans (by linarith)
    have hD5 : |s' - s| ≤ 5 * Real.sqrt V := by
      by_cases hv : V ≤ 1
      · have h := Real.sq_sqrt hV
        have hl : Real.sqrt V ≤ 1 := by simpa using Real.sqrt_le_sqrt hv
        nlinarith [mul_nonneg (Real.sqrt_nonneg V) (sub_nonneg.mpr hl)]
      · have hl : 1 ≤ Real.sqrt V := by simpa using Real.sqrt_le_sqrt (le_of_not_ge hv)
        linarith
    have hAs : |a' n - a n| ≤ Real.sqrt (a n) * r n + r n ^ 2 := by
      calc
        _ = |a' n - a n - da n + da n| := by ring_nf
        _ ≤ _ := (abs_add_le _ _).trans (by linarith [hA n, hda n])
    have hrs := Real.sqrt_nonneg (a n)
    have har : a n ≤ Real.sqrt (a n) := by
      have ht := Real.sqrt_le_sqrt (ha n).2
      rw [Real.sqrt_one] at ht
      nlinarith [Real.sq_sqrt (ha n).1, mul_nonneg hrs (sub_nonneg.mpr ht)]
    have hba : |b' n - s'| ≤ 2 := (abs_sub _ _).trans (by linarith [hb' n])
    have h1 := sub_nonneg.mpr (ha n).2
    dsimp only
    rw [Finset.sum_range_succ]
    change |blend (a' n) s' (b' n) - blend (a n) s (b n)| ≤
        3 * Real.sqrt (V + r n ^ 2) + 2 * (V + r n ^ 2) ∧
      |blend (a' n) s' (b' n) - blend (a n) s (b n) - variation (a n) (da n) s (b n) ds (db n)| ≤
        16 * (V + r n ^ 2)
    constructor
    · have hid : blend (a' n) s' (b' n) - blend (a n) s (b n) =
          blend (a n) (s' - s) (b' n - b n) + (a' n - a n) * (b' n - s') := by unfold blend; ring
      rw [hid]
      apply (abs_add_le _ _).trans
      rw [abs_mul]
      have hw := (abs_blend_le (s := s' - s) (b := b' n - b n) (ha n).1 (ha n).2)
      have hnew := survival_sqrt (ha n).1 (ha n).2 hV (r := r n)
      nlinarith [mul_le_mul_of_nonneg_left hD h1, mul_le_mul_of_nonneg_left (hlip n) (ha n).1,
        mul_le_mul hAs hba (abs_nonneg _) (add_nonneg (mul_nonneg hrs (hr n)) (sq_nonneg _)), mul_nonneg (ha n).1 hV,
        mul_le_mul_of_nonneg_right har (hr n)]
    · have hid : blend (a' n) s' (b' n) - blend (a n) s (b n) - variation (a n) (da n) s (b n) ds (db n) =
          blend (a n) (s' - s - ds) (b' n - b n - db n) +
          (a' n - a n - da n) * (b' n - s') + da n * ((b' n - b n) - (s' - s)) := by
        unfold variation blend
        ring
      rw [hid]
      apply (abs_add_le _ _).trans
      apply le_trans (add_le_add_left (abs_add_le _ _) _)
      simp only [abs_mul]
      have hw := abs_blend_le (s := s' - s - ds) (b := b' n - b n - db n) (ha n).1 (ha n).2
      have hsmall : |(b' n - b n) - (s' - s)| ≤ r n + 5 * Real.sqrt V :=
        (abs_sub _ _).trans (add_le_add (hlip n) hD5)
      have ht : Real.sqrt (a n) * r n * Real.sqrt V ≤ (a n * V + r n ^ 2) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt (a n) * Real.sqrt V - r n),
          show (Real.sqrt (a n) * Real.sqrt V) ^ 2 = a n * V by
            rw [mul_pow, Real.sq_sqrt (ha n).1, Real.sq_sqrt hV]]
      have hr1 : Real.sqrt (a n) ≤ 1 := by simpa using Real.sqrt_le_sqrt (ha n).2
      nlinarith [mul_le_mul_of_nonneg_left hE h1, mul_le_mul_of_nonneg_left (hB n) (ha n).1,
        mul_le_mul (hA n) hba (abs_nonneg _) (sq_nonneg _),
        mul_le_mul (hda n) hsmall (abs_nonneg _) (mul_nonneg hrs (hr n)),
        mul_le_mul_of_nonneg_right hr1 (sq_nonneg (r n)), mul_nonneg (ha n).1 hV,
        mul_le_mul_of_nonneg_right (ha n).2 (sq_nonneg (r n))]

end LongTails.Proofs.SampleLossMixture
