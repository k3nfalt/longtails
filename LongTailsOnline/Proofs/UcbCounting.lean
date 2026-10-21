import LongTailsOnline.Proofs.UcbExecution

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.Ucb

open LongTailsOnline.Setups.StochasticBandit LongTailsOnline.Algorithms.Ucb

noncomputable def limit (p : Params) (i : Arm p.k) : ℕ :=
  if 0 < gap p i then ⌈8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2⌉₊ + 1 else 0

noncomputable def potential (p : Params) (c : Counts p.k) : ℝ :=
  ∑ i, gap p i * (min (c i) (limit p i) : ℕ)

lemma gap_nonneg {p : Params} (hp : ∀ i, p.μ i ≤ p.μ p.best) (i : Arm p.k) :
    0 ≤ gap p i := sub_nonneg.mpr (hp i)

lemma gap_le_one {p : Params} (hp : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) (i : Arm p.k) :
    gap p i ≤ 1 := by
  have h1 := (hp p.best).2
  have h0 := (hp i).1
  dsimp [gap]
  linarith

lemma potential_increment (p : Params) (c : Counts p.k) (a : Arm p.k) :
    potential p (increment c a) = potential p c +
      if c a < limit p a then gap p a else 0 := by
  classical
  let d := if c a < limit p a then gap p a else 0
  calc
    _ = ∑ i, (gap p i * (min (c i) (limit p i) : ℕ) + if i = a then d else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        by_cases hc : c a < limit p a
        · have h0 : min (c a) (limit p a) = c a := min_eq_left (by omega)
          have h1 : min (c a + 1) (limit p a) = c a + 1 := min_eq_left (by omega)
          simp only [increment, ite_true, h0, h1, d, ite_eq_left hc, Nat.cast_add, Nat.cast_one]
          ring
        · have h0 : min (c a) (limit p a) = limit p a := min_eq_right (by omega)
          have h1 : min (c a + 1) (limit p a) = limit p a := min_eq_right (by omega)
          simp [increment, h0, h1, d, hc]
      · simp [increment, hi]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [potential, d]

lemma potential_increment_nonneg {p : Params} (hp : ∀ i, p.μ i ≤ p.μ p.best)
    (c : Counts p.k) (a : Arm p.k) :
    potential p c ≤ potential p (increment c a) := by
  rw [potential_increment]
  split_ifs <;> linarith [gap_nonneg hp a]

lemma radius_small {p : Params} (i : Arm p.k) (hg : 0 < gap p i)
    {t n : ℕ} (ht : t < p.T) (hn : limit p i ≤ n) :
    2 * radius t n < gap p i := by
  have hx : 8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2 < (n : ℝ) := by
    have hc := Nat.le_ceil (8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2)
    have hl : ⌈8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2⌉₊ + 1 ≤ n := by
      simpa [limit, hg] using hn
    have hlR : (⌈8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2⌉₊ : ℝ) + 1 ≤ n := by
      exact_mod_cast hl
    linarith
  have hnN : 0 < n := by
    have hl : 0 < limit p i := by simp [limit, hg]
    omega
  have hnR : (0 : ℝ) < n := by positivity
  have hlog := Real.log_le_log (show (0 : ℝ) < t + 1 by positivity)
    (show (t + 1 : ℝ) ≤ p.T + 1 by exact_mod_cast (show t + 1 ≤ p.T + 1 by omega))
  have hl0 : 0 ≤ Real.log (t + 1 : ℝ) :=
    Real.log_nonneg (by have h := Nat.cast_nonneg (α := ℝ) t; linarith)
  have hr : radius t n ^ 2 * n = 2 * Real.log (t + 1 : ℝ) := by
    rw [radius, Real.sq_sqrt (by positivity)]
    field_simp
  have hx' := (div_lt_iff₀ (sq_pos_of_pos hg)).mp hx
  have hm : (4 * radius t n ^ 2) * n < gap p i ^ 2 * n := by nlinarith
  have hs : 4 * radius t n ^ 2 < gap p i ^ 2 := (mul_lt_mul_iff_left₀ hnR).mp hm
  have hrad := Real.sqrt_nonneg (2 * Real.log (t + 1 : ℝ) / n)
  change 0 ≤ radius t n at hrad
  nlinarith

lemma selected_small {p : Params} (w : Sample p.k) {t : ℕ}
    (ht : t < p.T) (hk : p.k + 1 ≤ t) (hg : 0 < gap p (play w t))
    (hconf : ∀ i n, 0 < n → n ≤ t → |empirical w i n - p.μ i| ≤ radius t n) :
    (trajectory w t).1 (play w t) < limit p (play w t) := by
  by_contra hn
  have hpos (i : Arm p.k) : 0 < (trajectory w t).1 i :=
    count_pos w t i (by have := i.isLt; omega)
  have hb := hconf p.best _ (hpos p.best) (count_le w t p.best)
  have ha := hconf (play w t) _ (hpos (play w t)) (count_le w t (play w t))
  have hm : index t (trajectory w t) p.best ≤ index t (trajectory w t) (play w t) := by
    change index t (trajectory w t) p.best ≤ index t (trajectory w t) (select t (trajectory w t))
    rw [select, ite_eq_right (by omega)]
    exact le_maximum _ _
  rw [index_eq_empirical, index_eq_empirical] at hm
  have hsmall := radius_small (n := (trajectory w t).1 (play w t)) (play w t) hg ht (by omega)
  have hb' := (abs_le.mp hb).1
  have ha' := (abs_le.mp ha).2
  dsimp [gap] at hg hsmall
  linarith

lemma potential_le (p : Params) (hp : ∀ i, p.μ i ≤ p.μ p.best) (c : Counts p.k) :
    potential p c ≤ ∑ i, gap p i * limit p i := by
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.min_le_right (c i) (limit p i))
      (gap_nonneg hp i)

end LongTailsOnline.Proofs.Ucb
