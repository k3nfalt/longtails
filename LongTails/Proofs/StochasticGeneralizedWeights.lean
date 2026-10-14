import LongTails.Proofs.DampedGeneralizedDynamics

open scoped BigOperators

namespace OracleTemplate.StochasticGeneralized

lemma weight_scale_lower {G A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (heq : G * a ^ 2 = A + a) : 1 ≤ G * a := by
  by_contra h
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge h) ha
  nlinarith

lemma weight_after_up {G A a b a' : ℝ} (hG : 0 < G) (hA : 0 ≤ A)
    (ha : 0 < a) (heq : G * a ^ 2 = A + a) (hb : b ≤ a)
    (heq' : (16 * G) * a' ^ 2 = A + b + a') : a' ≤ 5 / 16 * a := by
  have hGa := weight_scale_lower hA ha heq
  by_contra h
  have hd : 0 < a' - 5 / 16 * a := by linarith
  have hder : 0 < 16 * G * (a' + 5 / 16 * a) - 1 := by
    have hm := mul_pos hG hd
    nlinarith
  have hp := mul_pos hd hder
  have hGa' := mul_le_mul_of_nonneg_right hGa ha.le
  nlinarith

lemma weight_after_down {G A a a' : ℝ} (hG : 0 < G) (hA : 0 ≤ A)
    (ha : 0 < a) (heq : G * a ^ 2 = A + a)
    (heq' : (G / 16) * a' ^ 2 = A + a + a') : a' ≤ 20 * a := by
  have hGa := weight_scale_lower hA ha heq
  by_contra h
  have hd : 0 < a' - 20 * a := by linarith
  have hder : 0 < G / 16 * (a' + 20 * a) - 1 := by
    have hm := mul_pos hG hd
    nlinarith
  have hp := mul_pos hd hder
  nlinarith

lemma initial_weight_le {G A a T : ℝ} (hT : 0 < T) (hA : A ≤ T)
    (hG : 1 / T ≤ G) (ha : 0 < a) (heq : G * a ^ 2 = A + a) :
    a ≤ 2 * T := by
  have hGT : 1 ≤ G * T := by
    simpa only [one_div_mul_cancel hT.ne'] using
      mul_le_mul_of_nonneg_right hG hT.le
  have hs := mul_le_mul_of_nonneg_right hGT (sq_nonneg a)
  have he := congrArg (fun x => x * T) heq
  have hAT := mul_le_mul_of_nonneg_right hA hT.le
  by_contra h
  have hp : 0 < (a - 2 * T) * (a + T) := mul_pos (by linarith) (by positivity)
  nlinarith

lemma nominal_sum_invariant (a A : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ i < n, a (i+1) ≤ 5 / 16 * a i + 20 * (A (i+1) - A i)) :
    11 / 16 * (∑ i ∈ Finset.range n, a i) + a n ≤ a 0 + 20 * (A n - A 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hi => hrec i (by omega))
    have hs := hrec n (by omega)
    rw [Finset.sum_range_succ]
    linarith

lemma nominal_sum_le (a A : ℕ → ℝ) (n : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (ha : ∀ i < n, 0 ≤ a i) (hA0 : 0 ≤ A 0) (ha0 : a 0 ≤ 2 * T)
    (hstop : ∀ i < n, A i ≤ T)
    (hrec : ∀ i < n, a (i+1) ≤ 5 / 16 * a i + 20 * (A (i+1) - A i)) :
    (∑ i ∈ Finset.range n, a i) ≤ 32 * T := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    have hi := nominal_sum_invariant a A n (fun i hi => hrec i (by omega))
    have hs := hstop n (by omega)
    have hn := ha n (by omega)
    rw [Finset.sum_range_succ]
    linarith

lemma rounded_batch_le {r : ℝ} (hr : 0 ≤ r) :
    ((max 1 ⌈r⌉₊ : ℕ) : ℝ) ≤ 1+r := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by have h := Nat.ceil_lt_add_one hr; linarith)

lemma batch_calls_le (m : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) {C T : ℝ}
    (hC : 0 ≤ C) (hm : ∀ i < n, (m i : ℝ) ≤ 1+C*a i)
    (hsum : (∑ i ∈ Finset.range n, a i) ≤ 32*T) :
    ((2*∑ i ∈ Finset.range n, m i : ℕ) : ℝ) ≤ 2*n+64*C*T := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum] at h
  have hs := mul_le_mul_of_nonneg_left hsum hC
  push_cast
  nlinarith only [h, hs]

lemma preterminal_weight_le (a A : ℕ → ℝ) (n : ℕ) {T : ℝ}
    (ha : ∀ i < n, 0 ≤ a i) (hA0 : 0 ≤ A 0) (ha0 : a 0 ≤ 2*T) (hAn : A n ≤ T)
    (hrec : ∀ i < n, a (i+1) ≤ 5/16*a i+20*(A (i+1)-A i)) :
    a n ≤ 22*T := by
  have hi := nominal_sum_invariant a A n hrec
  have hs : 0 ≤ ∑ i ∈ Finset.range n, a i :=
    Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  linarith

lemma active_nominal_invariant (a w A : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ i < n, a (i+1) ≤ a i-11/16*w i+20*(A (i+1)-A i)) :
    11/16*(∑ i ∈ Finset.range n, w i)+a n ≤ a 0+20*(A n-A 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hi => hrec i (by omega))
    have hs := hrec n (by omega)
    rw [Finset.sum_range_succ]
    linarith

lemma active_nominal_sum_le (a w A : ℕ → ℝ) (n : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hw : ∀ i < n, 0 ≤ w i) (hA0 : 0 ≤ A 0) (ha0 : a 0 ≤ 2*T)
    (hactive : ∀ i < n, w i ≠ 0 → w i = a i ∧ A i ≤ T)
    (hrec : ∀ i < n, a (i+1) ≤ a i-11/16*w i+20*(A (i+1)-A i)) :
    (∑ i ∈ Finset.range n, w i) ≤ 32*T := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : w n = 0
    · rw [hn, add_zero]
      exact ih (fun i hi => hw i (by omega))
        (fun i hi => hactive i (by omega)) (fun i hi => hrec i (by omega))
    · have h := hactive n (by omega) hn
      have hi := active_nominal_invariant a w A n (fun i hi => hrec i (by omega))
      have hn0 := hw n (by omega)
      rw [← h.1] at hi
      linarith [h.2]

lemma active_raw_weight_le (a w A : ℕ → ℝ) (n : ℕ) {T : ℝ}
    (hw : ∀ i < n, 0 ≤ w i) (hA0 : 0 ≤ A 0) (ha0 : a 0 ≤ 2*T) (hAn : A n ≤ T)
    (hrec : ∀ i < n, a (i+1) ≤ a i-11/16*w i+20*(A (i+1)-A i)) :
    a n ≤ 22*T := by
  have hi := active_nominal_invariant a w A n hrec
  have hs : 0 ≤ ∑ i ∈ Finset.range n, w i :=
    Finset.sum_nonneg (fun i hi => hw i (Finset.mem_range.mp hi))
  linarith

end OracleTemplate.StochasticGeneralized
