import LongTails.Algorithms.RegretMatchingPotential
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset

namespace OracleTemplate.RegretMatchingPotential

variable {m : ℕ}

noncomputable def sqNorm (Q : Fin m → ℝ) : ℝ := ∑ a, Q a ^ 2

lemma total_nonneg {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ total Q :=
  sum_nonneg fun a _ => hQ a

lemma total_eq_zero {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (h : ¬ 0 < total Q) :
    ∀ a, Q a = 0 := by
  have h0 : total Q = 0 := le_antisymm (not_lt.mp h) (total_nonneg hQ)
  exact fun a => (sum_eq_zero_iff_of_nonneg fun b _ => hQ b).mp h0 a (mem_univ a)

lemma strategy_nonneg {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (a : Fin m) :
    0 ≤ strategy Q a := by
  unfold strategy
  split_ifs with h
  · exact div_nonneg (hQ a) h.le
  · positivity

lemma strategy_sum (hm : 0 < m) {Q : Fin m → ℝ} : ∑ a, strategy Q a = 1 := by
  unfold strategy
  split_ifs with h
  · rw [← sum_div]; exact div_self h.ne'
  · simp [card_univ, Fintype.card_fin]; field_simp

lemma value_regret (hm : 0 < m) (Q u : Fin m → ℝ) :
    value (strategy Q) (regret Q u) = 0 := by
  unfold value regret
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, strategy_sum hm, one_mul]
  unfold value; ring

lemma inner_regret (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    ∑ a, Q a * regret Q u a = 0 := by
  by_cases h : 0 < total Q
  · have hv := value_regret hm Q u
    unfold value strategy at hv
    simp only [h, ↓reduceIte] at hv
    have : ∑ a, Q a * regret Q u a = total Q * ∑ a, Q a / total Q * regret Q u a := by
      rw [mul_sum]; refine sum_congr rfl fun a _ => ?_; field_simp
    rw [this, hv, mul_zero]
  · have hz := total_eq_zero hQ h
    simp [hz]

lemma step_nonneg (Q u : Fin m → ℝ) (a : Fin m) : 0 ≤ step Q u a := le_max_right _ _

lemma step_ge (Q u : Fin m → ℝ) (a : Fin m) : Q a + regret Q u a ≤ step Q u a :=
  le_max_left _ _

lemma inner_increment_nonneg (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a)
    (u : Fin m → ℝ) : 0 ≤ ∑ a, Q a * (step Q u a - Q a) := by
  have h0 := inner_regret hm hQ u
  have : ∑ a, Q a * regret Q u a ≤ ∑ a, Q a * (step Q u a - Q a) :=
    sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (by linarith [step_ge Q u a]) (hQ a)
  linarith

lemma sqNorm_growth (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    sqNorm Q + ∑ a, (step Q u a - Q a) ^ 2 ≤ sqNorm (step Q u) := by
  have h := inner_increment_nonneg hm hQ u
  have e : sqNorm (step Q u) =
      sqNorm Q + 2 * ∑ a, Q a * (step Q u a - Q a) + ∑ a, (step Q u a - Q a) ^ 2 := by
    unfold sqNorm; rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_; ring
  linarith

lemma sqNorm_mono (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    sqNorm Q ≤ sqNorm (step Q u) := by
  have := sqNorm_growth hm hQ u
  have : 0 ≤ ∑ a, (step Q u a - Q a) ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  linarith


noncomputable def inc (Q u : Fin m → ℝ) : Fin m → ℝ := fun a => step Q u a - Q a

noncomputable def gain (Q u : Fin m → ℝ) : ℝ :=
  value (strategy (step Q u)) u - value (strategy Q) u

noncomputable def size (Q : Fin m → ℝ) : ℝ := Real.sqrt (sqNorm Q)

lemma sqNorm_nonneg (Q : Fin m → ℝ) : 0 ≤ sqNorm Q := sum_nonneg fun _ _ => sq_nonneg _

lemma size_sq (Q : Fin m → ℝ) : size Q ^ 2 = sqNorm Q := Real.sq_sqrt (sqNorm_nonneg Q)

lemma size_nonneg (Q : Fin m → ℝ) : 0 ≤ size Q := Real.sqrt_nonneg _

lemma size_mono (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    size Q ≤ size (step Q u) := Real.sqrt_le_sqrt (sqNorm_mono hm hQ u)

lemma step_eq (Q u : Fin m → ℝ) (a : Fin m) : step Q u a = Q a + inc Q u a := by
  unfold inc; ring

lemma regret_le_inc (Q u : Fin m → ℝ) (a : Fin m) : regret Q u a ≤ inc Q u a := by
  unfold inc; linarith [step_ge Q u a]

lemma value_shift (hm : 0 < m) (Q u : Fin m → ℝ) (c : ℝ) :
    value (strategy Q) (fun a => u a - c) = value (strategy Q) u - c := by
  unfold value
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, strategy_sum hm, one_mul]

lemma gain_eq (hm : 0 < m) (Q u : Fin m → ℝ) :
    gain Q u = value (strategy (step Q u)) (regret Q u) :=
  (value_shift hm (step Q u) u (value (strategy Q) u)).symm

lemma step_mul_regret (Q u : Fin m → ℝ) (a : Fin m) :
    step Q u a * regret Q u a = step Q u a * inc Q u a := by
  unfold inc step
  rcases le_total 0 (Q a + regret Q u a) with h | h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right h]; ring

lemma strategy_of_pos {Q : Fin m → ℝ} (h : 0 < total Q) (a : Fin m) :
    strategy Q a = Q a / total Q := by
  unfold strategy; simp [h]

lemma value_le {x v : Fin m → ℝ} (hx : ∀ a, 0 ≤ x a) (hs : ∑ a, x a = 1) {c : ℝ}
    (hv : ∀ a, v a ≤ c) : value x v ≤ c := by
  unfold value
  calc ∑ a, x a * v a ≤ ∑ a, x a * c := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hv a) (hx a)
    _ = c := by rw [← sum_mul, hs, one_mul]

lemma le_value {x v : Fin m → ℝ} (hx : ∀ a, 0 ≤ x a) (hs : ∑ a, x a = 1) {c : ℝ}
    (hv : ∀ a, c ≤ v a) : c ≤ value x v := by
  unfold value
  calc c = ∑ a, x a * c := by rw [← sum_mul, hs, one_mul]
    _ ≤ ∑ a, x a * v a := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hv a) (hx a)

lemma value_mono {x v w : Fin m → ℝ} (hx : ∀ a, 0 ≤ x a) (h : ∀ a, v a ≤ w a) :
    value x v ≤ value x w :=
  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hx a)

lemma sum_step_mul_inc (Q u : Fin m → ℝ) :
    ∑ a, step Q u a * inc Q u a = ∑ a, Q a * inc Q u a + ∑ a, inc Q u a ^ 2 := by
  rw [← sum_add_distrib]; refine sum_congr rfl fun a _ => ?_; rw [step_eq]; ring

lemma sqNorm_step (Q u : Fin m → ℝ) :
    sqNorm (step Q u) = sqNorm Q + 2 * ∑ a, Q a * inc Q u a + ∑ a, inc Q u a ^ 2 := by
  unfold sqNorm; rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_; rw [step_eq]; ring

lemma inner_inc_nonneg (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    0 ≤ ∑ a, Q a * inc Q u a := inner_increment_nonneg hm hQ u

lemma sum_inc_sq_le (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    ∑ a, inc Q u a ^ 2 ≤ sqNorm (step Q u) - sqNorm Q := by
  rw [sqNorm_step]; linarith [inner_inc_nonneg hm hQ u]

lemma step_zero (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ)
    (h : ¬ 0 < total (step Q u)) : Q = 0 ∧ step Q u = 0 := by
  have h1 := total_eq_zero (step_nonneg Q u) h
  have h2 := inner_inc_nonneg hm hQ u
  have e : ∑ a, Q a * inc Q u a = -∑ a, Q a ^ 2 := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun a _ => ?_; unfold inc; rw [h1 a]; ring
  have h3 : ∑ a, Q a ^ 2 = 0 :=
    le_antisymm (by linarith) (sum_nonneg fun a _ => sq_nonneg _)
  have h4 : ∀ a, Q a = 0 := fun a =>
    pow_eq_zero_iff (two_ne_zero) |>.mp
      ((sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (Q b)).mp h3 a (mem_univ a))
  exact ⟨funext h4, funext h1⟩

lemma gain_mul_total (hm : 0 < m) (Q u : Fin m → ℝ) (h : 0 < total (step Q u)) :
    gain Q u * total (step Q u) = ∑ a, step Q u a * inc Q u a := by
  rw [gain_eq hm]; unfold value
  simp only [strategy_of_pos h]
  rw [sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ h.ne', step_mul_regret]

lemma inc_sq_le_gain (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    ∑ a, inc Q u a ^ 2 ≤ gain Q u * total (step Q u) := by
  by_cases h : 0 < total (step Q u)
  · rw [gain_mul_total hm Q u h, sum_step_mul_inc]; linarith [inner_inc_nonneg hm hQ u]
  · obtain ⟨h1, h2⟩ := step_zero hm hQ u h
    have : ∀ a, inc Q u a = 0 := fun a => by
      unfold inc; rw [h2, h1]; simp
    simp [this, total, h2]

lemma gain_nonneg (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    0 ≤ gain Q u := by
  by_cases h : 0 < total (step Q u)
  · have h1 := inc_sq_le_gain hm hQ u
    have h2 : 0 ≤ ∑ a, inc Q u a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    exact le_of_mul_le_mul_right (by linarith) h
  · obtain ⟨h1, h2⟩ := step_zero hm hQ u h
    unfold gain; rw [h2, ← h1]; simp

lemma regret_le {Q u : Fin m → ℝ} (hm : 0 < m) (hQ : ∀ a, 0 ≤ Q a) {B : ℝ}
    (hu : ∀ a b, u a - u b ≤ B) (a : Fin m) : regret Q u a ≤ B := by
  unfold regret
  have := le_value (v := u) (strategy_nonneg hQ) (strategy_sum hm) (c := u a - B)
    (fun b => by linarith [hu a b])
  linarith

lemma gain_le (hm : 0 < m) {Q u : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) {B : ℝ}
    (hu : ∀ a b, u a - u b ≤ B) : gain Q u ≤ B := by
  rw [gain_eq hm]
  exact value_le (strategy_nonneg (step_nonneg Q u)) (strategy_sum hm) (regret_le hm hQ hu)

lemma sqNorm_step_sub_le (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    sqNorm (step Q u) - sqNorm Q ≤ 2 * gain Q u * total (step Q u) := by
  by_cases h : 0 < total (step Q u)
  · have e := gain_mul_total hm Q u h
    rw [sum_step_mul_inc] at e
    rw [sqNorm_step]
    have : 0 ≤ ∑ a, inc Q u a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    nlinarith
  · obtain ⟨h1, h2⟩ := step_zero hm hQ u h
    rw [h2, h1]; simp [sqNorm, total]

lemma total_le_size (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) :
    total Q ≤ m * size Q := by
  have h1 : total Q ^ 2 ≤ m * sqNorm Q := by
    have := sq_sum_le_card_mul_sum_sq (s := univ) (f := Q)
    simpa [card_univ, Fintype.card_fin, total, sqNorm] using this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : total Q ^ 2 ≤ (m * size Q) ^ 2 := by
    rw [mul_pow, size_sq]
    nlinarith [sqNorm_nonneg Q]
  exact (pow_le_pow_iff_left₀ (total_nonneg hQ)
    (mul_nonneg (by linarith) (size_nonneg Q)) two_ne_zero).mp h2

lemma size_le_total {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) : size Q ≤ total Q := by
  have h := sum_sq_le_sq_sum_of_nonneg (s := univ) (f := Q) fun a _ => hQ a
  have : |total Q| = total Q := abs_of_nonneg (total_nonneg hQ)
  rw [← this]
  exact Real.sqrt_le_sqrt h |>.trans (by rw [Real.sqrt_sq_eq_abs]; rfl)

lemma charge (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) :
    size (step Q u) - size Q ≤ 2 * m * gain Q u := by
  have h1 := sqNorm_step_sub_le hm hQ u
  have h2 := total_le_size hm (step_nonneg Q u)
  have hg := gain_nonneg hm hQ u
  have hR := size_mono hm hQ u
  have hR0 := size_nonneg Q
  have e1 := size_sq Q
  have e2 := size_sq (step Q u)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h3 : (size (step Q u) - size Q) * (size (step Q u) + size Q) ≤
      2 * m * gain Q u * size (step Q u) := by
    have : 2 * gain Q u * total (step Q u) ≤ 2 * gain Q u * (m * size (step Q u)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith
  by_contra hc
  rw [not_le] at hc
  have hpos : 0 < size (step Q u) := by nlinarith [mul_nonneg hm0 hg]
  nlinarith [mul_nonneg (mul_nonneg hm0 hg) hR0]

lemma coord_le_size {Q : Fin m → ℝ} (a : Fin m) : Q a ≤ size Q :=
  (le_abs_self _).trans (Real.abs_le_sqrt
    (single_le_sum (f := fun b => Q b ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)))


lemma lagged_le (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u v : Fin m → ℝ) :
    value (strategy Q) (regret (step Q u) v) ≤ 2 * (size (step (step Q u) v) - size Q) := by
  have hQ1 : ∀ a, 0 ≤ step Q u a := step_nonneg Q u
  have hb : value (strategy Q) (regret (step Q u) v) ≤ size (step (step Q u) v) :=
    value_le (strategy_nonneg hQ) (strategy_sum hm) fun a =>
      (show regret (step Q u) v a ≤ step (step Q u) v a by
        linarith [step_ge (step Q u) v a, hQ1 a]).trans (coord_le_size a)
  have hmono : size Q ≤ size (step (step Q u) v) :=
    (size_mono hm hQ u).trans (size_mono hm hQ1 v)
  by_cases h0 : size Q = 0
  · rw [h0]; linarith [size_nonneg (step (step Q u) v)]
  have hpos : 0 < size Q := lt_of_le_of_ne (size_nonneg Q) (Ne.symm h0)
  have htot : 0 < total Q := lt_of_lt_of_le hpos (size_le_total hQ)
  have h1 : value (strategy Q) (regret (step Q u) v) ≤ (∑ a, Q a * inc (step Q u) v a) / total Q := by
    calc _ ≤ value (strategy Q) (inc (step Q u) v) :=
          value_mono (strategy_nonneg hQ) (regret_le_inc (step Q u) v)
      _ = _ := by
          unfold value; simp only [strategy_of_pos htot]; rw [sum_div]
          exact sum_congr rfl fun a _ => by ring
  have h2 : 2 * ∑ a, Q a * inc (step Q u) v a ≤ sqNorm (step (step Q u) v) - sqNorm Q := by
    have e1 := sqNorm_step (step Q u) v
    have g0 := sum_inc_sq_le hm hQ u
    have e2 : ∑ a, Q a * inc (step Q u) v a =
        ∑ a, step Q u a * inc (step Q u) v a - ∑ a, inc Q u a * inc (step Q u) v a := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun a _ => ?_; rw [step_eq Q u a]; ring
    have e3 : 0 ≤ ∑ a, (inc Q u a + inc (step Q u) v a) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have e4 : ∑ a, (inc Q u a + inc (step Q u) v a) ^ 2 = ∑ a, inc Q u a ^ 2 +
        2 * ∑ a, inc Q u a * inc (step Q u) v a + ∑ a, inc (step Q u) v a ^ 2 := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    linarith
  have hN : sqNorm Q ≤ sqNorm (step (step Q u) v) :=
    (sqNorm_mono hm hQ u).trans (sqNorm_mono hm hQ1 v)
  rw [← size_sq Q, ← size_sq (step (step Q u) v)] at h2 hN
  set a := size Q
  set b := size (step (step Q u) v)
  set w := value (strategy Q) (regret (step Q u) v)
  have h3 : w * (2 * a) ≤ b ^ 2 - a ^ 2 := by
    rcases le_or_gt w 0 with hw | hw
    · nlinarith
    · have : w * total Q ≤ ∑ a, Q a * inc (step Q u) v a := by
        rw [le_div_iff₀ htot] at h1; exact h1
      have : w * a ≤ w * total Q := mul_le_mul_of_nonneg_left (size_le_total hQ) hw.le
      linarith
  rcases le_or_gt (2 * a) b with hb2 | hb2
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hmono) (by linarith : (0 : ℝ) ≤ 3 * a - b)]

lemma regret_sq_le (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) {a : Fin m}
    (ha : 0 ≤ regret Q u a) : regret Q u a ^ 2 ≤ sqNorm (step Q u) - sqNorm Q := by
  have h1 := sum_inc_sq_le hm hQ u
  have h2 : inc Q u a ^ 2 ≤ ∑ b, inc Q u b ^ 2 :=
    single_le_sum (f := fun b => inc Q u b ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)
  have h3 := regret_le_inc Q u a
  nlinarith

lemma move_sq_le (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ a, 0 ≤ Q a) (u : Fin m → ℝ) {K : ℝ}
    (hK : 0 < K) (hKQ : K ≤ size Q) :
    K * (∑ a, |strategy (step Q u) a - strategy Q a|) ^ 2 ≤ 4 * m * gain Q u := by
  have hs : 0 < total Q := lt_of_lt_of_le hK (hKQ.trans (size_le_total hQ))
  have hKs : K ≤ total (step Q u) :=
    hKQ.trans ((size_mono hm hQ u).trans (size_le_total (step_nonneg Q u)))
  have hs' : 0 < total (step Q u) := lt_of_lt_of_le hK hKs
  set L := ∑ a, |inc Q u a|
  set d := ∑ a, |strategy (step Q u) a - strategy Q a|
  have hdiff : |total Q - total (step Q u)| ≤ L := by
    have : total (step Q u) - total Q = ∑ a, inc Q u a := by
      unfold total; rw [← sum_sub_distrib]; exact sum_congr rfl fun a _ => by rw [step_eq]; ring
    rw [abs_sub_comm, this]; exact abs_sum_le_sum_abs _ _
  have hcoord : ∀ a, |strategy (step Q u) a - strategy Q a| * total (step Q u) ≤
      |inc Q u a| + Q a / total Q * |total Q - total (step Q u)| := by
    intro a
    rw [strategy_of_pos hs', strategy_of_pos hs]
    have e : (step Q u a / total (step Q u) - Q a / total Q) * total (step Q u) =
        inc Q u a + Q a / total Q * (total Q - total (step Q u)) := by
      rw [step_eq]; field_simp; ring
    have e2 : |step Q u a / total (step Q u) - Q a / total Q| * total (step Q u) =
        |(step Q u a / total (step Q u) - Q a / total Q) * total (step Q u)| := by
      rw [abs_mul, abs_of_pos hs']
    rw [e2, e]
    calc _ ≤ |inc Q u a| + |Q a / total Q * (total Q - total (step Q u))| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (div_nonneg (hQ a) hs.le)]
  have hd : d * total (step Q u) ≤ 2 * L := by
    have hsum : ∑ a, Q a / total Q = 1 := by rw [← sum_div]; exact div_self hs.ne'
    calc d * total (step Q u) = ∑ a, |strategy (step Q u) a - strategy Q a| * total (step Q u) := sum_mul _ _ _
      _ ≤ ∑ a, (|inc Q u a| + Q a / total Q * |total Q - total (step Q u)|) := sum_le_sum fun a _ => hcoord a
      _ = L + |total Q - total (step Q u)| := by rw [sum_add_distrib, ← sum_mul, hsum, one_mul]
      _ ≤ 2 * L := by linarith
  have hL : L ^ 2 ≤ m * ∑ a, inc Q u a ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun a => |inc Q u a|)
    simpa [card_univ, Fintype.card_fin, sq_abs] using this
  have hg := inc_sq_le_gain hm hQ u
  have hd0 : 0 ≤ d := sum_nonneg fun _ _ => abs_nonneg _
  have hL0 : 0 ≤ L := sum_nonneg fun _ _ => abs_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (d * total (step Q u)) ^ 2 ≤ 4 * m * gain Q u * total (step Q u) := by
    have : (d * total (step Q u)) ^ 2 ≤ (2 * L) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hd0 hs'.le) hd 2
    nlinarith
  have h2 : d ^ 2 * total (step Q u) ≤ 4 * m * gain Q u := by
    have : d ^ 2 * total (step Q u) * total (step Q u) ≤ 4 * m * gain Q u * total (step Q u) := by
      nlinarith
    exact le_of_mul_le_mul_right this hs'
  nlinarith [sq_nonneg d]

end OracleTemplate.RegretMatchingPotential
