import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic

open Finset

namespace OracleTemplate.ArrowHurwicz

def win (M : ℕ) : Finset ℤ := Icc (-(M : ℤ)) M

lemma mem_win {M : ℕ} {k : ℤ} : k ∈ win M ↔ |k| ≤ M := by
  unfold win; rw [mem_Icc, abs_le]

lemma win_reflect {R : Type*} [AddCommMonoid R] (M : ℕ) (c : ℤ) (f : ℤ → R)
    (hf : ∀ k, f k ≠ 0 → |k| ≤ M ∧ |c - k| ≤ M) :
    ∑ s ∈ win M, f (c - s) = ∑ k ∈ win M, f k := by
  apply sum_bij_ne_zero (fun s _ _ => c - s)
  · intro s _ hs; exact mem_win.mpr (hf _ hs).1
  · intro a _ _ b _ _ h; simpa using h
  · intro k hk hk0
    refine ⟨c - k, mem_win.mpr (hf k hk0).2, by simpa using hk0, by ring⟩
  · intro s _ _; rfl

lemma win_shift {R : Type*} [AddCommMonoid R] (M : ℕ) (c : ℤ) (f : ℤ → R)
    (hf : ∀ k, f k ≠ 0 → |k| ≤ M ∧ |k - c| ≤ M) :
    ∑ s ∈ win M, f (s + c) = ∑ k ∈ win M, f k := by
  apply sum_bij_ne_zero (fun s _ _ => s + c)
  · intro s _ hs; exact mem_win.mpr (hf _ hs).1
  · intro a _ _ b _ _ h; simpa using h
  · intro k hk hk0
    refine ⟨k - c, mem_win.mpr (hf k hk0).2, by simpa using hk0, by ring⟩
  · intro s _ _; rfl

lemma win_sum_range {R : Type*} [AddCommMonoid R] (M : ℕ) (a : ℤ) (n : ℕ) (f : ℤ → R)
    (hf : ∀ k, f k ≠ 0 → a ≤ k ∧ k < a + n) (ha : -(M : ℤ) ≤ a) (hb : a + n ≤ M + 1) :
    ∑ k ∈ win M, f k = ∑ i ∈ range n, f (a + i) := by
  symm
  refine sum_bij_ne_zero (s := range n) (t := win M) (f := fun i => f (a + i)) (g := f)
    (fun i _ _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi hi0
    have := (hf _ hi0)
    rw [mem_win, abs_le]; constructor <;> omega
  · intro i _ _ j _ _ h; simpa using h
  · intro k _ hk0
    obtain ⟨h1, h2⟩ := hf k hk0
    refine ⟨(k - a).toNat, mem_range.mpr (by omega), ?_, ?_⟩
    · rw [show a + ((k - a).toNat : ℤ) = k by omega]; exact hk0
    · rw [show a + ((k - a).toNat : ℤ) = k by omega]
  · intro i _ _; rfl

variable (T : ℕ)

lemma toeplitz_identity (M : ℕ) (η : ℝ) (P Kg : ℤ → ℤ → ℝ) (H : ℤ → ℝ)
    (hP : ∀ t s, P t s ≠ 0 → (1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T))
    (hK : ∀ t s, Kg t s ≠ 0 → (1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T))
    (hsym : ∀ t s, P t s = P s t) (hM : T + 1 ≤ M) :
    ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * (P t s - P (t + 1) s - η * Kg t s + η * Kg s (t + 1)) =
      ∑ t ∈ win M, ∑ s ∈ win M,
        ((H (t - s + 1) - H (-(t - s)) - (H (t - s) - H (-(t - s) + 1))) / 2 * P t s -
          η * (H (t - s + 1) - H (-(t - s))) * Kg t s) := by
  have sh1 : ∀ s ∈ win M, ∑ t ∈ win M, H (t + 1 - s) * P (t + 1) s =
      ∑ t ∈ win M, H (t - s) * P t s := by
    intro s _
    have := win_shift M 1 (fun t => H (t - s) * P t s) (by
      intro k hk
      have hp : P k s ≠ 0 := by intro h0; apply hk; simp [h0]
      have := (hP k s hp).1
      constructor <;> rw [abs_le] <;> constructor <;> omega)
    simpa [sub_add_eq_add_sub] using this
  have sh2 : ∀ s ∈ win M, ∑ t ∈ win M, H (t + 1 - s) * Kg s (t + 1) =
      ∑ t ∈ win M, H (t - s) * Kg s t := by
    intro s _
    have := win_shift M 1 (fun t => H (t - s) * Kg s t) (by
      intro k hk
      have hp : Kg s k ≠ 0 := by intro h0; apply hk; simp [h0]
      have := (hK s k hp).2
      constructor <;> rw [abs_le] <;> constructor <;> omega)
    simpa [sub_add_eq_add_sub] using this
  have A : ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * P (t + 1) s =
      ∑ t ∈ win M, ∑ s ∈ win M, H (t - s) * P t s := by
    rw [sum_comm, sum_congr rfl sh1, sum_comm]
  have B : ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * Kg s (t + 1) =
      ∑ t ∈ win M, ∑ s ∈ win M, H (s - t) * Kg t s := by
    rw [sum_comm, sum_congr rfl sh2]
  have e1 : ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * (P t s - P (t + 1) s - η * Kg t s + η * Kg s (t + 1)) =
      ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * P t s - ∑ t ∈ win M, ∑ s ∈ win M, H (t - s) * P t s -
        η * ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * Kg t s +
        η * ∑ t ∈ win M, ∑ s ∈ win M, H (s - t) * Kg t s := by
    rw [← A, ← B]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _; ring
  have e2 : ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * P t s =
      ∑ t ∈ win M, ∑ s ∈ win M, H (s + 1 - t) * P t s := by
    rw [sum_comm]; apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _; rw [hsym]
  have e3 : ∑ t ∈ win M, ∑ s ∈ win M, H (t - s) * P t s =
      ∑ t ∈ win M, ∑ s ∈ win M, H (s - t) * P t s := by
    rw [sum_comm]; apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _; rw [hsym]
  rw [e1]
  have h1 : ∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * P t s =
      (∑ t ∈ win M, ∑ s ∈ win M, H (t + 1 - s) * P t s + ∑ t ∈ win M, ∑ s ∈ win M, H (s + 1 - t) * P t s) / 2 := by
    rw [← e2]; ring
  have h2 : ∑ t ∈ win M, ∑ s ∈ win M, H (t - s) * P t s =
      (∑ t ∈ win M, ∑ s ∈ win M, H (t - s) * P t s + ∑ t ∈ win M, ∑ s ∈ win M, H (s - t) * P t s) / 2 := by
    rw [← e3]; ring
  rw [h1, h2]
  simp only [mul_sum, sum_div, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _
  rw [show s + 1 - t = -(t - s) + 1 by ring, show s - t = -(t - s) by ring,
    show t + 1 - s = t - s + 1 by ring]
  ring

lemma lag_tele (a : ℤ → ℝ) (B : ℝ) (ha : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ T) (hB : ∀ k, |a k| ≤ B)
    (k : ℤ) : |∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k))| ≤ |k| * B := by
  have az : ∀ k, ¬ (1 ≤ k ∧ k ≤ (T : ℤ)) → a k = 0 := by
    intro k hk; by_contra h; exact hk (ha k h)
  have step : ∀ k : ℤ, ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - (k + 1))) =
      ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k)) + (a (T - k) - a (-k)) := by
    intro k
    have := sum_range_sub (fun t : ℕ => a ((t : ℤ) - k)) T
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub] at this
    have e : ∀ t : ℕ, a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - (k + 1)) =
        (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k)) + (a ((t : ℤ) + 1 - k) - a ((t : ℤ) - k)) := by
      intro t; rw [show (t : ℤ) + 1 - (k + 1) = (t : ℤ) - k by ring]; ring
    simp_rw [e, sum_add_distrib]
    rw [show ∑ t ∈ range T, (a ((t : ℤ) + 1 - k) - a ((t : ℤ) - k)) = a (T - k) - a (-k) by
      rw [← this]]
  have inc : ∀ k : ℤ, |a (T - k) - a (-k)| ≤ B := by
    intro k
    by_cases hk : 0 ≤ k
    · rw [az (-k) (by omega), sub_zero]; exact hB _
    · rw [az (T - k) (by omega), zero_sub, abs_neg]; exact hB _
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [step]
    have := inc n
    calc _ ≤ |∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - n))| + |a (T - n) - a (-n)| := abs_add_le _ _
      _ ≤ |(n : ℤ)| * B + B := add_le_add ih this
      _ = |((n : ℤ) + 1 : ℤ)| * B := by
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ n), abs_of_nonneg (by omega : (0 : ℤ) ≤ n + 1)]
        push_cast; ring
  | pred n ih =>
    have h := step (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at h
    have e : ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - (-(n : ℤ) - 1))) =
        ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - -(n : ℤ))) - (a (T - (-(n : ℤ) - 1)) - a (-(-(n : ℤ) - 1))) := by
      linarith
    rw [e]
    have := inc (-(n : ℤ) - 1)
    calc _ ≤ |∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - -(n : ℤ)))| +
          |a (T - (-(n : ℤ) - 1)) - a (-(-(n : ℤ) - 1))| := abs_sub _ _
      _ ≤ |-(n : ℤ)| * B + B := add_le_add ih this
      _ = |(-(n : ℤ) - 1 : ℤ)| * B := by
        rw [abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ n), abs_of_nonpos (by omega : (-(n : ℤ) - 1) ≤ 0)]
        push_cast; ring

lemma lag_bound (M : ℕ) (F a : ℤ → ℝ) (B : ℝ) (ha : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ T)
    (hB : ∀ k, |a k| ≤ B) (hF : ∀ k, F k ≠ 0 → |k| ≤ T + 1) (hM : 2 * T + 1 ≤ M) :
    |∑ t ∈ range T, ∑ s ∈ win M, F ((t : ℤ) + 1 - s) * (a ((t : ℤ) + 1) - a s)| ≤
      B * ∑ k ∈ win M, |(k : ℝ)| * |F k| := by
  have e : ∀ t ∈ range T, ∑ s ∈ win M, F ((t : ℤ) + 1 - s) * (a ((t : ℤ) + 1) - a s) =
      ∑ k ∈ win M, F k * (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k)) := by
    intro t ht
    have ht' : (t : ℤ) < T := by exact_mod_cast mem_range.mp ht
    have := win_reflect M ((t : ℤ) + 1) (fun k => F k * (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k))) (by
      intro k hk
      have hFk : F k ≠ 0 := by intro h0; apply hk; simp [h0]
      have := hF k hFk
      rw [abs_le] at this ⊢
      constructor
      · constructor <;> omega
      · rw [abs_le]; constructor <;> omega)
    simpa using this
  rw [sum_congr rfl e, sum_comm]
  simp_rw [← mul_sum]
  calc |∑ k ∈ win M, F k * ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k))|
      ≤ ∑ k ∈ win M, |F k * ∑ t ∈ range T, (a ((t : ℤ) + 1) - a ((t : ℤ) + 1 - k))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ win M, |F k| * (|(k : ℝ)| * B) := by
        apply sum_le_sum; intro k _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := lag_tele T a B ha hB k
        rw [← Int.cast_abs]; exact_mod_cast this
    _ = B * ∑ k ∈ win M, |(k : ℝ)| * |F k| := by
        rw [mul_sum]; apply sum_congr rfl; intro k _; ring

end OracleTemplate.ArrowHurwicz
