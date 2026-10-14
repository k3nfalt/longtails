import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace OracleTemplate.SampledConvex

noncomputable def step (η : ℝ) (T k : ℕ) : ℝ := η * ((T : ℝ) - k) / T

noncomputable def tail (η : ℝ) (T k : ℕ) : ℝ := η * ((T : ℝ) - k) * ((T : ℝ) - k + 1) / (2 * T)

noncomputable def charge (L η : ℝ) (T k : ℕ) : ℝ := 2 * L * step η T k ^ 2 * (1 + L * step η T k)

noncomputable def weight (L η : ℝ) (T : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => weight L η T k * tail η T k / (tail η T (k + 1) + charge L η T (k + 1))

lemma tail_succ (η : ℝ) (T k : ℕ) (hT : 0 < T) :
    tail η T k = tail η T (k + 1) + step η T k := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [tail, step, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma step_pos {η : ℝ} {T k : ℕ} (hη : 0 < η) (hk : k < T) : 0 < step η T k := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hk' : (k : ℝ) < T := by exact_mod_cast hk
  unfold step
  apply div_pos (mul_pos hη (by linarith)) hT

lemma step_le {η : ℝ} {T k : ℕ} (hη : 0 ≤ η) (hk : k < T) : step η T k ≤ η := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  unfold step
  rw [div_le_iff₀ hT]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma tail_pos {η : ℝ} {T k : ℕ} (hη : 0 < η) (hk : k < T) : 0 < tail η T k := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hk' : (k : ℝ) < T := by exact_mod_cast hk
  unfold tail
  apply div_pos _ (by positivity)
  exact mul_pos (mul_pos hη (by linarith)) (by linarith)

lemma tail_nonneg {η : ℝ} {T k : ℕ} (hη : 0 ≤ η) (hk : k ≤ T) : 0 ≤ tail η T k := by
  have hk' : (k : ℝ) ≤ T := by exact_mod_cast hk
  unfold tail
  apply div_nonneg _ (by positivity)
  exact mul_nonneg (mul_nonneg hη (by linarith)) (by linarith)

lemma tail_last {η : ℝ} {T : ℕ} (hT : 0 < T) : tail η T (T - 1) = step η T (T - 1) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hT.ne'), Nat.cast_one]
  simp only [tail, step, hc]
  field_simp
  ring

lemma tail_zero {η : ℝ} {T : ℕ} (hT : 0 < T) : tail η T 0 = η * ((T : ℝ) + 1) / 2 := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [tail, Nat.cast_zero, sub_zero]
  field_simp

lemma ratio_le {η : ℝ} {T k : ℕ} (hη : 0 < η) (hk : k < T) :
    step η T k ^ 2 / tail η T k ≤ 2 * η / T := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hk' : (k : ℝ) < T := by exact_mod_cast hk
  rw [div_le_div_iff₀ (tail_pos hη hk) hT]
  unfold step tail
  have h1 : 0 < (T : ℝ) - k := by linarith
  field_simp
  nlinarith [mul_pos (mul_pos hη hη) (mul_pos h1 h1), mul_pos hη h1]

lemma ratio_sum {η : ℝ} {T : ℕ} (hη : 0 < η) (m : ℕ) (hm : m ≤ T) :
    ∑ k ∈ range m, step η T k ^ 2 / tail η T k ≤ 2 * η := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    simp
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  calc ∑ k ∈ range m, step η T k ^ 2 / tail η T k ≤ ∑ _k ∈ range m, 2 * η / T :=
        sum_le_sum (fun k hk => ratio_le hη (lt_of_lt_of_le (mem_range.mp hk) hm))
    _ = m * (2 * η / T) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ T * (2 * η / T) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
    _ = 2 * η := by field_simp

lemma charge_nonneg {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (T k : ℕ) (hk : k ≤ T) :
    0 ≤ charge L η T k := by
  have hs : 0 ≤ step η T k := by
    unfold step
    have hk' : (k : ℝ) ≤ T := by exact_mod_cast hk
    apply div_nonneg (mul_nonneg hη (by linarith)) (Nat.cast_nonneg _)
  unfold charge
  positivity

lemma charge_le {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T k : ℕ}
    (hk : k < T) : charge L η T k ≤ (9 / 32) * step η T k := by
  have hs := step_pos hη hk
  have hsl := step_le hη.le hk
  have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hsl hL) hLη
  unfold charge
  have h1 : 2 * L * step η T k ^ 2 * (1 + L * step η T k) =
      step η T k * (2 * (L * step η T k) * (1 + L * step η T k)) := by ring
  rw [h1, mul_comm (9 / 32 : ℝ)]
  have : 0 ≤ L * step η T k := mul_nonneg hL hs.le
  have h2 : 2 * (L * step η T k) * (1 + L * step η T k) ≤ 9 / 32 := by nlinarith
  exact mul_le_mul_of_nonneg_left h2 hs.le

lemma charge_sum {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ} (m : ℕ)
    (hm : m ≤ T) : ∑ k ∈ range m, charge L η T k / tail η T k ≤ 9 / 16 := by
  have hb : ∀ k ∈ range m, charge L η T k / tail η T k ≤
      (9 / 4 * L) * (step η T k ^ 2 / tail η T k) := by
    intro k hk
    have hkT := lt_of_lt_of_le (mem_range.mp hk) hm
    have ht := tail_pos hη hkT
    have hs := step_le hη.le hkT
    have hsp := step_pos hη hkT
    have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hs hL) hLη
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right ht]
    unfold charge
    have : 0 ≤ L * step η T k := mul_nonneg hL hsp.le
    nlinarith [mul_nonneg hL (sq_nonneg (step η T k))]
  calc ∑ k ∈ range m, charge L η T k / tail η T k ≤
        ∑ k ∈ range m, (9 / 4 * L) * (step η T k ^ 2 / tail η T k) := sum_le_sum hb
    _ = (9 / 4 * L) * ∑ k ∈ range m, step η T k ^ 2 / tail η T k := by rw [mul_sum]
    _ ≤ (9 / 4 * L) * (2 * η) := mul_le_mul_of_nonneg_left (ratio_sum hη m hm) (by positivity)
    _ ≤ 9 / 16 := by nlinarith

lemma weight_identity {L η : ℝ} {T k : ℕ} (hL : 0 ≤ L) (hη : 0 < η) (hk : k + 1 < T) :
    weight L η T (k + 1) * (tail η T (k + 1) + charge L η T (k + 1)) =
      weight L η T k * tail η T k := by
  have hpos : 0 < tail η T (k + 1) + charge L η T (k + 1) :=
    add_pos_of_pos_of_nonneg (tail_pos hη hk) (charge_nonneg hL hη.le T (k + 1) hk.le)
  simp only [weight]
  field_simp

lemma weight_bounds {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ} :
    ∀ k, k < T → 0 < weight L η T k ∧
      weight L η T k * tail η T k ≤ tail η T 0 ∧
      tail η T 0 * (1 - ∑ j ∈ range k, charge L η T (j + 1) / tail η T (j + 1)) ≤
        weight L η T k * tail η T k := by
  intro k
  induction k with
  | zero =>
    intro hT
    simp only [weight, one_mul, range_zero, sum_empty, sub_zero, mul_one]
    exact ⟨one_pos, le_rfl, le_rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hv, hup, hlow⟩ := ih (lt_trans (Nat.lt_succ_self k) hk)
    have ht := tail_pos hη hk
    have ht0 := tail_pos hη (lt_trans (Nat.lt_succ_self k) hk)
    have hc := charge_nonneg hL hη.le T (k + 1) hk.le
    have hid := weight_identity hL hη hk
    have hden : 0 < tail η T (k + 1) + charge L η T (k + 1) := add_pos_of_pos_of_nonneg ht hc
    have hv' : 0 < weight L η T (k + 1) := by
      simp only [weight]
      exact div_pos (mul_pos hv ht0) hden
    refine ⟨hv', ?_, ?_⟩
    · have : weight L η T (k + 1) * tail η T (k + 1) ≤
          weight L η T (k + 1) * (tail η T (k + 1) + charge L η T (k + 1)) := by nlinarith
      linarith
    · rw [sum_range_succ]
      have hrat : weight L η T (k + 1) * tail η T (k + 1) =
          weight L η T k * tail η T k * (tail η T (k + 1) /
            (tail η T (k + 1) + charge L η T (k + 1))) := by
        rw [← hid]
        field_simp
      have hsplit : tail η T (k + 1) / (tail η T (k + 1) + charge L η T (k + 1)) =
          1 - charge L η T (k + 1) / (tail η T (k + 1) + charge L η T (k + 1)) := by
        field_simp
        ring
      have hmono : charge L η T (k + 1) / (tail η T (k + 1) + charge L η T (k + 1)) ≤
          charge L η T (k + 1) / tail η T (k + 1) :=
        div_le_div_of_nonneg_left hc ht (by linarith)
      have hcle : charge L η T (k + 1) ≤ tail η T (k + 1) := by
        have h1 := charge_le hL hη hLη hk
        have h2 := tail_succ η T (k + 1) (lt_of_le_of_lt (Nat.zero_le _) hk)
        have h3 := tail_nonneg (η := η) (T := T) (k := k + 1 + 1) hη.le (Nat.succ_le_of_lt hk)
        have h4 := step_pos hη hk
        linarith
      have hq : 0 ≤ 1 - charge L η T (k + 1) / tail η T (k + 1) := by
        rw [sub_nonneg, div_le_one ht]
        exact hcle
      have hwt : 0 ≤ weight L η T k * tail η T k := (mul_pos hv ht0).le
      have hS0 : 0 ≤ tail η T 0 := tail_nonneg hη.le (Nat.zero_le _)
      have hs0 : 0 ≤ ∑ j ∈ range k, charge L η T (j + 1) / tail η T (j + 1) :=
        sum_nonneg (fun j hj => div_nonneg (charge_nonneg hL hη.le T (j + 1)
          (by have := mem_range.mp hj; omega)) (tail_nonneg hη.le (by have := mem_range.mp hj; omega)))
      have hr0 : 0 ≤ charge L η T (k + 1) / tail η T (k + 1) := div_nonneg hc ht.le
      have hstep := mul_le_mul_of_nonneg_right hlow hq
      rw [hrat, hsplit]
      set s := ∑ j ∈ range k, charge L η T (j + 1) / tail η T (j + 1)
      set r := charge L η T (k + 1) / tail η T (k + 1)
      set r' := charge L η T (k + 1) / (tail η T (k + 1) + charge L η T (k + 1))
      have h5 : weight L η T k * tail η T k * (1 - r) ≤ weight L η T k * tail η T k * (1 - r') :=
        mul_le_mul_of_nonneg_left (by linarith) hwt
      nlinarith [mul_nonneg hS0 (mul_nonneg hs0 hr0)]

lemma weight_mono {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T k : ℕ}
    (hk : k + 1 < T) : weight L η T k ≤ weight L η T (k + 1) := by
  obtain ⟨hv, -, -⟩ := weight_bounds hL hη hLη k (Nat.lt_of_succ_lt hk)
  have hid := weight_identity hL hη hk
  have ht := tail_pos hη hk
  have hc := charge_nonneg hL hη.le T (k + 1) hk.le
  have h1 := charge_le hL hη hLη hk
  have h2 := tail_succ η T k (lt_of_le_of_lt (Nat.zero_le _) hk)
  have h3 := step_pos hη (Nat.lt_of_succ_lt hk)
  have h4 : step η T (k + 1) ≤ step η T k := by
    have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hk)
    unfold step
    apply div_le_div_of_nonneg_right _ hT.le
    push_cast
    nlinarith
  have hle : tail η T (k + 1) + charge L η T (k + 1) ≤ tail η T k := by linarith
  have hv' : 0 < weight L η T (k + 1) := by
    simp only [weight]
    exact div_pos (mul_pos hv (tail_pos hη (Nat.lt_of_succ_lt hk))) (by positivity)
  nlinarith

lemma potential_recursion {L η σ : ℝ} (hL : 0 ≤ L) (hη : 0 < η) {T : ℕ} (A Φ d e : ℕ → ℝ)
    (hH : ∀ k, k < T → step η T k * weight L η T k * (A (k + 1) - Φ k) ≤
      weight L η T k / 2 * (d k - e k) + weight L η T k * charge L η T k * A k +
        step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2)
    (hJ : ∀ k, k + 1 < T → weight L η T (k + 1) * Φ (k + 1) ≤
      weight L η T k * Φ k + (weight L η T (k + 1) - weight L η T k) * A (k + 1))
    (hD : ∀ k, k + 1 < T → weight L η T (k + 1) * d (k + 1) ≤ weight L η T k * e k) :
    ∀ m, m < T →
      weight L η T m * tail η T m * Φ m + weight L η T m * charge L η T m * A m +
        weight L η T m / 2 * d m ≤
      weight L η T 0 * tail η T 0 * Φ 0 + weight L η T 0 * charge L η T 0 * A 0 +
        weight L η T 0 / 2 * d 0 +
        ∑ k ∈ range m, step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hprev := ih (Nat.lt_of_succ_lt hm)
    have hid := weight_identity hL hη hm
    have hts := tail_succ η T m (lt_of_le_of_lt (Nat.zero_le _) hm)
    have hH' := hH m (Nat.lt_of_succ_lt hm)
    have hJ' := hJ m hm
    have hD' := hD m hm
    have htn : 0 ≤ tail η T (m + 1) := (tail_pos hη hm).le
    have hJs := mul_le_mul_of_nonneg_left hJ' htn
    rw [sum_range_succ]
    linear_combination hJs + (1 / 2 : ℝ) * hD' + hH' + hprev + A (m + 1) * hid +
      (weight L η T m * A (m + 1) - weight L η T m * Φ m) * hts

set_option maxHeartbeats 1000000 in
lemma potential_bound {L η σ D : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ}
    (hT : 0 < T) (A Φ d e : ℕ → ℝ)
    (hH : ∀ k, k < T → step η T k * weight L η T k * (A (k + 1) - Φ k) ≤
      weight L η T k / 2 * (d k - e k) + weight L η T k * charge L η T k * A k +
        step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2)
    (hJ : ∀ k, k + 1 < T → weight L η T (k + 1) * Φ (k + 1) ≤
      weight L η T k * Φ k + (weight L η T (k + 1) - weight L η T k) * A (k + 1))
    (hD : ∀ k, k + 1 < T → weight L η T (k + 1) * d (k + 1) ≤ weight L η T k * e k)
    (he : ∀ k, k < T → 0 ≤ e k) (hΦ0 : Φ 0 = 0) (hd0 : d 0 ≤ D ^ 2)
    (hA0 : A 0 ≤ L * D ^ 2 / 2) :
    A T ≤ 3 * D ^ 2 / (η * T) + 6 * η * σ ^ 2 := by
  have hT1 : T - 1 < T := Nat.sub_lt hT one_pos
  have hrec := potential_recursion hL hη A Φ d e hH hJ hD (T - 1) hT1
  have hlast := hH (T - 1) hT1
  have hsucc : T - 1 + 1 = T := Nat.sub_add_cancel hT
  rw [hsucc] at hlast
  have htl := tail_last (η := η) hT
  have he' := he (T - 1) hT1
  obtain ⟨hvpos, -, hvlow⟩ := weight_bounds hL hη hLη (T - 1) hT1
  have hS0 : tail η T 0 = η * ((T : ℝ) + 1) / 2 := tail_zero hT
  have hS0pos : 0 < tail η T 0 := tail_pos hη hT
  have hw0 : weight L η T 0 = 1 := rfl
  have hall : ∑ k ∈ range T, step η T k ^ 2 / tail η T k ≤ 2 * η := ratio_sum hη T le_rfl
  have hfull : ∑ k ∈ range (T - 1), step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2 +
      step η T (T - 1) ^ 2 * weight L η T (T - 1) * (1 + L * step η T (T - 1)) * σ ^ 2 ≤
      tail η T 0 * (9 / 4 * η) * σ ^ 2 := by
    have hb : ∀ k ∈ range T, step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2 ≤
        tail η T 0 * (9 / 8) * σ ^ 2 * (step η T k ^ 2 / tail η T k) := by
      intro k hk
      have hkT : k < T := mem_range.mp hk
      obtain ⟨hv, hvup, -⟩ := weight_bounds hL hη hLη k hkT
      have ht := tail_pos hη hkT
      have hs := step_le hη.le hkT
      have hsp := step_pos hη hkT
      have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hs hL) hLη
      have hvle : weight L η T k ≤ tail η T 0 / tail η T k := by
        rw [le_div_iff₀ ht]; exact hvup
      have h1 : weight L η T k * (1 + L * step η T k) ≤ tail η T 0 / tail η T k * (9 / 8) :=
        mul_le_mul hvle (by linarith) (by nlinarith [mul_nonneg hL hsp.le]) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg (step η T k)) (sq_nonneg σ))
      have h4 : tail η T 0 * (9 / 8) * σ ^ 2 * (step η T k ^ 2 / tail η T k) =
          step η T k ^ 2 * σ ^ 2 * (tail η T 0 / tail η T k * (9 / 8)) := by
        field_simp
      rw [h4]
      nlinarith [h2]
    have hs1 := sum_le_sum hb
    rw [← mul_sum] at hs1
    have hrs := sum_range_succ (fun k => step η T k ^ 2 * weight L η T k * (1 + L * step η T k) *
      σ ^ 2) (T - 1)
    rw [hsucc] at hrs
    rw [← hrs]
    calc _ ≤ _ := hs1
      _ ≤ tail η T 0 * (9 / 8) * σ ^ 2 * (2 * η) :=
          mul_le_mul_of_nonneg_left hall (by positivity)
      _ = _ := by ring
  have hchargesum : ∑ j ∈ range (T - 1), charge L η T (j + 1) / tail η T (j + 1) ≤ 9 / 16 := by
    have h := charge_sum hL hη hLη T le_rfl
    have hsh := sum_range_succ' (fun k => charge L η T k / tail η T k) (T - 1)
    rw [hsucc] at hsh
    have h0 : 0 ≤ charge L η T 0 / tail η T 0 :=
      div_nonneg (charge_nonneg hL hη.le T 0 (Nat.zero_le _)) hS0pos.le
    linarith
  have hlowv : tail η T 0 * (7 / 16) ≤ weight L η T (T - 1) * tail η T (T - 1) := by
    have := mul_le_mul_of_nonneg_left (show (7 / 16 : ℝ) ≤ 1 - ∑ j ∈ range (T - 1),
      charge L η T (j + 1) / tail η T (j + 1) by linarith) hS0pos.le
    linarith
  have hc0 : charge L η T 0 * L ≤ 9 / 256 := by
    have hs0 : step η T 0 = η := by
      have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      simp only [step, Nat.cast_zero, sub_zero]; field_simp
    unfold charge
    rw [hs0]
    have hLη0 : 0 ≤ L * η := mul_nonneg hL hη.le
    nlinarith [mul_nonneg hLη0 hLη0]
  have hc0n : 0 ≤ charge L η T 0 := charge_nonneg hL hη.le T 0 (Nat.zero_le _)
  have hA0c : charge L η T 0 * A 0 ≤ (9 / 256) * D ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hA0 hc0n
    nlinarith [sq_nonneg D]
  rw [htl] at hlowv
  have hkey : step η T (T - 1) * weight L η T (T - 1) * A T ≤
      (265 / 256) * D ^ 2 / 2 + tail η T 0 * (9 / 4 * η) * σ ^ 2 := by
    rw [htl] at hrec
    rw [hΦ0, hw0] at hrec
    have hwe : 0 ≤ weight L η T (T - 1) / 2 * e (T - 1) := mul_nonneg (by positivity) he'
    linear_combination hlast + hrec + hfull + hA0c + (1 / 2 : ℝ) * hd0 + hwe
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hS0ge : η * T / 2 ≤ tail η T 0 := by
    rw [hS0]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hη.le) (by norm_num)
  have hpos : 0 < step η T (T - 1) * weight L η T (T - 1) := by
    rw [← htl]; exact mul_pos (tail_pos hη hT1) hvpos
  have hX : 0 ≤ (265 / 256) * D ^ 2 / 2 + tail η T 0 * (9 / 4 * η) * σ ^ 2 := by positivity
  have hAT : A T ≤ ((265 / 256) * D ^ 2 / 2 + tail η T 0 * (9 / 4 * η) * σ ^ 2) /
      (tail η T 0 * (7 / 16)) := by
    rw [le_div_iff₀ (by positivity)]
    rcases le_or_gt (A T) 0 with h | h
    · have : A T * (tail η T 0 * (7 / 16)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      linarith
    · have h1 := mul_le_mul_of_nonneg_left hlowv h.le
      have h2 : A T * (weight L η T (T - 1) * step η T (T - 1)) =
          step η T (T - 1) * weight L η T (T - 1) * A T := by ring
      linarith
  calc A T ≤ _ := hAT
    _ = (16 / 7) * ((265 / 256) * D ^ 2 / (2 * tail η T 0)) + (36 / 7) * η * σ ^ 2 := by
        field_simp
        ring
    _ ≤ (16 / 7) * ((265 / 256) * D ^ 2 / (η * T)) + (36 / 7) * η * σ ^ 2 := by
        have hden : η * T ≤ 2 * tail η T 0 := by linarith
        have hq : (265 / 256) * D ^ 2 / (2 * tail η T 0) ≤ (265 / 256) * D ^ 2 / (η * T) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        linarith
    _ ≤ 3 * D ^ 2 / (η * T) + 6 * η * σ ^ 2 := by
        have h1 : (16 / 7) * ((265 / 256) * D ^ 2 / (η * T)) ≤ 3 * D ^ 2 / (η * T) := by
          rw [← mul_div_assoc, ← mul_assoc]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [sq_nonneg D]
        have h2 : (36 / 7) * η * σ ^ 2 ≤ 6 * η * σ ^ 2 := by nlinarith [sq_nonneg σ]
        linarith

lemma tuning_bound {L R σ ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hε : 0 < ε) {T : ℕ}
    (hT : 48 * L * R ^ 2 / ε + 324 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ T) :
    0 < R / (8 * L * R + σ * Real.sqrt T) ∧ L * (R / (8 * L * R + σ * Real.sqrt T)) ≤ 1 / 8 ∧
      3 * R ^ 2 / (R / (8 * L * R + σ * Real.sqrt T) * T) +
        6 * (R / (8 * L * R + σ * Real.sqrt T)) * σ ^ 2 ≤ ε := by
  have hA : 0 < 48 * L * R ^ 2 / ε := by positivity
  have hB : 0 ≤ 324 * σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  set q := Real.sqrt (T : ℝ)
  have hD : 0 < 8 * L * R + σ * q := by positivity
  set η := R / (8 * L * R + σ * q)
  have hη : 0 < η := div_pos hR hD
  refine ⟨hη, ?_, ?_⟩
  · rw [show L * η = L * R / (8 * L * R + σ * q) by simp only [η]; ring, div_le_iff₀ hD]
    nlinarith [mul_nonneg hσ hsq.le]
  · have h1 : 3 * R ^ 2 / (η * T) = 24 * L * R ^ 2 / T + 3 * σ * R / q := by
      simp only [η]
      rw [← hss]
      field_simp
      ring
    have h2 : 6 * η * σ ^ 2 ≤ 6 * σ * R / q := by
      have hk : R / (8 * L * R + σ * q) * σ ≤ R / q := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD hsq]
        nlinarith [mul_pos (mul_pos hL hR) hR]
      calc 6 * η * σ ^ 2 = 6 * σ * (R / (8 * L * R + σ * q) * σ) := by simp only [η]; ring
        _ ≤ 6 * σ * (R / q) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 6 * σ * R / q := by ring
    have h3 : 24 * L * R ^ 2 / T ≤ ε / 2 := by
      rw [div_le_iff₀ hTpos]
      have : 48 * L * R ^ 2 ≤ ε * T := by
        have := mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_right hB) hT) hε.le
        rwa [mul_div_cancel₀ _ hε.ne'] at this
      linarith
    have h4 : 9 * σ * R / q ≤ ε / 2 := by
      rw [div_le_iff₀ hsq]
      have hT2 : 324 * σ ^ 2 * R ^ 2 ≤ ε ^ 2 * T := by
        have := mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_left hA.le) hT) (sq_nonneg ε)
        rwa [mul_div_cancel₀ _ (pow_ne_zero 2 hε.ne')] at this
      rw [← hss] at hT2
      have h5 : 18 * σ * R ≤ ε * q := by
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp
          (by nlinarith [hT2])
      linarith
    have h6 : 3 * σ * R / q + 6 * σ * R / q = 9 * σ * R / q := by ring
    linarith

end OracleTemplate.SampledConvex
