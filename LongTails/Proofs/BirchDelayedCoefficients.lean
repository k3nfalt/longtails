import Mathlib.Tactic

namespace LongTails.Proofs.BirchDelayedCoefficients

lemma segment_lower (u : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a) (s n : ℕ) :
    (∀ j, s ≤ j → j < s + n → a * u j ≤ u (j + 1)) →
      a ^ n * u s ≤ u (s + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      intro h
      have hprev := ih (fun j hj hjn => h j hj (by omega))
      have hlast := h (s + n) (by omega) (by omega)
      have hmul := mul_le_mul_of_nonneg_left hprev ha
      rw [pow_succ]
      have heq : a ^ n * a * u s = a * (a ^ n * u s) := by ring
      rw [heq]
      simpa [Nat.add_assoc] using hmul.trans hlast

lemma delay_power_lower (lam : ℝ) (R : ℕ) (hsmall : lam ≤ 1 / 2)
    (hdelay : 4 * lam * (R : ℝ) ≤ 1) :
    (1 / 2 : ℝ) ≤ (1 - 2 * lam) ^ R := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * lam) by linarith) R
  have heq : 1 + -(2 * lam) = 1 - 2 * lam := by ring
  rw [heq] at h
  nlinarith

lemma delayed_nonnegative (u : ℕ → ℝ) (source : ℕ → Option ℕ)
    (lam : ℝ) (R : ℕ) (hlam : 0 ≤ lam) (hsmall : lam ≤ 1 / 2)
    (hdelay : 4 * lam * (R : ℝ) ≤ 1) (hinit : 0 ≤ u 0)
    (hsource : ∀ n j, source n = some j → j ≤ n ∧ n - j ≤ R)
    (hrec : ∀ n, u (n + 1) = u n - lam * (source n).elim 0 u) :
    ∀ n, 0 ≤ u n ∧ (1 - 2 * lam) * u n ≤ u (n + 1) ∧ u (n + 1) ≤ u n := by
  have ha : 0 ≤ 1 - 2 * lam := by linarith
  have ha1 : 1 - 2 * lam ≤ 1 := by linarith
  have hp := delay_power_lower lam R hsmall hdelay
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn : 0 ≤ u n := by
        cases n with
        | zero => exact hinit
        | succ k =>
            have hk := ih k (by omega)
            exact (mul_nonneg ha hk.1).trans hk.2.1
      refine ⟨hn, ?_⟩
      cases hs : source n with
      | none =>
          rw [hrec n, hs]
          simp only [Option.elim_none, mul_zero, sub_zero]
          constructor
          · nlinarith [mul_nonneg hlam hn]
          · exact le_rfl
      | some j =>
          obtain ⟨hjn, hjR⟩ := hsource n j hs
          have hj : 0 ≤ u j := by
            by_cases heq : j = n
            · simpa [heq] using hn
            · exact (ih j (by omega)).1
          have hseg := segment_lower u (1 - 2 * lam) ha j (n - j)
            (fun t ht htn => (ih t (by omega)).2.1)
          rw [Nat.add_sub_of_le hjn] at hseg
          have hpow : (1 - 2 * lam) ^ R ≤ (1 - 2 * lam) ^ (n - j) :=
            pow_le_pow_of_le_one ha ha1 hjR
          have hhalf := (mul_le_mul_of_nonneg_right (hp.trans hpow) hj).trans hseg
          have hratio : u j ≤ 2 * u n := by linarith
          have hmul := mul_le_mul_of_nonneg_left hratio hlam
          rw [hrec n, hs]
          simp only [Option.elim_some]
          constructor
          · nlinarith
          · nlinarith [mul_nonneg hlam hj]

lemma old_mass_tail (F : ℕ → ℝ) (source : ℕ → ℕ) (j : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hnonneg : ∀ n, 0 ≤ F n)
    (hbefore : ∀ n, n ≤ j → F n = 1) (hsource : ∀ n, source n ≤ n)
    (hrec : ∀ n, j ≤ n → F (n + 1) = F n - lam * F (source n)) :
    ∀ n, F (j + n) ≤ (1 - lam) ^ n := by
  have hmono : Antitone F := antitone_nat_of_succ_le (fun n => by
    by_cases hn : n < j
    · rw [hbefore (n + 1) (by omega), hbefore n (by omega)]
    · rw [hrec n (by omega)]
      exact sub_le_self _ (mul_nonneg hlam (hnonneg _)))
  have hstep (n : ℕ) (hn : j ≤ n) : F (n + 1) ≤ (1 - lam) * F n := by
    rw [hrec n hn]
    have h := mul_le_mul_of_nonneg_left (hmono (hsource n)) hlam
    nlinarith
  intro n
  induction n with
  | zero => simp [hbefore j le_rfl]
  | succ n ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 - lam by linarith)
      have hs := hstep (j + n) (by omega)
      simpa [Nat.add_assoc, pow_succ, mul_comm] using hs.trans hm

lemma coefficient_square_sum_le {ι : Type*} (s : Finset ι) (b : ι → ℝ) (a : ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ b i) (hmax : ∀ i ∈ s, b i ≤ a)
    (hmass : ∑ i ∈ s, b i = 1) : (∑ i ∈ s, b i ^ 2) ≤ a := by
  calc
    (∑ i ∈ s, b i ^ 2) ≤ ∑ i ∈ s, a * b i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_right (hmax i hi) (hnonneg i hi)
      nlinarith
    _ = a := by rw [← Finset.mul_sum, hmass, mul_one]

lemma ema_block_bounds (alpha : ℝ) (H : ℕ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hsmall : (H : ℝ) * alpha ≤ 1 / 2) :
    (H : ℝ) * alpha / 2 ≤ 1 - (1 - alpha) ^ H ∧
      1 - (1 - alpha) ^ H ≤ (H : ℝ) * alpha := by
  have hr : 0 ≤ 1 - alpha := by linarith
  have hr1 : 1 - alpha ≤ 1 := by linarith
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -alpha by linarith) H
  have heq : 1 + -alpha = 1 - alpha := by ring
  rw [heq] at hbern
  have hhalf : (1 / 2 : ℝ) ≤ (1 - alpha) ^ H := by nlinarith
  have hsum : (H : ℝ) / 2 ≤ ∑ j ∈ Finset.range H, (1 - alpha) ^ j := by
    calc
      (H : ℝ) / 2 = ∑ _j ∈ Finset.range H, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.range H, (1 - alpha) ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hhalf.trans (pow_le_pow_of_le_one hr hr1 (Nat.le_of_lt (Finset.mem_range.mp hj)))
  have hg := geom_sum_mul_neg (1 - alpha) H
  have hm := mul_le_mul_of_nonneg_left hsum ha
  constructor <;> nlinarith

lemma delayed_after_birth (u : ℕ → ℝ) (source : ℕ → ℕ) (birth R : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hsmall : lam ≤ 1 / 2) (hdelay : 4 * lam * (R : ℝ) ≤ 1)
    (hsource : ∀ n, source n ≤ n ∧ n - source n ≤ R)
    (hbefore : ∀ n, n < birth → u n = 0) (hbirth : 0 ≤ u birth)
    (hrec : ∀ n, birth ≤ n → u (n + 1) = u n - lam * u (source n)) :
    (∀ n, 0 ≤ u n ∧ u n ≤ u birth) ∧ ∀ n, birth ≤ n → u (n + 1) ≤ u n := by
  let v := fun n => u (birth + n)
  let src := fun n => if birth ≤ source (birth + n) then some (source (birth + n) - birth) else none
  have hs : ∀ n j, src n = some j → j ≤ n ∧ n - j ≤ R := by
    intro n j hj
    dsimp only [src] at hj
    split_ifs at hj with hb
    · have he := Option.some.inj hj
      have hh := hsource (birth + n)
      omega
  have hr : ∀ n, v (n + 1) = v n - lam * (src n).elim 0 v := by
    intro n
    dsimp only [v]
    rw [← Nat.add_assoc, hrec (birth + n) (by omega)]
    dsimp only [src]
    split_ifs with hb
    · simp only [Option.elim_some, Nat.add_sub_of_le hb]
    · rw [hbefore (source (birth + n)) (by omega)]
      rfl
  have hh := delayed_nonnegative v src lam R hlam hsmall hdelay
    (by simpa [v] using hbirth) hs hr
  have hmono : Antitone v := antitone_nat_of_succ_le (fun n => (hh n).2.2)
  constructor
  · intro n
    by_cases hn : n < birth
    · rw [hbefore n hn]
      exact ⟨le_rfl, hbirth⟩
    · have he : birth + (n - birth) = n := by omega
      have hp := (hh (n - birth)).1
      have hu := hmono (Nat.zero_le (n - birth))
      exact ⟨by simpa [v, he] using hp, by simpa [v, he] using hu⟩
  · intro n hn
    have he : birth + (n - birth) = n := by omega
    simpa [v, ← Nat.add_assoc, he] using (hh (n - birth)).2.2

lemma weighted_schur {ι : Type*} (s : Finset ι) (C : ι → ι → ℝ)
    (weight A D : ℝ) (hw : 0 ≤ weight) (hA : 0 ≤ A) (hD : A ≤ D)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, C i j ≤ A)
    (hcolumn : ∀ j ∈ s, ∑ i ∈ s, C i j ≤ A) :
    ∀ j ∈ s, (∑ i ∈ s, weight * (∑ k ∈ s, C i k) * C i j) ≤ D ^ 2 * weight := by
  intro j hj
  calc
    (∑ i ∈ s, weight * (∑ k ∈ s, C i k) * C i j) ≤
        ∑ i ∈ s, weight * A * C i j := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrow i hi) hw) (hC i hi j hj)
    _ = weight * A * ∑ i ∈ s, C i j := by rw [Finset.mul_sum]
    _ ≤ weight * A * A := mul_le_mul_of_nonneg_left (hcolumn j hj) (mul_nonneg hw hA)
    _ ≤ D ^ 2 * weight := by
      have hh : A ^ 2 ≤ D ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh hw]

lemma delayed_forcing_nonnegative (u f : ℕ → ℝ) (source : ℕ → ℕ)
    (lam : ℝ) (R : ℕ) (hlam : 0 ≤ lam) (hsmall : lam ≤ 1 / 2)
    (hdelay : 4 * lam * (R : ℝ) ≤ 1) (hinit : 0 ≤ u 0)
    (hsource : ∀ n, source n ≤ n ∧ n - source n ≤ R)
    (hf : ∀ n, 0 ≤ f n)
    (hrec : ∀ n, u (n + 1) = u n - lam * u (source n) + f n) :
    ∀ n, 0 ≤ u n ∧ (1 - 2 * lam) * u n ≤ u (n + 1) ∧
      u n ≤ u 0 + ∑ j ∈ Finset.range n, f j := by
  have ha : 0 ≤ 1 - 2 * lam := by linarith
  have ha1 : 1 - 2 * lam ≤ 1 := by linarith
  have hp := delay_power_lower lam R hsmall hdelay
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn : 0 ≤ u n := by
        cases n with
        | zero => exact hinit
        | succ k => exact (mul_nonneg ha (ih k (by omega)).1).trans (ih k (by omega)).2.1
      have hjn := (hsource n).1
      have hj : 0 ≤ u (source n) := by
        by_cases he : source n = n
        · simpa [he] using hn
        · exact (ih (source n) (by omega)).1
      have hseg := segment_lower u (1 - 2 * lam) ha (source n) (n - source n)
        (fun j hj hjn => (ih j (by omega)).2.1)
      rw [Nat.add_sub_of_le hjn] at hseg
      have hpow := pow_le_pow_of_le_one ha ha1 (hsource n).2
      have hhalf := (mul_le_mul_of_nonneg_right (hp.trans hpow) hj).trans hseg
      have hratio : u (source n) ≤ 2 * u n := by linarith
      refine ⟨hn, ?_, ?_⟩
      · rw [hrec n]
        nlinarith [mul_le_mul_of_nonneg_left hratio hlam, hf n]
      · cases n with
        | zero => simp
        | succ k =>
            rw [hrec k, Finset.sum_range_succ]
            have hsrc : 0 ≤ u (source k) := by
              by_cases he : source k = k + 1
              · simpa [he] using hn
              · exact (ih (source k) (by have := (hsource k).1; omega)).1
            have hprev := (ih k (by omega)).2.2
            nlinarith [mul_nonneg hlam hsrc]

lemma geometric_sum_le (ρ : ℝ) (n : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ Finset.range n, ρ ^ j) ≤ 1 / (1 - ρ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - ρ)).2
  have he := geom_sum_mul_neg ρ n
  nlinarith [pow_nonneg hρ n]

lemma truncated_geometric_sum_le (ρ : ℝ) (c n : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ Finset.range n, ρ ^ (j - c)) ≤ (c : ℝ) + 1 / (1 - ρ) := by
  have hfirst : (∑ j ∈ Finset.range c, ρ ^ (j - c)) = (c : ℝ) := by
    have he : ∀ j ∈ Finset.range c, ρ ^ (j - c) = 1 := by
      intro j hj
      rw [Nat.sub_eq_zero_of_le (by have := Finset.mem_range.mp hj; omega), pow_zero]
    rw [Finset.sum_congr rfl he]
    simp
  calc
    _ ≤ ∑ j ∈ Finset.range (c + n), ρ ^ (j - c) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun j _ _ => pow_nonneg hρ _)
    _ = (c : ℝ) + ∑ j ∈ Finset.range n, ρ ^ j := by
      rw [Finset.sum_range_add, hfirst]
      simp
    _ ≤ _ := by linarith [geometric_sum_le ρ n hρ hρ1]

lemma truncated_geometric_row (ρ : ℝ) (c K k : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk : k < K) :
    (∑ j ∈ Finset.range K, if j ≤ k then ρ ^ (k - j - c) else 0) ≤ (c : ℝ) + 1 / (1 - ρ) := by
  have he : (∑ j ∈ Finset.range (k + 1), if j ≤ k then ρ ^ (k - j - c) else 0) =
      ∑ j ∈ Finset.range K, if j ≤ k then ρ ^ (k - j - c) else 0 := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hj' : ¬j ≤ k := by simp only [Finset.mem_range] at hj; omega
    simp [hj']
  rw [← he]
  have hf : (∑ j ∈ Finset.range (k + 1), if j ≤ k then ρ ^ (k - j - c) else 0) =
      ∑ j ∈ Finset.range (k + 1), ρ ^ (k - j - c) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (by have := Finset.mem_range.mp hj; omega)]
  rw [hf]
  have hr := Finset.sum_range_reflect (fun j => ρ ^ (j - c)) (k + 1)
  have hr' : (∑ j ∈ Finset.range (k + 1), ρ ^ (k - j - c)) =
      ∑ j ∈ Finset.range (k + 1), ρ ^ (j - c) := by simpa only [Nat.add_sub_cancel] using hr
  rw [hr']
  exact truncated_geometric_sum_le ρ c (k + 1) hρ hρ1

lemma truncated_geometric_column (ρ : ℝ) (c K j : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hj : j < K) :
    (∑ k ∈ Finset.range K, if j ≤ k then ρ ^ (k - j - c) else 0) ≤ (c : ℝ) + 1 / (1 - ρ) := by
  have he : K = j + (K - j) := by omega
  conv_lhs => rw [he]
  rw [Finset.sum_range_add]
  have hzero : (∑ k ∈ Finset.range j, if j ≤ k then ρ ^ (k - j - c) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [show ¬j ≤ k by have := Finset.mem_range.mp hk; omega]
  rw [hzero, zero_add]
  simpa only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left] using
    truncated_geometric_sum_le ρ c (K - j) hρ hρ1

lemma ema_inverse_le (H B : ℕ) (hH : 0 < H) (hB : 2 * H ≤ B) :
    0 < 1 - (1 - 1 / (B : ℝ)) ^ H ∧
      1 / (1 - (1 - 1 / (B : ℝ)) ^ H) ≤ 2 * (B : ℝ) / (H : ℝ) := by
  have hB0 : 0 < B := by omega
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB0
  have hHB : 2 * (H : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hα : (H : ℝ) * (1 / (B : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hBr).2
    linarith
  have h := (ema_block_bounds (1 / (B : ℝ)) H (by positivity)
    ((div_le_one hBr).2 (by exact_mod_cast hB0)) hα).1
  have hl : 0 < 1 - (1 - 1 / (B : ℝ)) ^ H :=
    lt_of_lt_of_le (by positivity) h
  refine ⟨hl, ?_⟩
  apply (div_le_iff₀ hl).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hHr).2
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 2 * (B : ℝ) by positivity)
  have he : (H : ℝ) * (1 / (B : ℝ)) / 2 * (2 * (B : ℝ)) = H := by field_simp
  rw [he] at hm
  nlinarith

end LongTails.Proofs.BirchDelayedCoefficients
