import LongTails.Proofs.BirchCausalCoefficients

namespace LongTails.Proofs.BirchCausalTransport

open Finset
open LongTails.Proofs.BirchDelayedCoefficients
open LongTails.Proofs.BirchCausalCoefficients

def displacement (history : ℕ → Finset ℕ) (start q t : ℕ) : ℝ :=
  if t < start then (if t ∈ history q then 0 else 1)
  else (if t ∈ history q then 1 else 0)

lemma displacement_bounds (history : ℕ → Finset ℕ) (start q t : ℕ) :
    0 ≤ displacement history start q t ∧ displacement history start q t ≤ 1 := by
  unfold displacement
  split_ifs <;> norm_num

lemma displacement_eq_abs (history : ℕ → Finset ℕ) (start q t : ℕ) :
    displacement history start q t =
      |(if t ∈ history q then (1 : ℝ) else 0) - (if t < start then 1 else 0)| := by
  unfold displacement
  split_ifs <;> norm_num

noncomputable def transportMass (history : ℕ → Finset ℕ) (start n t : ℕ)
    (initial : ℝ) (source : ℕ → ℝ) : ℝ :=
  initial * (if t < start then 1 else 0) +
    ∑ q ∈ range (n + 1), source q * displacement history start q t

lemma transportMass_bounds (history : ℕ → Finset ℕ) (start n t : ℕ)
    (initial : ℝ) (source : ℕ → ℝ) (hi : 0 ≤ initial)
    (hs : ∀ q, 0 ≤ source q) (hmass : initial + ∑ q ∈ range (n + 1), source q = 1) :
    0 ≤ transportMass history start n t initial source ∧
      transportMass history start n t initial source ≤ 1 := by
  have hb : 0 ≤ (if t < start then (1 : ℝ) else 0) ∧
      (if t < start then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  constructor
  · exact add_nonneg (mul_nonneg hi hb.1)
      (sum_nonneg (fun q _ => mul_nonneg (hs q) (displacement_bounds history start q t).1))
  · calc
      _ ≤ initial + ∑ q ∈ range (n + 1), source q := by
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_left hb.2 hi
        · apply sum_le_sum
          intro q _
          simpa using mul_le_mul_of_nonneg_left (displacement_bounds history start q t).2 (hs q)
      _ = 1 := hmass

lemma transportMass_zero (history : ℕ → Finset ℕ) (start n t : ℕ)
    (initial : ℝ) (source : ℕ → ℝ) (hpast : ∀ q, history q ⊆ range q)
    (hstart : start ≤ n) (ht : n ≤ t) :
    transportMass history start n t initial source = 0 := by
  have hts : ¬t < start := by omega
  have hz : ∀ q ∈ range (n + 1), displacement history start q t = 0 := by
    intro q hq
    have htq : t ∉ history q := by
      intro hh
      have := mem_range.mp (hpast q hh)
      have := mem_range.mp hq
      omega
    simp [displacement, hts, htq]
  simp only [transportMass, hts, ite_false, mul_zero, zero_add]
  exact sum_eq_zero (fun q hq => by rw [hz q hq, mul_zero])

lemma transportMass_old (history : ℕ → Finset ℕ) (r start n t : ℕ)
    (initial : ℝ) (source : ℕ → ℝ)
    (hrecent : ∀ q, range (q - r) ⊆ history q) (ht : t < start)
    (hs : ∀ q, 0 ≤ source q) :
    transportMass history start n t initial source ≤
      initial + ∑ q ∈ range (t + r + 1), source q := by
  have hsub : (range (n + 1)).filter (fun q => t ∉ history q) ⊆ range (t + r + 1) := by
    intro q hq
    obtain ⟨_, hq⟩ := mem_filter.mp hq
    apply mem_range.mpr
    by_contra h
    exact hq (hrecent q (mem_range.mpr (by omega)))
  have he : transportMass history start n t initial source =
      initial + ∑ q ∈ (range (n + 1)).filter (fun q => t ∉ history q), source q := by
    simp only [transportMass, displacement, ht, ite_true, mul_one, mul_ite, mul_zero,
      sum_filter]
    congr 1
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp_all
  rw [he]
  exact add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hs q))

lemma transportMass_envelope (history : ℕ → Finset ℕ) (r H n t : ℕ)
    (initial : ℝ) (source : ℕ → ℝ) (β : ℝ) (hH : 0 < H)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpast : ∀ q, history q ⊆ range q)
    (hrecent : ∀ q, range (q - r) ⊆ history q)
    (hi : 0 ≤ initial) (hs : ∀ q, 0 ≤ source q)
    (hmass : initial + ∑ q ∈ range (n + 1), source q = 1)
    (htail : ∀ c, initial + ∑ q ∈ range c, source q ≤ β ^ (n - c - r)) :
    transportMass history (n / H * H) n t initial source ≤
      if t ≤ n then β ^ (n - t - max (H - 1) (2 * r + 1)) else 0 := by
  have hstart : n / H * H ≤ n := Nat.div_mul_le_self n H
  by_cases ht : n ≤ t
  · rw [transportMass_zero history _ n t initial source hpast hstart ht]
    split_ifs <;> positivity
  · have htn : t ≤ n := by omega
    rw [ite_eq_left htn]
    by_cases hts : t < n / H * H
    · have hm := (transportMass_old history r _ n t initial source hrecent hts hs).trans
        (htail (t + r + 1))
      apply hm.trans
      apply pow_le_pow_of_le_one hβ hβ1
      have := le_max_right (H - 1) (2 * r + 1)
      omega
    · have hrem : n < n / H * H + H := by
        have := Nat.mod_lt n hH
        have hd := Nat.mod_add_div n H
        rw [Nat.mul_comm H (n / H)] at hd
        omega
      have he : n - t - max (H - 1) (2 * r + 1) = 0 := by
        have := le_max_left (H - 1) (2 * r + 1)
        omega
      rw [he, pow_zero]
      exact (transportMass_bounds history _ n t initial source hi hs hmass).2

lemma envelope_row_column (C : ℕ → ℕ → ℝ) (N s : ℕ) (H β : ℝ)
    (hH : 0 < H) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hbound : ∀ i ∈ range N, ∀ j ∈ range N,
      C i j ≤ (if j ≤ i then β ^ (i - j - s) else 0) / H) :
    (∀ i ∈ range N, (∑ j ∈ range N, C i j) ≤ ((s : ℝ) + 1 / (1 - β)) / H) ∧
    (∀ j ∈ range N, (∑ i ∈ range N, C i j) ≤ ((s : ℝ) + 1 / (1 - β)) / H) := by
  constructor
  · intro i hi
    calc
      _ ≤ ∑ j ∈ range N, (if j ≤ i then β ^ (i - j - s) else 0) / H :=
        sum_le_sum (fun j hj => hbound i hi j hj)
      _ = (∑ j ∈ range N, if j ≤ i then β ^ (i - j - s) else 0) / H :=
        (sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right
        (truncated_geometric_row β s N i hβ hβ1 (mem_range.mp hi)) hH.le
  · intro j hj
    calc
      _ ≤ ∑ i ∈ range N, (if j ≤ i then β ^ (i - j - s) else 0) / H :=
        sum_le_sum (fun i hi => hbound i hi j hj)
      _ = (∑ i ∈ range N, if j ≤ i then β ^ (i - j - s) else 0) / H :=
        (sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right
        (truncated_geometric_column β s N j hβ hβ1 (mem_range.mp hj)) hH.le

lemma envelope_certificate (C : ℕ → ℕ → ℝ) (N s : ℕ) (H β D : ℝ)
    (hH : 0 < H) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : ∀ i ∈ range N, ∀ j ∈ range N, 0 ≤ C i j)
    (hbound : ∀ i ∈ range N, ∀ j ∈ range N,
      C i j ≤ (if j ≤ i then β ^ (i - j - s) else 0) / H)
    (hD : ((s : ℝ) + 1 / (1 - β)) / H ≤ D) :
    ∀ j ∈ range N,
      (∑ i ∈ range N, (1 / H) * (∑ t ∈ range N, C i t) * C i j) ≤ D ^ 2 / H := by
  have hb := envelope_row_column C N s H β hH hβ hβ1 hbound
  have ha : 0 ≤ ((s : ℝ) + 1 / (1 - β)) / H := by positivity
  have hh := weighted_schur (range N) C (1 / H)
    (((s : ℝ) + 1 / (1 - β)) / H) D (by positivity) ha hD hC hb.1 hb.2
  simpa [div_eq_mul_inv] using hh

lemma row_column_certificate {ι : Type*} (s : Finset ι) (C : ι → ι → ℝ)
    (w : ι → ℝ) (R S D : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hR : 0 ≤ R)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, C i j ≤ R)
    (hcol : ∀ j ∈ s, ∑ i ∈ s, w i * C i j ≤ S * w j)
    (hD : R * S ≤ D ^ 2) :
    ∀ j ∈ s, (∑ i ∈ s, w i * (∑ t ∈ s, C i t) * C i j) ≤ D ^ 2 * w j := by
  intro j hj
  calc
    _ ≤ ∑ i ∈ s, R * (w i * C i j) := by
      apply sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_right (hrow i hi) (mul_nonneg (hw i hi) (hC i hi j hj))
      nlinarith
    _ = R * ∑ i ∈ s, w i * C i j := by rw [mul_sum]
    _ ≤ R * (S * w j) := mul_le_mul_of_nonneg_left (hcol j hj) hR
    _ ≤ D ^ 2 * w j := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hD (hw j hj)

lemma composition_row {ι : Type*} (s : Finset ι) (A B : ι → ι → ℝ)
    (RA RB : ℝ) (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j) (hRB : 0 ≤ RB)
    (hrowA : ∀ i ∈ s, ∑ j ∈ s, A i j ≤ RA)
    (hrowB : ∀ i ∈ s, ∑ j ∈ s, B i j ≤ RB) :
    ∀ i ∈ s, (∑ j ∈ s, ∑ k ∈ s, A i k * B k j) ≤ RA * RB := by
  intro i hi
  rw [sum_comm]
  calc
    _ = ∑ k ∈ s, A i k * ∑ j ∈ s, B k j := by simp_rw [mul_sum]
    _ ≤ ∑ k ∈ s, A i k * RB := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hrowB k hk) (hA i hi k hk)
    _ = (∑ k ∈ s, A i k) * RB := by rw [sum_mul]
    _ ≤ RA * RB := mul_le_mul_of_nonneg_right (hrowA i hi) hRB

lemma composition_column {ι : Type*} (s : Finset ι) (A B : ι → ι → ℝ)
    (w : ι → ℝ) (SA SB : ℝ) (hSA : 0 ≤ SA)
    (hB : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ B i j)
    (hcolA : ∀ j ∈ s, ∑ i ∈ s, w i * A i j ≤ SA * w j)
    (hcolB : ∀ j ∈ s, ∑ i ∈ s, w i * B i j ≤ SB * w j) :
    ∀ j ∈ s, (∑ i ∈ s, w i * ∑ k ∈ s, A i k * B k j) ≤ SA * SB * w j := by
  intro j hj
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ k ∈ s, (∑ i ∈ s, w i * A i k) * B k j := by
      simp_rw [sum_mul, mul_assoc]
    _ ≤ ∑ k ∈ s, (SA * w k) * B k j := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hcolA k hk) (hB k hk j hj)
    _ = SA * ∑ k ∈ s, w k * B k j := by simp_rw [mul_sum, mul_assoc]
    _ ≤ SA * (SB * w j) := mul_le_mul_of_nonneg_left (hcolB j hj) hSA
    _ = SA * SB * w j := by ring

noncomputable def causalTransport (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B H n t : ℕ) : ℝ :=
  transportMass history (n / H * H) n t (initialWeight history hpast B n)
    (sourceWeight history hpast B n) / H

lemma causalTransport_bounds (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B H r : ℕ)
    (hB : 2 ≤ B) (hH : 0 < H) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) (n t : ℕ) :
    0 ≤ causalTransport history hpast B H n t ∧
      causalTransport history hpast B H n t ≤
        (if t ≤ n then (1 - 1 / (B : ℝ)) ^ (n - t - max (H - 1) (2 * r + 1)) else 0) / H := by
  have hb := weight_bounds history hpast B r hB hr hrecent hclosed
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hβ : 0 ≤ 1 - 1 / (B : ℝ) := by
    have hh : 1 / (B : ℝ) ≤ 1 := (div_le_one hBr).2 (by exact_mod_cast (show 1 ≤ B by omega))
    linarith
  have hβ1 : 1 - 1 / (B : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  constructor
  · exact div_nonneg (transportMass_bounds history _ n t _ _ (hb.1 n).1
      (fun q => (hb.2.1 n q).1) (hb.2.2.1 n (n + 1) (by omega))).1 (by positivity)
  · exact div_le_div_of_nonneg_right (transportMass_envelope history r H n t _ _ _ hH hβ hβ1
      hpast hrecent (hb.1 n).1 (fun q => (hb.2.1 n q).1)
      (hb.2.2.1 n (n + 1) (by omega)) (hb.2.2.2 n)) (by positivity)

lemma causalTransport_certificate (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B H r N : ℕ)
    (hB : 2 ≤ B) (hH : 0 < H) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) :
    ∀ t ∈ range N,
      (∑ n ∈ range N, (1 / (H : ℝ)) *
        (∑ j ∈ range N, causalTransport history hpast B H n j) *
          causalTransport history hpast B H n t) ≤
        (((max (H - 1) (2 * r + 1) : ℕ) : ℝ) + B) ^ 2 / H ^ 3 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hβ : 0 ≤ 1 - 1 / (B : ℝ) := by
    have hh : 1 / (B : ℝ) ≤ 1 := (div_le_one hBr).2 (by exact_mod_cast (show 1 ≤ B by omega))
    linarith
  have hβ1 : 1 - 1 / (B : ℝ) < 1 := by have := one_div_pos.mpr hBr; linarith
  have h := envelope_certificate (causalTransport history hpast B H) N
    (max (H - 1) (2 * r + 1)) H (1 - 1 / (B : ℝ))
    ((((max (H - 1) (2 * r + 1) : ℕ) : ℝ) + B) / H)
    hHr hβ hβ1 (fun i _ j _ => (causalTransport_bounds history hpast B H r hB hH hr hrecent hclosed i j).1)
    (fun i _ j _ => (causalTransport_bounds history hpast B H r hB hH hr hrecent hclosed i j).2)
    (by simp)
  intro t ht
  convert h t ht using 1
  field_simp

end LongTails.Proofs.BirchCausalTransport
