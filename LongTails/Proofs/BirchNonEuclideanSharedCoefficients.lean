import LongTails.Proofs.BirchNonEuclideanShared
import LongTails.Proofs.BirchNonEuclideanTransport

namespace LongTails.Proofs.BirchNonEuclideanSharedCoefficients

open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanShared
open LongTails.Proofs.BirchNonEuclideanDelta (coefficientMass coefficientMass_single
  linearValue_fst_smul linearValue_snd_smul linearValue_fst_sum linearValue_snd_sum
  localRaw_mass weighted_single_sum_le)

lemma buffer_mass_direction (workers m H B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) :
    ∀ k, coefficientMass (bufferValue m H B (canonicalTuning η B) k).1 = 1 ∧
      (bufferValue m H B (canonicalTuning η B) k).2 = 0 := by
  intro k
  induction k with
  | zero =>
      rw [bufferValue_zero]
      constructor
      · simp only [linearValue_fst_smul, linearValue_fst_sum, map_smul, map_sum, coefficientMass_single]
        simp [smul_eq_mul]
        field_simp
      · simp only [linearValue_snd_smul, linearValue_snd_sum, Finset.sum_const_zero, smul_zero]
  | succ k ih =>
      rw [(shared_recurrences workers m H k B η ht hw0 hw).2]
      constructor
      · simp only [linearValue_fst_sum, linearValue_fst_smul, map_sum, map_smul,
          localRaw_mass _ _ _ _ ih.1, smul_eq_mul, mul_one]
        simp [ne_of_gt hm]
      · simp only [linearValue_snd_sum, linearValue_snd_smul, localRaw_direction,
          ih.2, smul_zero, Finset.sum_const_zero]

lemma mainValue_raw (workers m H B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) (k : ℕ) :
    (mainValue m H B (canonicalTuning η B) k).1 = 0 := by
  induction k with
  | zero => rw [mainValue_zero]; rfl
  | succ k ih =>
      rw [(shared_recurrences workers m H k B η ht hw0 hw).1]
      simp only [Prod.fst_add, linearValue_fst_sum, linearValue_fst_smul, ih,
        Finset.sum_const_zero, smul_zero, add_zero]

lemma localRaw_split (α : ℝ) (first : ℕ) (v : LinearValue) (n : ℕ) :
    localRaw α first v n = (1 - α) ^ n • v + localRaw α first 0 n := by
  rw [localRaw_closed, localRaw_closed]
  simp only [smul_zero, zero_add]

noncomputable def roundRaw (m H B k : ℕ) : LinearValue :=
  ∑ i ∈ Finset.range m, (1 / (m : ℝ)) • localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0) 0 H

lemma buffer_recurrence (workers m H k B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) (hm : 0 < m) :
    bufferValue m H B (canonicalTuning η B) (k + 1) =
      (1 - 1 / (B : ℝ)) ^ H • bufferValue m H B (canonicalTuning η B) k + roundRaw m H B k := by
  rw [(shared_recurrences workers m H k B η ht hw0 hw).2]
  have hs (i : ℕ) := localRaw_split (1 / (B : ℝ)) (queryIndex m H B k i 0)
    (bufferValue m H B (canonicalTuning η B) k) H
  simp_rw [hs, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_smul]
  simp [ne_of_gt hm]

lemma queryIndex_injective (m H B k i h j v l : ℕ) (hi : i < m) (hv : v < m)
    (hh : h < H) (hl : l < H) (he : queryIndex m H B k i h = queryIndex m H B j v l) :
    k = j ∧ i = v ∧ h = l := by
  have him := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ m by omega)
  have hvm := Nat.mul_le_mul_right (4 * H + 5) (show v + 1 ≤ m by omega)
  rw [Nat.add_mul] at him hvm
  have hijk : i * (4 * H + 5) + 4 * h < m * (4 * H + 5) + 3 := by omega
  have hvjl : v * (4 * H + 5) + 4 * l < m * (4 * H + 5) + 3 := by omega
  have he' : k * (m * (4 * H + 5) + 3) + (i * (4 * H + 5) + 4 * h) =
      j * (m * (4 * H + 5) + 3) + (v * (4 * H + 5) + 4 * l) := by
    dsimp [queryIndex] at he
    omega
  have hkj : k = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hkj | hjk
    · have hh := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) (show k + 1 ≤ j by omega)
      rw [Nat.add_mul] at hh
      omega
    · have hh := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) (show j + 1 ≤ k by omega)
      rw [Nat.add_mul] at hh
      omega
  subst j
  have hiv : i = v := by
    have he'' : i * (4 * H + 5) + 4 * h = v * (4 * H + 5) + 4 * l := by omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hiv | hvi
    · have hh' := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ v by omega)
      rw [Nat.add_mul] at hh'
      omega
    · have hh' := Nat.mul_le_mul_right (4 * H + 5) (show v + 1 ≤ i by omega)
      rw [Nat.add_mul] at hh'
      omega
  subst v
  exact ⟨rfl, rfl, by omega⟩

lemma roundRaw_coefficient (m H B k q : ℕ) :
    (roundRaw m H B k).1 q = ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
      (1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - h)) *
        Finsupp.single (queryIndex m H B k i h) (1 : ℝ) q := by
  unfold roundRaw
  simp only [localRaw_closed, smul_zero, zero_add, linearValue_fst_sum, linearValue_fst_smul,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  have he : queryIndex m H B k i 0 + 4 * h = queryIndex m H B k i h := by simp [queryIndex]
  rw [he]
  ring

lemma roundRaw_nonneg (m H B k q : ℕ) (hB : 0 < B) : 0 ≤ (roundRaw m H B k).1 q := by
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  rw [roundRaw_coefficient]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
    (Finsupp.single_nonneg.mpr (by norm_num) q)

lemma roundRaw_le (m H B k q : ℕ) (hB : 0 < B) : (roundRaw m H B k).1 q ≤ 1 / ((m : ℝ) * B) := by
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  have hweight : ∀ z ∈ ((Finset.range m) ×ˢ (Finset.range H)),
      1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - z.2) ≤ 1 / ((m : ℝ) * B) := by
    intro z _
    have hp : (1 - 1 / (B : ℝ)) ^ (H - 1 - z.2) ≤ 1 :=
      pow_le_one₀ (by linarith) (by
        have : 0 ≤ 1 / (B : ℝ) := by positivity
        linarith)
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 / ((m : ℝ) * B) by positivity)]
  have hh := weighted_single_sum_le ((Finset.range m) ×ˢ (Finset.range H))
    (fun z => queryIndex m H B k z.1 z.2)
    (fun z => 1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - z.2))
    (1 / ((m : ℝ) * B)) q (by positivity)
    (by
      intro x hx y hy he
      have h := queryIndex_injective m H B k x.1 x.2 k y.1 y.2
        (Finset.mem_range.mp (Finset.mem_product.mp hx).1) (Finset.mem_range.mp (Finset.mem_product.mp hy).1)
        (Finset.mem_range.mp (Finset.mem_product.mp hx).2) (Finset.mem_range.mp (Finset.mem_product.mp hy).2) he
      exact Prod.ext h.2.1 h.2.2) hweight
  simpa only [roundRaw_coefficient, Finset.sum_product] using hh

lemma roundRaw_old_zero (m H B k q : ℕ) (hq : q < queryIndex m H B k 0 0) : (roundRaw m H B k).1 q = 0 := by
  rw [roundRaw_coefficient]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro h _
  have he : queryIndex m H B k i h ≠ q := by dsimp [queryIndex] at hq ⊢; omega
  simp [he]

lemma buffer_initial_coefficient (m H B : ℕ) (t : Tuning) (q : ℕ) :
    (bufferValue m H B t 0).1 q = ∑ j ∈ Finset.range (m * B),
      (1 / ((m : ℝ) * B)) * Finsupp.single (1 + j) (1 : ℝ) q := by
  rw [bufferValue_zero]
  simp only [linearValue_fst_smul, linearValue_fst_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul, Finset.mul_sum, Nat.cast_mul]

lemma buffer_initial_bounds (m H B : ℕ) (t : Tuning) (q : ℕ) :
    0 ≤ (bufferValue m H B t 0).1 q ∧ (bufferValue m H B t 0).1 q ≤ 1 / ((m : ℝ) * B) := by
  rw [buffer_initial_coefficient]
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by positivity) (Finsupp.single_nonneg.mpr (by norm_num) q)
  · exact weighted_single_sum_le (Finset.range (m * B)) (fun j => 1 + j)
      (fun _ => 1 / ((m : ℝ) * B)) (1 / ((m : ℝ) * B)) q (by positivity)
      (by intro x _ y _ he; dsimp only at he; omega) (by intro _ _; rfl)

lemma buffer_future_zero (workers m H B k : ℕ) (t : Tuning)
    (ht : t.Valid) (hw0 : 0 < workers) (hw : m < workers) (q : ℕ)
    (hq : queryIndex m H B k 0 0 ≤ q) : (bufferValue m H B t k).1 q = 0 := by
  have hv := (sharedPrefix_valid workers m H k B t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have hnext : (codeSymbolic t (sharedPrefix m H k B).2).next ≤ q := by
    rw [← hn, sharedPrefix_next]
    dsimp [queryIndex] at hq
    omega
  exact (codeSymbolic_causal _ t (momentumIndex m H B k) q hnext).2.2.1

lemma buffer_coefficient_recurrence (workers m H k B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) (hm : 0 < m) (q : ℕ) :
    (bufferValue m H B (canonicalTuning η B) (k + 1)).1 q =
      (1 - 1 / (B : ℝ)) ^ H * (bufferValue m H B (canonicalTuning η B) k).1 q + (roundRaw m H B k).1 q := by
  rw [buffer_recurrence workers m H k B η ht hw0 hw hm]
  rfl

lemma buffer_coefficient_bounds (workers m H B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (q k : ℕ) :
    0 ≤ (bufferValue m H B (canonicalTuning η B) k).1 q ∧
      (bufferValue m H B (canonicalTuning η B) k).1 q ≤ 1 / ((m : ℝ) * B) := by
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  have hρ0 : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  have hρ1 : (1 - 1 / (B : ℝ)) ^ H ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  induction k with
  | zero => exact buffer_initial_bounds m H B _ q
  | succ k ih =>
      rw [buffer_coefficient_recurrence workers m H k B η ht hw0 hw hm q]
      constructor
      · exact add_nonneg (mul_nonneg hρ0 ih.1) (roundRaw_nonneg m H B k q hB)
      · by_cases hq : q < queryIndex m H B k 0 0
        · rw [roundRaw_old_zero m H B k q hq, add_zero]
          exact (mul_le_mul_of_nonneg_right hρ1 ih.1).trans (by simpa only [one_mul] using ih.2)
        · rw [buffer_future_zero workers m H B k _ ht hw0 hw q (by omega), mul_zero, zero_add]
          exact roundRaw_le m H B k q hB

lemma localRaw_zero_upper (α : ℝ) (first n q : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ (localRaw α first 0 n).1 q ∧ (localRaw α first 0 n).1 q ≤ α :=
  LongTails.Proofs.BirchNonEuclideanDelta.localRaw_coefficient_bounds α first 0 hα hα1
    (by intro q; simpa using hα) (by intro q _; rfl) n q

lemma localRaw_zero_sum_upper (α : ℝ) (first n q : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (localRaw α first 0 n).1 q ≤ α * ∑ j ∈ Finset.range n, Finsupp.single (first + 4 * j) (1 : ℝ) q := by
  rw [localRaw_closed]
  simp only [smul_zero, zero_add, linearValue_fst_sum, linearValue_fst_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp : (1 - α) ^ (n - 1 - j) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hi : 0 ≤ Finsupp.single (first + 4 * j) (1 : ℝ) q := Finsupp.single_nonneg.mpr (by norm_num) q
  calc
    _ ≤ (α * 1) * Finsupp.single (first + 4 * j) (1 : ℝ) q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hα) hi
    _ = _ := by ring

lemma localRaw_square_pointwise (α c : ℝ) (first n q : ℕ) (v : LinearValue)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    (hv : ∀ q, 0 ≤ v.1 q ∧ v.1 q ≤ c) (hf : ∀ q, first ≤ q → v.1 q = 0) :
    (localRaw α first v n).1 q ^ 2 ≤ c * v.1 q +
      α ^ 2 * ∑ j ∈ Finset.range n, Finsupp.single (first + 4 * j) (1 : ℝ) q := by
  by_cases hq : q < first
  · rw [localRaw_old α first v n q hq]
    have hi : (∑ j ∈ Finset.range n, Finsupp.single (first + 4 * j) (1 : ℝ) q) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [show first + 4 * j ≠ q by omega]
    rw [hi, mul_zero, add_zero]
    have hp0 : 0 ≤ (1 - α) ^ n := pow_nonneg (by linarith) _
    have hp1 : (1 - α) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have ha0 : 0 ≤ (1 - α) ^ n * v.1 q := mul_nonneg hp0 (hv q).1
    have ha1 : (1 - α) ^ n * v.1 q ≤ v.1 q := by nlinarith [(hv q).1]
    have ha2 : (1 - α) ^ n * v.1 q ≤ c := ha1.trans (hv q).2
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha2), mul_nonneg hc (sub_nonneg.mpr ha1)]
  · have hz := hf q (by omega)
    have he : (localRaw α first v n).1 q = (localRaw α first 0 n).1 q := by
      rw [localRaw_split]
      simp only [Prod.fst_add, linearValue_fst_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul, hz, mul_zero, zero_add]
    rw [he, hz, mul_zero, zero_add]
    have hb := localRaw_zero_upper α first n q hα hα1
    have hs := localRaw_zero_sum_upper α first n q hα hα1
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), mul_le_mul_of_nonneg_left hs hα]

lemma localRaw_square_sum (α c : ℝ) (first n : ℕ) (v : LinearValue) (s : Finset ℕ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    (hv : ∀ q, 0 ≤ v.1 q ∧ v.1 q ≤ c) (hf : ∀ q, first ≤ q → v.1 q = 0)
    (hmass : (∑ q ∈ s, v.1 q) ≤ 1) :
    (∑ q ∈ s, (localRaw α first v n).1 q ^ 2) ≤ c + (n : ℝ) * α ^ 2 := by
  have hind (j : ℕ) : (∑ q ∈ s, Finsupp.single (first + 4 * j) (1 : ℝ) q) ≤ 1 := by
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs <;> norm_num
  have hs : (∑ q ∈ s, ∑ j ∈ Finset.range n, Finsupp.single (first + 4 * j) (1 : ℝ) q) ≤ n := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hind j)
      _ = _ := by simp
  calc
    _ ≤ ∑ q ∈ s, (c * v.1 q + α ^ 2 * ∑ j ∈ Finset.range n,
        Finsupp.single (first + 4 * j) (1 : ℝ) q) :=
      Finset.sum_le_sum (fun q _ => localRaw_square_pointwise α c first n q v hα hα1 hc hv hf)
    _ = c * (∑ q ∈ s, v.1 q) + α ^ 2 * (∑ q ∈ s, ∑ j ∈ Finset.range n,
        Finsupp.single (first + 4 * j) (1 : ℝ) q) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ c * 1 + α ^ 2 * n := add_le_add (mul_le_mul_of_nonneg_left hmass hc)
      (mul_le_mul_of_nonneg_left hs (sq_nonneg α))
    _ = _ := by ring

lemma querySet_mono (m H B j k : ℕ) (hjk : j ≤ k) : querySet m H B j ⊆ querySet m H B k := by
  apply Finset.union_subset_union_right
  intro q hq
  obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.mp hq
  exact Finset.mem_biUnion.mpr ⟨i, Finset.range_mono hjk hi, hq⟩

lemma querySet_lt (m H B k q : ℕ) (hq : q ∈ querySet m H B k) :
    q < m * B + 2 + k * (m * (4 * H + 5) + 3) := by
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hinit
    have := Finset.mem_range.mp hj
    omega
  · obtain ⟨j, hj, i, hi, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    have hj' := Finset.mem_range.mp hj
    have hi' := Finset.mem_range.mp hi
    have hh' := Finset.mem_range.mp hh
    have hjk := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) (show j + 1 ≤ k by omega)
    have him := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ m by omega)
    rw [Nat.add_mul] at hjk him
    dsimp [queryIndex]
    omega

lemma buffer_sum (workers m H B K k : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hk : k ≤ K) :
    (∑ q ∈ querySet m H B K, (bufferValue m H B (canonicalTuning η B) k).1 q) = 1 := by
  let t := canonicalTuning η B
  have hs := LongTails.Proofs.BirchNonEuclideanTransport.codeSymbolic_vector_supported
    (sharedPrefix m H k B).2 t (momentumIndex m H B k)
  rw [(sharedPrefix_sets workers m H k B t ht hw0 hw).1] at hs
  have hs' : (bufferValue m H B t k).1 ∈ Finsupp.supported ℝ ℝ (querySet m H B K : Set ℕ) :=
    (Finsupp.supported_mono (show (querySet m H B k : Set ℕ) ⊆ querySet m H B K from
      querySet_mono m H B k K hk)) hs
  have hmass := (buffer_mass_direction workers m H B η ht hw0 hw hm hB k).1
  have he := Finsupp.linearCombination_apply_of_mem_supported (R := ℝ) (v := fun _ => (1 : ℝ)) hs'
  simpa only [coefficientMass, smul_eq_mul, mul_one] using he.symm.trans hmass

lemma estimator_square_sum (workers m H K B k i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hk : k ≤ K) (hh : h < H) :
    (∑ q ∈ querySet m H B K, (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
      (bufferValue m H B (canonicalTuning η B) k) (h + 1)).1 q ^ 2) ≤
        1 / ((m : ℝ) * B) + (H : ℝ) / B ^ 2 := by
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  have hf : ∀ q, queryIndex m H B k i 0 ≤ q → (bufferValue m H B (canonicalTuning η B) k).1 q = 0 := by
    intro q hq
    apply buffer_future_zero workers m H B k _ ht hw0 hw q
    dsimp [queryIndex] at hq ⊢
    omega
  have hs := localRaw_square_sum (1 / (B : ℝ)) (1 / ((m : ℝ) * B)) (queryIndex m H B k i 0) (h + 1)
    (bufferValue m H B (canonicalTuning η B) k) (querySet m H B K) hα0 hα1 (by positivity)
    (fun q => buffer_coefficient_bounds workers m H B η ht hw0 hw hm hB q k) hf
    (buffer_sum workers m H B K k η ht hw0 hw hm hB hk).le
  apply hs.trans
  have hhn : ((h + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hh
  calc
    _ ≤ 1 / ((m : ℝ) * B) + (H : ℝ) * (1 / (B : ℝ)) ^ 2 := by gcongr
    _ = _ := by ring

lemma sharedPrefix_estimators (workers m H K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    ∀ e ∈ new.sharps, (new.sharpInputs e).2 = 0 ∧
      (∑ q ∈ new.queries, (new.sharpInputs e).1 q) = 1 ∧
      (∑ q ∈ new.queries, (new.sharpInputs e).1 q ^ 2) ≤ 1 / ((m : ℝ) * B) + (H : ℝ) / B ^ 2 := by
  let t := canonicalTuning η B
  dsimp only
  intro e he
  rw [(sharedPrefix_sets workers m H K B t ht hw0 hw).2.1] at he
  obtain ⟨k, hk, i, hi, h, hh, rfl⟩ := by
    simpa only [sharpSet, roundSharps, Finset.mem_biUnion, Finset.mem_image] using he
  have hki := Finset.mem_range.mp hk
  have hii := Finset.mem_range.mp hi
  have hhi := Finset.mem_range.mp hh
  have hr := (sharedPrefix_records workers m H K B k i h η ht hw0 hw hki hii hhi).2
  have hb := buffer_mass_direction workers m H B η ht hw0 hw hm hB k
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, localRaw_direction, hb.2, smul_zero]
  · rw [← LongTails.Proofs.BirchNonEuclideanDelta.codeSymbolic_sharp_mass, hr]
    exact localRaw_mass _ _ _ _ hb.1
  · rw [hr, (sharedPrefix_sets workers m H K B t ht hw0 hw).1]
    exact estimator_square_sum workers m H K B k i h η ht hw0 hw hm hB hki.le hhi

end LongTails.Proofs.BirchNonEuclideanSharedCoefficients
