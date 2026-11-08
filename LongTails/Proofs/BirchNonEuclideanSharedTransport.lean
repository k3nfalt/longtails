import LongTails.Proofs.BirchNonEuclideanSharedCoefficients

namespace LongTails.Proofs.BirchNonEuclideanSharedTransport

open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanShared
open LongTails.Proofs.BirchNonEuclideanSharedCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_fst_smul linearValue_snd_smul
  linearValue_fst_sum linearValue_snd_sum)

lemma sharpIndex_injective (m H B k i h j v l : ℕ) (hi : i < m) (hv : v < m)
    (hh : h < H) (hl : l < H) (he : sharpIndex m H B k i h = sharpIndex m H B j v l) :
    k = j ∧ i = v ∧ h = l :=
  queryIndex_injective m H B k i h j v l hi hv hh hl (by dsimp [sharpIndex] at he; omega)

lemma sharp_sum_apply (m H B k i n j v l : ℕ) (hi : i < m) (hv : v < m) (hn : n ≤ H) (hl : l < H) :
    (∑ h ∈ Finset.range n, Finsupp.single (sharpIndex m H B k i h) (1 : ℝ) (sharpIndex m H B j v l)) =
      if k = j ∧ i = v ∧ l < n then 1 else 0 := by
  have he (h : ℕ) (hh : h ∈ Finset.range n) :
      Finsupp.single (sharpIndex m H B k i h) (1 : ℝ) (sharpIndex m H B j v l) =
        if k = j ∧ i = v ∧ h = l then 1 else 0 := by
    have heq : sharpIndex m H B k i h = sharpIndex m H B j v l ↔ k = j ∧ i = v ∧ h = l := by
      constructor
      · exact sharpIndex_injective m H B k i h j v l hi hv (by have := Finset.mem_range.mp hh; omega) hl
      · rintro ⟨rfl, rfl, rfl⟩
        rfl
    simp only [Finsupp.single_apply, heq]
  rw [Finset.sum_congr rfl he]
  by_cases hk : k = j <;> by_cases hiv : i = v <;> simp [hk, hiv]

lemma mainValue_closed (workers m H B K : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) :
    mainValue m H B (canonicalTuning η B) K =
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, (1 / (m : ℝ)) • ((1 / (H : ℝ) * η) •
        ∑ h ∈ Finset.range H, ((0, Finsupp.single (sharpIndex m H B k i h) 1) : LinearValue)) := by
  induction K with
  | zero => simp [mainValue_zero]
  | succ K ih => rw [(shared_recurrences workers m H K B η ht hw0 hw).1, ih, Finset.sum_range_succ]

lemma mainValue_direction (workers m H B K j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hv : v < m) (hl : l < H) :
    (mainValue m H B (canonicalTuning η B) K).2 (sharpIndex m H B j v l) =
      (1 / (m : ℝ)) * (1 / (H : ℝ) * η) * if j < K then 1 else 0 := by
  rw [mainValue_closed workers m H B K η ht hw0 hw]
  simp only [linearValue_snd_sum, linearValue_snd_smul, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul]
  have he (k : ℕ) :
      (∑ i ∈ Finset.range m, (1 / (m : ℝ)) * ((1 / (H : ℝ) * η) *
        ∑ h ∈ Finset.range H, Finsupp.single (sharpIndex m H B k i h) (1 : ℝ) (sharpIndex m H B j v l))) =
        (1 / (m : ℝ)) * (1 / (H : ℝ) * η) * if k = j then 1 else 0 := by
    have hh (i : ℕ) (hi : i ∈ Finset.range m) := sharp_sum_apply m H B k i H j v l
      (Finset.mem_range.mp hi) hv le_rfl hl
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun a => (1 / (m : ℝ)) * ((1 / (H : ℝ) * η) * a)) (hh i hi))]
    by_cases hk : k = j <;> simp [hk, hv, hl]
  simp_rw [he]
  simp

lemma localPath_direction (m H B k i n j v l : ℕ) (x : LinearValue) (η : ℝ)
    (hi : i < m) (hv : v < m) (hn : n ≤ H) (hl : l < H) :
    (localPath (1 / (H : ℝ) * η) (queryIndex m H B k i 0) x n).2 (sharpIndex m H B j v l) =
      x.2 (sharpIndex m H B j v l) + (1 / (H : ℝ) * η) *
        if k = j ∧ i = v ∧ l < n then 1 else 0 := by
  rw [localPath_closed]
  simp only [Prod.snd_add, linearValue_snd_smul, linearValue_snd_sum, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  have he : (∑ h ∈ Finset.range n, Finsupp.single (queryIndex m H B k i 0 + 4 * h + 2) (1 : ℝ)
      (sharpIndex m H B j v l)) = if k = j ∧ i = v ∧ l < n then 1 else 0 := by
    convert sharp_sum_apply m H B k i n j v l hi hv hn hl using 1
    apply Finset.sum_congr rfl
    intro h _
    congr 2
  rw [he]

lemma query_direction (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hk : k < K) (hi : i < m) (hh : h < H) (hv : v < m) (hl : l < H) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    (new.queryPoints (queryIndex m H B k i h)).2 (sharpIndex m H B j v l) =
      (1 / (m : ℝ)) * (1 / (H : ℝ) * η) * (if j < k then 1 else 0) +
        (1 / (H : ℝ) * η) * if k = j ∧ i = v ∧ l < h then 1 else 0 := by
  dsimp only
  rw [(sharedPrefix_records workers m H K B k i h η ht hw0 hw hk hi hh).1,
    localPath_direction m H B k i h j v l _ η hi hv hh.le hl,
    mainValue_direction workers m H B k j v l η ht hw0 hw hv hl]

lemma sharedPrefix_initial_records (workers m H K B j : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) (hj : j < m * B) :
    (codeSymbolic t (sharedPrefix m H K B).2).queryPoints (1 + j) = 0 := by
  have hz : (codeSymbolic t (sharedPrefix m H 0 B).2).queryPoints (1 + j) = 0 := by
    rw [sharedPrefix_zero]
    dsimp only
    rw [localBatch_prefix]
    dsimp only
    rw [codeSymbolic_emit]
    have hr := (batchPrefix_records 0 0 (m * B) (m * B) {} t rfl j hj).2
    simpa only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, codeSymbolic,
      codeInstructions, List.map_nil, List.foldl_nil] using hr
  have hv := (sharedPrefix_valid workers m H 0 B t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have hjn : 1 + j < (codeSymbolic t (sharedPrefix m H 0 B).2).next := by
    rw [← hn, sharedPrefix_next]
    omega
  exact (codeExtends_symbolic t _ _ (sharedPrefix_extends m H K B 0 (Nat.zero_le K)) _ hjn).2.2.1.trans hz

lemma sharedPrefix_query_linear (workers m H K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    ∀ q ∈ new.queries, (new.queryPoints q).1 = 0 := by
  dsimp only
  intro q hq
  rw [(sharedPrefix_sets workers m H K B _ ht hw0 hw).1] at hq
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hinit
    rw [sharedPrefix_initial_records workers m H K B j _ ht hw0 hw (Finset.mem_range.mp hj)]
    rfl
  · obtain ⟨k, hk, i, hi, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    rw [(sharedPrefix_records workers m H K B k i h η ht hw0 hw
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hi) (Finset.mem_range.mp hh)).1, localPath_raw]
    exact mainValue_raw workers m H B η ht hw0 hw k

noncomputable def oldMass (m H B : ℕ) (t : Tuning) (j k : ℕ) : ℝ :=
  ∑ q ∈ querySet m H B j, (bufferValue m H B t k).1 q

lemma oldMass_recurrence (workers m H B j k : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hjk : j ≤ k) :
    oldMass m H B (canonicalTuning η B) j (k + 1) =
      (1 - 1 / (B : ℝ)) ^ H * oldMass m H B (canonicalTuning η B) j k := by
  dsimp only [oldMass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [buffer_coefficient_recurrence workers m H k B η ht hw0 hw hm q]
  have hlt := querySet_lt m H B j q hq
  have hmul := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) hjk
  have hf : q < queryIndex m H B k 0 0 := by dsimp [queryIndex]; omega
  rw [roundRaw_old_zero m H B k q hf, add_zero]

lemma oldMass_exact (workers m H B j k : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hjk : j ≤ k) :
    oldMass m H B (canonicalTuning η B) j k = ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j) := by
  induction k, hjk using Nat.le_induction with
  | base =>
      simpa only [oldMass, Nat.sub_self, pow_zero] using buffer_sum workers m H B j j η ht hw0 hw hm hB le_rfl
  | succ k hjk ih =>
      rw [oldMass_recurrence workers m H B j k η ht hw0 hw hm hjk, ih,
        Nat.succ_sub hjk, pow_succ]
      ring

lemma roundRaw_at_query (m H B k j v l : ℕ) (hv : v < m) (hl : l < H) :
    (roundRaw m H B k).1 (queryIndex m H B j v l) =
      if k = j then 1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - l) else 0 := by
  rw [roundRaw_coefficient]
  have he (i h : ℕ) (hi : i < m) (hh : h < H) :
      Finsupp.single (queryIndex m H B k i h) (1 : ℝ) (queryIndex m H B j v l) =
        if k = j ∧ i = v ∧ h = l then 1 else 0 := by
    have heq : queryIndex m H B k i h = queryIndex m H B j v l ↔ k = j ∧ i = v ∧ h = l := by
      constructor
      · exact queryIndex_injective m H B k i h j v l hi hv hh hl
      · rintro ⟨rfl, rfl, rfl⟩
        rfl
    simp only [Finsupp.single_apply, heq]
  calc
    _ = ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
        (1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - h)) *
          (if k = j ∧ i = v ∧ h = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro h hh
      rw [he i h (Finset.mem_range.mp hi) (Finset.mem_range.mp hh)]
    _ = _ := by by_cases hk : k = j <;> simp [hk, ite_and, hv, hl]

lemma buffer_initial_at_query (m H B j v l : ℕ) (t : Tuning) :
    (bufferValue m H B t 0).1 (queryIndex m H B j v l) = 0 := by
  rw [buffer_initial_coefficient]
  apply Finset.sum_eq_zero
  intro u hu
  have he : 1 + u ≠ queryIndex m H B j v l := by
    have := Finset.mem_range.mp hu
    dsimp [queryIndex]
    omega
  simp [he]

lemma buffer_at_query (workers m H B k j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hv : v < m) (hl : l < H) :
    (bufferValue m H B (canonicalTuning η B) k).1 (queryIndex m H B j v l) =
      if j < k then 1 / ((m : ℝ) * B) * (1 - 1 / (B : ℝ)) ^ (H - 1 - l) *
        ((1 - 1 / (B : ℝ)) ^ H) ^ (k - 1 - j) else 0 := by
  induction k with
  | zero => simp [buffer_initial_at_query]
  | succ k ih =>
      rw [buffer_coefficient_recurrence workers m H k B η ht hw0 hw hm,
        ih, roundRaw_at_query m H B k j v l hv hl]
      by_cases he : k = j
      · subst j
        simp
      · by_cases hjk : j < k
        · have hjs : j < k + 1 := by omega
          have hexp : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
          rw [ite_eq_left hjk, ite_eq_right he, ite_eq_left hjs, hexp, pow_succ]
          ring
        · have hjs : ¬j < k + 1 := by omega
          simp [hjk, he, hjs]

def workerQueries (m H B j v : ℕ) : Finset ℕ := (Finset.range H).image (queryIndex m H B j v)

lemma workerQueries_sum {α : Type*} [AddCommMonoid α] (m H B j v : ℕ) (f : ℕ → α) :
    (∑ q ∈ workerQueries m H B j v, f q) = ∑ h ∈ Finset.range H, f (queryIndex m H B j v h) := by
  rw [workerQueries, Finset.sum_image]
  intro h _ l _ he
  dsimp [queryIndex] at he
  omega

lemma workerQueries_before (m H B j v k i q : ℕ) (hjk : j < k) (hv : v < m)
    (hq : q ∈ workerQueries m H B j v) : q < queryIndex m H B k i 0 := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
  have hl' := Finset.mem_range.mp hl
  have hjk' := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) (show j + 1 ≤ k by omega)
  have hvm := Nat.mul_le_mul_right (4 * H + 5) (show v + 1 ≤ m by omega)
  rw [Nat.add_mul] at hjk' hvm
  dsimp [queryIndex]
  omega

lemma reverse_ema_sum (α : ℝ) (H : ℕ) :
    (∑ l ∈ Finset.range H, α * (1 - α) ^ (H - 1 - l)) = 1 - (1 - α) ^ H := by
  rw [← Finset.mul_sum, Finset.sum_range_reflect]
  have hh := geom_sum_mul_neg (1 - α) H
  nlinarith

lemma buffer_worker_mass (workers m H B j v k : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hv : v < m) (hjk : j < k) :
    (∑ q ∈ workerQueries m H B j v, (bufferValue m H B (canonicalTuning η B) k).1 q) =
      (1 / (m : ℝ)) * (1 - (1 - 1 / (B : ℝ)) ^ H) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - 1 - j) := by
  rw [workerQueries_sum]
  calc
    _ = ∑ l ∈ Finset.range H, (1 / (m : ℝ)) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - 1 - j) *
        (1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (H - 1 - l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [buffer_at_query workers m H B k j v l η ht hw0 hw hm hv (Finset.mem_range.mp hl), ite_eq_left hjk]
      ring
    _ = _ := by rw [← Finset.mul_sum, reverse_ema_sum]; ring

lemma local_old_mass (workers m H B k i n j : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hjk : j ≤ k) :
    (∑ q ∈ querySet m H B j, (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
      (bufferValue m H B (canonicalTuning η B) k) n).1 q) =
        (1 - 1 / (B : ℝ)) ^ n * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j) := by
  have hq : ∀ q ∈ querySet m H B j, q < queryIndex m H B k i 0 := by
    intro q hq
    have hlt := querySet_lt m H B j q hq
    have hmul := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) hjk
    dsimp [queryIndex]
    omega
  rw [LongTails.Proofs.BirchNonEuclideanTransport.localRaw_sum_old _ _ _ _ _ hq]
  rw [show (∑ q ∈ querySet m H B j, (bufferValue m H B (canonicalTuning η B) k).1 q) =
    ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j) from oldMass_exact workers m H B j k η ht hw0 hw hm hB hjk]

lemma local_worker_mass (workers m H B k i n j v : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hv : v < m) (hjk : j < k) :
    (∑ q ∈ workerQueries m H B j v, (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
      (bufferValue m H B (canonicalTuning η B) k) n).1 q) =
        (1 - 1 / (B : ℝ)) ^ n * (1 / (m : ℝ)) * (1 - (1 - 1 / (B : ℝ)) ^ H) *
          ((1 - 1 / (B : ℝ)) ^ H) ^ (k - 1 - j) := by
  rw [LongTails.Proofs.BirchNonEuclideanTransport.localRaw_sum_old _ _ _ _ _
    (fun q hq => workerQueries_before m H B j v k i q hjk hv hq),
    buffer_worker_mass workers m H B j v k η ht hw0 hw hm hv hjk]
  ring

lemma localRaw_at_query (m H B k i n j v l : ℕ) (x : LinearValue)
    (hi : i < m) (hv : v < m) (hn : n ≤ H) (hl : l < H) :
    (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0) x n).1 (queryIndex m H B j v l) =
      (1 - 1 / (B : ℝ)) ^ n * x.1 (queryIndex m H B j v l) +
        if k = j ∧ i = v ∧ l < n then 1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (n - 1 - l) else 0 := by
  rw [localRaw_closed]
  simp only [Prod.fst_add, linearValue_fst_smul, linearValue_fst_sum, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  congr 1
  have he (h : ℕ) (hh : h ∈ Finset.range n) :
      Finsupp.single (queryIndex m H B k i 0 + 4 * h) (1 : ℝ) (queryIndex m H B j v l) =
        if k = j ∧ i = v ∧ h = l then 1 else 0 := by
    have hp : queryIndex m H B k i 0 + 4 * h = queryIndex m H B k i h := by simp [queryIndex]
    rw [hp]
    have heq : queryIndex m H B k i h = queryIndex m H B j v l ↔ k = j ∧ i = v ∧ h = l := by
      constructor
      · exact queryIndex_injective m H B k i h j v l hi hv (by have := Finset.mem_range.mp hh; omega) hl
      · rintro ⟨rfl, rfl, rfl⟩
        rfl
    simp only [Finsupp.single_apply, heq]
  calc
    _ = ∑ h ∈ Finset.range n, (1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (n - 1 - h)) *
        (if k = j ∧ i = v ∧ h = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [he h hh]
    _ = _ := by by_cases hk : k = j <;> by_cases hiv : i = v <;> simp [hk, hiv]

noncomputable def estimator (m H B : ℕ) (η : ℝ) (k i h : ℕ) : LinearValue :=
  localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0) (bufferValue m H B (canonicalTuning η B) k) (h + 1)

lemma estimator_at_query (workers m H B k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hi : i < m) (hv : v < m) (hh : h < H) (hl : l < H) :
    (estimator m H B η k i h).1 (queryIndex m H B j v l) =
      (if j < k then (1 - 1 / (B : ℝ)) ^ (h + 1) * (1 / ((m : ℝ) * B) *
        (1 - 1 / (B : ℝ)) ^ (H - 1 - l) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - 1 - j)) else 0) +
        if k = j ∧ i = v ∧ l ≤ h then 1 / (B : ℝ) * (1 - 1 / (B : ℝ)) ^ (h - l) else 0 := by
  rw [estimator, localRaw_at_query m H B k i (h + 1) j v l _ hi hv (by omega) hl,
    buffer_at_query workers m H B k j v l η ht hw0 hw hm hv hl]
  simp only [Nat.add_sub_cancel, Nat.lt_succ_iff, mul_ite, mul_zero]

lemma estimator_nonneg (workers m H B k i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (q : ℕ) : 0 ≤ (estimator m H B η k i h).1 q := by
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  have hraw : 0 ≤ (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
      (bufferValue m H B (canonicalTuning η B) k) (h + 1)).1 q := by
    rw [localRaw_split]
    change 0 ≤ (1 - 1 / (B : ℝ)) ^ (h + 1) * (bufferValue m H B (canonicalTuning η B) k).1 q +
      (localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0) 0 (h + 1)).1 q
    exact add_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (buffer_coefficient_bounds workers m H B η ht hw0 hw hm hB q k).1)
      (localRaw_zero_upper _ _ _ _ hα0 hα1).1
  exact hraw

lemma sharpIndex_mem (m H B K k i h : ℕ) (hk : k < K) (hi : i < m) (hh : h < H) :
    sharpIndex m H B k i h ∈ sharpSet m H B K :=
  Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk,
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
      Finset.mem_image.mpr ⟨h, Finset.mem_range.mpr hh, rfl⟩⟩⟩

lemma estimator_mass (workers m H B K k i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hk : k < K) (hi : i < m) (hh : h < H) :
    (∑ q ∈ querySet m H B K, (estimator m H B η k i h).1 q) = 1 := by
  have hs := sharedPrefix_sets workers m H K B _ ht hw0 hw
  have he : sharpIndex m H B k i h ∈ (codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2).sharps := by
    rw [hs.2.1]
    exact sharpIndex_mem m H B K k i h hk hi hh
  have hmass := (sharedPrefix_estimators workers m H K B η ht hw0 hw hm hB _ he).2.1
  rw [hs.1, (sharedPrefix_records workers m H K B k i h η ht hw0 hw hk hi hh).2] at hmass
  exact hmass

lemma query_direction_bounds (workers m H B K q j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hη : 0 ≤ η) (hq : q ∈ querySet m H B K) (hv : v < m) (hl : l < H) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    0 ≤ (new.queryPoints q).2 (sharpIndex m H B j v l) ∧
      (new.queryPoints q).2 (sharpIndex m H B j v l) ≤ 1 / (H : ℝ) * η := by
  dsimp only
  have hc : 0 ≤ 1 / (H : ℝ) * η := mul_nonneg (by positivity) hη
  have hm0 : 0 ≤ 1 / (m : ℝ) := by positivity
  have hm1 : 1 / (m : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hm)).mpr (by exact_mod_cast hm)
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hinit
    rw [sharedPrefix_initial_records workers m H K B u _ ht hw0 hw (Finset.mem_range.mp hu)]
    simpa using hc
  · obtain ⟨k, hk, i, hi, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    rw [query_direction workers m H B K k i h j v l η ht hw0 hw
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hi) (Finset.mem_range.mp hh) hv hl]
    by_cases hjk : j < k
    · have he : ¬(k = j ∧ i = v ∧ l < h) := by rintro ⟨rfl, _, _⟩; omega
      simp only [ite_eq_left hjk, ite_eq_right he, mul_one, mul_zero, add_zero]
      exact ⟨mul_nonneg hm0 hc, by nlinarith [mul_le_mul_of_nonneg_right hm1 hc]⟩
    · simp only [ite_eq_right hjk, mul_zero, zero_add]
      split_ifs
      · simpa only [mul_one] using And.intro hc le_rfl
      · simp only [mul_zero]
        exact ⟨le_rfl, hc⟩

lemma query_distance_le (workers m H B K k q j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hη : 0 < η) (hq : q ∈ querySet m H B K) (hv : v < m) (hl : l < H) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    |((new.queryPoints q).2 (sharpIndex m H B j v l) -
      (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l)) / η| ≤ 1 / (H : ℝ) := by
  dsimp only
  have hc : 0 ≤ 1 / (H : ℝ) * η := by positivity
  have hm0 : 0 ≤ 1 / (m : ℝ) := by positivity
  have hm1 : 1 / (m : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hm)).mpr (by exact_mod_cast hm)
  have hqv := query_direction_bounds workers m H B K q j v l η ht hw0 hw hm hη.le hq hv hl
  have hmv : 0 ≤ (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l) ∧
      (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l) ≤ 1 / (H : ℝ) * η := by
    rw [mainValue_direction workers m H B k j v l η ht hw0 hw hv hl]
    split_ifs
    · simp only [mul_one]
      exact ⟨mul_nonneg hm0 hc, by nlinarith [mul_le_mul_of_nonneg_right hm1 hc]⟩
    · simp only [mul_zero]
      exact ⟨le_rfl, hc⟩
  rw [abs_div, abs_of_pos hη]
  apply (div_le_iff₀ hη).mpr
  exact abs_le.mpr ⟨by linarith [hqv.1, hmv.2], by linarith [hqv.2, hmv.1]⟩

noncomputable def queryTransport (m H B K : ℕ) (η : ℝ) (k i h j v l : ℕ) : ℝ :=
  let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
  ∑ q ∈ querySet m H B K, |(estimator m H B η k i h).1 q| *
    |((new.queryPoints q).2 (sharpIndex m H B j v l) -
      (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l)) / η|

lemma queryTransport_nonneg (m H B K : ℕ) (η : ℝ) (k i h j v l : ℕ) :
    0 ≤ queryTransport m H B K η k i h j v l :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

lemma queryTransport_le (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hη : 0 < η) (hk : k < K) (hi : i < m) (hh : h < H)
    (hv : v < m) (hl : l < H) : queryTransport m H B K η k i h j v l ≤ 1 / (H : ℝ) := by
  calc
    _ ≤ ∑ q ∈ querySet m H B K, (estimator m H B η k i h).1 q * (1 / (H : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_of_nonneg (estimator_nonneg workers m H B k i h η ht hw0 hw hm hB q)]
      exact mul_le_mul_of_nonneg_left (query_distance_le workers m H B K k q j v l η ht hw0 hw hm hη hq hv hl)
        (estimator_nonneg workers m H B k i h η ht hw0 hw hm hB q)
    _ = _ := by rw [← Finset.sum_mul, estimator_mass workers m H B K k i h η ht hw0 hw hm hB hk hi hh, one_mul]

lemma queryTransport_current_other (workers m H B K k i h v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hi : i < m) (hh : h < H) (hv : v < m) (hl : l < H) (hiv : i ≠ v) :
    queryTransport m H B K η k i h k v l = 0 := by
  unfold queryTransport
  apply Finset.sum_eq_zero
  intro q hq
  rw [mainValue_direction workers m H B k k v l η ht hw0 hw hv hl]
  simp only [lt_self_iff_false]
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hinit
    rw [sharedPrefix_initial_records workers m H K B u _ ht hw0 hw (Finset.mem_range.mp hu)]
    simp
  · obtain ⟨r, hr, w, hw', u, hu, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    have hr' := Finset.mem_range.mp hr
    have hw'' := Finset.mem_range.mp hw'
    have hu' := Finset.mem_range.mp hu
    by_cases hrk : r < k
    · rw [query_direction workers m H B K r w u k v l η ht hw0 hw hr' hw'' hu' hv hl]
      simp [show ¬k < r by omega, show r ≠ k by omega]
    · by_cases hkr : k = r
      · subst r
        by_cases hwi : w = i
        · subst w
          rw [query_direction workers m H B K k i u k v l η ht hw0 hw hr' hi hu' hv hl]
          simp [hiv]
        · rw [estimator_at_query workers m H B k i h k w u η ht hw0 hw hm hi hw'' hh hu']
          simp [Ne.symm hwi]
      · rw [estimator_at_query workers m H B k i h r w u η ht hw0 hw hm hi hw'' hh hu']
        simp [hrk, hkr]

lemma queryTransport_later_zero (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hi : i < m) (hh : h < H) (hv : v < m) (hl : l < H) (hkj : k < j) :
    queryTransport m H B K η k i h j v l = 0 := by
  unfold queryTransport
  apply Finset.sum_eq_zero
  intro q hq
  rw [mainValue_direction workers m H B k j v l η ht hw0 hw hv hl]
  simp only [ite_eq_right (show ¬j < k by omega), mul_zero, sub_zero]
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hinit
    rw [sharedPrefix_initial_records workers m H K B u _ ht hw0 hw (Finset.mem_range.mp hu)]
    simp
  · obtain ⟨r, hr, w, hw', u, hu, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    have hr' := Finset.mem_range.mp hr
    have hw'' := Finset.mem_range.mp hw'
    have hu' := Finset.mem_range.mp hu
    by_cases hrk : r ≤ k
    · rw [query_direction workers m H B K r w u j v l η ht hw0 hw hr' hw'' hu' hv hl]
      simp [show ¬j < r by omega, show r ≠ j by omega]
    · rw [estimator_at_query workers m H B k i h r w u η ht hw0 hw hm hi hw'' hh hu']
      simp [show ¬r < k by omega, show k ≠ r by omega]

lemma normalized_main_direction (workers m H B k j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hη : 0 < η) (hv : v < m) (hl : l < H) :
    (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l) / η =
      (1 / (m : ℝ)) * (1 / (H : ℝ)) * if j < k then 1 else 0 := by
  rw [mainValue_direction workers m H B k j v l η ht hw0 hw hv hl]
  apply (div_eq_iff hη.ne').mpr
  ring

lemma normalized_query_direction (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hη : 0 < η) (hk : k < K) (hi : i < m) (hh : h < H) (hv : v < m) (hl : l < H) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    (new.queryPoints (queryIndex m H B k i h)).2 (sharpIndex m H B j v l) / η =
      (1 / (m : ℝ)) * (1 / (H : ℝ)) * (if j < k then 1 else 0) +
        (1 / (H : ℝ)) * if k = j ∧ i = v ∧ l < h then 1 else 0 := by
  dsimp only
  rw [query_direction workers m H B K k i h j v l η ht hw0 hw hk hi hh hv hl]
  apply (div_eq_iff hη.ne').mpr
  ring

lemma query_distance_historical (workers m H B K k q j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hη : 0 < η) (hq : q ∈ querySet m H B K) (hv : v < m) (hl : l < H) (hjk : j < k) :
    let new := codeSymbolic (canonicalTuning η B) (sharedPrefix m H K B).2
    |((new.queryPoints q).2 (sharpIndex m H B j v l) -
      (mainValue m H B (canonicalTuning η B) k).2 (sharpIndex m H B j v l)) / η| ≤
        (1 / (m : ℝ)) * (1 / (H : ℝ)) * (if q ∈ querySet m H B (j + 1) then 1 else 0) +
          (1 / (H : ℝ)) * if q ∈ workerQueries m H B j v then 1 else 0 := by
  dsimp only
  have hc : 0 ≤ (1 / (m : ℝ)) * (1 / (H : ℝ)) := by positivity
  have hd : 0 ≤ 1 / (H : ℝ) := by positivity
  rw [sub_div, normalized_main_direction workers m H B k j v l η ht hw0 hw hη hv hl,
    ite_eq_left hjk, mul_one]
  rcases Finset.mem_union.mp hq with hinit | hround
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hinit
    have hmem : 1 + u ∈ querySet m H B (j + 1) := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    rw [sharedPrefix_initial_records workers m H K B u _ ht hw0 hw (Finset.mem_range.mp hu)]
    simp only [Prod.snd_zero, Finsupp.coe_zero, Pi.zero_apply, zero_div, zero_sub, abs_neg,
      abs_of_nonneg hc, ite_eq_left hmem, mul_one]
    exact le_add_of_nonneg_right (by positivity)
  · obtain ⟨r, hr, w, hw', u, hu, rfl⟩ := by
      simpa only [Finset.mem_biUnion, roundQueries, Finset.mem_image] using hround
    have hr' := Finset.mem_range.mp hr
    have hw'' := Finset.mem_range.mp hw'
    have hu' := Finset.mem_range.mp hu
    rw [normalized_query_direction workers m H B K r w u j v l η ht hw0 hw hη hr' hw'' hu' hv hl]
    by_cases hjr : j < r
    · have he : ¬(r = j ∧ w = v ∧ l < u) := by rintro ⟨rfl, _, _⟩; omega
      simp only [ite_eq_left hjr, ite_eq_right he, mul_one, mul_zero, add_zero, sub_self, abs_zero]
      positivity
    · have hmem : queryIndex m H B r w u ∈ querySet m H B (j + 1) :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (by omega),
          Finset.mem_biUnion.mpr ⟨w, hw', Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩⟩)
      rw [ite_eq_right hjr, mul_zero, zero_add, ite_eq_left hmem, mul_one]
      by_cases he : r = j ∧ w = v ∧ l < u
      · obtain ⟨hrj, hwv, hlu⟩ := he
        subst r
        subst w
        have hmemw : queryIndex m H B j v u ∈ workerQueries m H B j v := Finset.mem_image.mpr ⟨u, hu, rfl⟩
        rw [ite_eq_left (by exact ⟨rfl, rfl, hlu⟩), ite_eq_left hmemw, mul_one]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [ite_eq_right he, mul_zero, zero_sub, abs_neg, abs_of_nonneg hc]
        exact le_add_of_nonneg_right (by positivity)

lemma workerQueries_subset (m H B j v K : ℕ) (hj : j < K) (hv : v < m) :
    workerQueries m H B j v ⊆ querySet m H B K := by
  intro q hq
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_range.mpr hv, hq⟩⟩)

lemma indicator_sum_subset (s t : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (ht : t ⊆ s) :
    (∑ q ∈ s, f q * (c * if q ∈ t then 1 else 0)) = c * ∑ q ∈ t, f q := by
  calc
    _ = ∑ q ∈ s, if q ∈ t then c * f q else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> ring
    _ = ∑ q ∈ t, c * f q := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
    _ = _ := by rw [Finset.mul_sum]

lemma queryTransport_historical (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hη : 0 < η) (hk : k < K)
    (hv : v < m) (hl : l < H) (hjk : j < k) :
    queryTransport m H B K η k i h j v l ≤
      (1 - 1 / (B : ℝ)) ^ (h + 1) * (1 / ((m : ℝ) * H)) *
        ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) * (2 - (1 - 1 / (B : ℝ)) ^ H) := by
  have hnonneg := estimator_nonneg workers m H B k i h η ht hw0 hw hm hB
  have hsum : queryTransport m H B K η k i h j v l ≤
      (1 / (m : ℝ)) * (1 / (H : ℝ)) * (∑ q ∈ querySet m H B (j + 1), (estimator m H B η k i h).1 q) +
        (1 / (H : ℝ)) * (∑ q ∈ workerQueries m H B j v, (estimator m H B η k i h).1 q) := by
    calc
      _ ≤ ∑ q ∈ querySet m H B K, (estimator m H B η k i h).1 q *
          ((1 / (m : ℝ)) * (1 / (H : ℝ)) * (if q ∈ querySet m H B (j + 1) then 1 else 0) +
            (1 / (H : ℝ)) * if q ∈ workerQueries m H B j v then 1 else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [abs_of_nonneg (hnonneg q)]
        exact mul_le_mul_of_nonneg_left
          (query_distance_historical workers m H B K k q j v l η ht hw0 hw hη hq hv hl hjk) (hnonneg q)
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib,
          indicator_sum_subset _ _ _ _ (querySet_mono m H B (j + 1) K (by omega)),
          indicator_sum_subset _ _ _ _ (workerQueries_subset m H B j v K (by omega) hv)]
  dsimp only [estimator] at hsum
  rw [local_old_mass workers m H B k i (h + 1) (j + 1) η ht hw0 hw hm hB (by omega),
    local_worker_mass workers m H B k i (h + 1) j v η ht hw0 hw hm hv hjk] at hsum
  rw [show k - (j + 1) = k - j - 1 by omega, show k - 1 - j = k - j - 1 by omega] at hsum
  apply hsum.trans_eq
  ring

end LongTails.Proofs.BirchNonEuclideanSharedTransport
