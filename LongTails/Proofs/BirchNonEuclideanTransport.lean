import LongTails.Proofs.BirchNonEuclideanDelta

namespace LongTails.Proofs.BirchNonEuclideanTransport

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchDelayedCoefficients

lemma querySet_mono (H B j k : ℕ) (hjk : j ≤ k) : querySet H B j ⊆ querySet H B k := by
  apply Finset.union_subset_union_right
  intro q hq
  obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.mp hq
  exact Finset.mem_biUnion.mpr ⟨i, Finset.range_mono hjk hi, hq⟩

lemma querySet_lt (H B k q : ℕ) (hq : q ∈ querySet H B k) : q < B + 2 + k * (4 * H + 8) := by
  rcases Finset.mem_union.mp hq with hi | hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hj
    omega
  · obtain ⟨j, hj, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
    have hj' := Finset.mem_range.mp hj
    have hh' := Finset.mem_range.mp hh
    have hm := Nat.mul_le_mul_right (4 * H + 8) (show j + 1 ≤ k by omega)
    rw [Nat.add_mul] at hm
    dsimp [queryIndex]
    omega

lemma packetCoefficient_before (H B j k q : ℕ) (hjk : j ≤ k) (hq : q ∈ querySet H B j) :
    packetCoefficient H B k q = 0 := by
  have hlt := querySet_lt H B j q hq
  have hm := Nat.mul_le_mul_right (4 * H + 8) hjk
  apply Finset.sum_eq_zero
  intro h _
  have he : queryIndex H B k h ≠ q := by dsimp [queryIndex]; omega
  simp [he]

lemma codeSymbolic_vector_supported (s : CodeState) (t : Tuning) (j : ℕ) :
    ((codeSymbolic t s).vectors j).1 ∈
      Finsupp.supported ℝ ℝ ((codeSymbolic t s).queries : Set ℕ) := by
  let a : Program := {
    instructions := codeInstructions t s
    outputWorker := 0
    outputCount := 0
    outputPoint := fun _ => 0 }
  exact ((LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_maps_supported a).vectors j).1

noncomputable def oldMass (H B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (j k : ℕ) : ℝ :=
  ∑ q ∈ querySet H B j, (bufferValue H B dispatch worker t k).1 q

lemma oldMass_before (workers H B j k : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hB : 0 < B) (hkj : k ≤ j) :
    oldMass H B dispatch worker (canonicalTuning η B) j k = 1 := by
  let t := canonicalTuning η B
  have hs := codeSymbolic_vector_supported (deltaPrefix H dispatch worker k B).2 t (momentumIndex H B k)
  have hsets := (deltaPrefix_sets workers H k B dispatch worker t ht hw0 hw).1
  rw [hsets] at hs
  have hs' : (bufferValue H B dispatch worker t k).1 ∈ Finsupp.supported ℝ ℝ (querySet H B j : Set ℕ) := by
    exact (Finsupp.supported_mono (show (querySet H B k : Set ℕ) ⊆ querySet H B j from querySet_mono H B k j hkj)) hs
  have hm := (buffer_mass_direction workers H B dispatch worker η ht hw0 hw hsource hB k).1
  have he := Finsupp.linearCombination_apply_of_mem_supported (R := ℝ) (v := fun _ => (1 : ℝ)) hs'
  simpa only [coefficientMass, smul_eq_mul, mul_one, oldMass] using he.symm.trans hm

lemma oldMass_recurrence (workers H B j k : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hs : dispatch k ≤ k) (hjk : j ≤ k) :
    oldMass H B dispatch worker (canonicalTuning η B) j (k + 1) =
      oldMass H B dispatch worker (canonicalTuning η B) j k -
        (1 - (1 - 1 / (B : ℝ)) ^ H) * oldMass H B dispatch worker (canonicalTuning η B) j (dispatch k) := by
  dsimp only [oldMass]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [buffer_coefficient_recurrence workers H k B dispatch worker η ht hw0 hw hs q,
    packetCoefficient_before H B j k q hjk hq, add_zero]

lemma oldMass_tail (workers H B R j : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) :
    ∀ k, oldMass H B dispatch worker (canonicalTuning η B) j k ≤
      ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j) := by
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hρ0 : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  have hρ1 : (1 - 1 / (B : ℝ)) ^ H ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hp := LongTails.Proofs.BirchDelayedCoefficients.old_mass_tail
    (oldMass H B dispatch worker (canonicalTuning η B) j) dispatch j
    (1 - (1 - 1 / (B : ℝ)) ^ H) (by linarith) (by linarith)
    (by
      intro k
      apply Finset.sum_nonneg
      intro q _
      exact (buffer_coefficient_bounds workers H B R dispatch worker η ht hw0 hw hsource hB hlam hdelay q k).1)
    (fun k hk => oldMass_before workers H B j k dispatch worker η ht hw0 hw (fun k => (hsource k).1) hB hk)
    (fun k => (hsource k).1)
    (fun k hk => oldMass_recurrence workers H B j k dispatch worker η ht hw0 hw (hsource k).1 hk)
  intro k
  by_cases hkj : k ≤ j
  · rw [oldMass_before workers H B j k dispatch worker η ht hw0 hw (fun k => (hsource k).1) hB hkj,
      Nat.sub_eq_zero_of_le hkj, pow_zero]
  · have he : j + (k - j) = k := by omega
    simpa only [he, sub_sub_cancel] using hp (k - j)

lemma sharpIndex_injective (H B k h l j : ℕ) (hh : h < H) (hj : j < H)
    (he : sharpIndex H B k h = sharpIndex H B l j) : k = l ∧ h = j := by
  exact queryIndex_injective H B k h l j hh hj (by dsimp [sharpIndex] at he; omega)

lemma sharp_sum_apply (H B k n j t : ℕ) (hn : n ≤ H) (ht : t < H) :
    (∑ h ∈ Finset.range n, Finsupp.single (sharpIndex H B k h) (1 : ℝ) (sharpIndex H B j t)) =
      if k = j ∧ t < n then 1 else 0 := by
  have he (h : ℕ) (hh : h ∈ Finset.range n) :
      Finsupp.single (sharpIndex H B k h) (1 : ℝ) (sharpIndex H B j t) =
        if k = j ∧ h = t then 1 else 0 := by
    have hi : sharpIndex H B k h = sharpIndex H B j t ↔ k = j ∧ h = t := by
      constructor
      · exact sharpIndex_injective H B k h j t (by have := Finset.mem_range.mp hh; omega) ht
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [Finsupp.single_apply, hi]
  rw [Finset.sum_congr rfl he]
  by_cases hk : k = j <;> simp [hk]

lemma mainValue_direction (workers H B K j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (htH : t < H) :
    (mainValue H B dispatch worker (canonicalTuning η B) K).2 (sharpIndex H B j t) =
      (1 / (H : ℝ) * η) * if j < K then 1 else 0 := by
  rw [mainValue_closed workers H B K dispatch worker η ht hw0 hw hsource]
  simp only [linearValue_snd_smul, linearValue_snd_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  simp_rw [sharp_sum_apply H B _ H j t le_rfl htH]
  simp [htH]

lemma localPath_direction (H B k h j t : ℕ) (v : LinearValue) (η : ℝ)
    (hh : h ≤ H) (ht : t < H) :
    (localPath (1 / (H : ℝ) * η) (queryIndex H B k 0) v h).2 (sharpIndex H B j t) =
      v.2 (sharpIndex H B j t) + (1 / (H : ℝ) * η) * if k = j ∧ t < h then 1 else 0 := by
  rw [localPath_closed]
  simp only [Prod.snd_add, linearValue_snd_smul, linearValue_snd_sum, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  have he : (∑ u ∈ Finset.range h, Finsupp.single (queryIndex H B k 0 + 4 * u + 2) (1 : ℝ)
      (sharpIndex H B j t)) = if k = j ∧ t < h then 1 else 0 := by
    convert sharp_sum_apply H B k h j t hh ht using 1
    apply Finset.sum_congr rfl
    intro u _
    congr 2
  rw [he]

lemma query_direction (workers H B K k h j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hk : k < K) (hh : h < H) (htH : t < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    (m.queryPoints (queryIndex H B k h)).2 (sharpIndex H B j t) =
      (1 / (H : ℝ) * η) * ((if j < dispatch k then 1 else 0) +
        if k = j ∧ t < h then 1 else 0) := by
  dsimp only
  rw [(deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k) hk hh).1,
    localPath_direction H B k h j t _ η (by omega) htH,
    mainValue_direction workers H B (dispatch k) j t dispatch worker η ht hw0 hw hsource htH]
  ring

lemma localRaw_sum_old (α : ℝ) (first : ℕ) (v : LinearValue) (n : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q < first) :
    (∑ q ∈ s, (localRaw α first v n).1 q) = (1 - α) ^ n * ∑ q ∈ s, v.1 q := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact localRaw_old α first v n q (hs q hq)

lemma local_old_mass_le (workers H B R k n j : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hjk : j ≤ k) :
    (∑ q ∈ querySet H B j, (localRaw (1 / (B : ℝ)) (queryIndex H B k 0)
      (bufferValue H B dispatch worker (canonicalTuning η B) (dispatch k)) n).1 q) ≤
        ((1 - 1 / (B : ℝ)) ^ H) ^ (dispatch k - j) := by
  have hq : ∀ q ∈ querySet H B j, q < queryIndex H B k 0 := by
    intro q hq
    have hlt := querySet_lt H B j q hq
    have hm := Nat.mul_le_mul_right (4 * H + 8) hjk
    dsimp [queryIndex]
    omega
  rw [localRaw_sum_old _ _ _ _ _ hq]
  have hmass : 0 ≤ oldMass H B dispatch worker (canonicalTuning η B) j (dispatch k) := by
    apply Finset.sum_nonneg
    intro q _
    exact (buffer_coefficient_bounds workers H B R dispatch worker η ht hw0 hw hsource hB hlam hdelay q (dispatch k)).1
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hp : (1 - 1 / (B : ℝ)) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hp hmass
  have htail := oldMass_tail workers H B R j dispatch worker η ht hw0 hw hsource hB hlam hdelay (dispatch k)
  calc
    _ ≤ oldMass H B dispatch worker (canonicalTuning η B) j (dispatch k) := by
      simpa only [one_mul, oldMass] using hmul
    _ ≤ _ := htail

lemma local_old_mass_far (workers H B R k n j : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1)
    (hfar : j + 2 * R + 1 ≤ k) :
    (∑ q ∈ querySet H B (j + R + 1), (localRaw (1 / (B : ℝ)) (queryIndex H B k 0)
      (bufferValue H B dispatch worker (canonicalTuning η B) (dispatch k)) n).1 q) ≤
        ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) := by
  apply (local_old_mass_le workers H B R k n (j + R + 1) dispatch worker η ht hw0 hw hsource hB hlam hdelay (by omega)).trans
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  apply pow_le_pow_of_le_one
  · exact pow_nonneg (by linarith) _
  · exact pow_le_one₀ (by linarith) (by linarith)
  · have := hsource k
    omega

lemma local_indicator_bounds (s k h j t : ℕ) (hs : s ≤ k) :
    0 ≤ ((if j < s then 1 else 0) + if k = j ∧ t < h then 1 else 0 : ℝ) ∧
      ((if j < s then 1 else 0) + if k = j ∧ t < h then 1 else 0 : ℝ) ≤ 1 := by
  by_cases hj : j < s
  · have hn : ¬(k = j ∧ t < h) := by rintro ⟨rfl, _⟩; omega
    simp [hj, hn]
  · by_cases hb : k = j ∧ t < h <;> simp [hj, hb]

lemma query_direction_bounds (workers H B K q j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hη : 0 ≤ η) (hq : q ∈ querySet H B K) (htH : t < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    0 ≤ (m.queryPoints q).2 (sharpIndex H B j t) ∧
      (m.queryPoints q).2 (sharpIndex H B j t) ≤ 1 / (H : ℝ) * η := by
  dsimp only
  have hγ : 0 ≤ 1 / (H : ℝ) * η := mul_nonneg (by positivity) hη
  rcases Finset.mem_union.mp hq with hi | hi
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    rw [deltaPrefix_initial_records workers H K B u dispatch worker _ ht hw0 hw (Finset.mem_range.mp hu)]
    exact ⟨le_rfl, hγ⟩
  · obtain ⟨k, hk, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
    rw [query_direction workers H B K k h j t dispatch worker η ht hw0 hw hsource
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hh) htH]
    have hb := local_indicator_bounds (dispatch k) k h j t (hsource k)
    exact ⟨mul_nonneg hγ hb.1, by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 hγ⟩

lemma query_distance_le (workers H B K k q j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hη : 0 < η) (hq : q ∈ querySet H B K) (htH : t < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    |((m.queryPoints q).2 (sharpIndex H B j t) -
      (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t)) / η| ≤ 1 / (H : ℝ) := by
  dsimp only
  have hγ : 0 ≤ 1 / (H : ℝ) * η := mul_nonneg (by positivity) (le_of_lt hη)
  have hqv := query_direction_bounds workers H B K q j t dispatch worker η ht hw0 hw hsource (le_of_lt hη) hq htH
  have hmv : 0 ≤ (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t) ∧
      (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t) ≤ 1 / (H : ℝ) * η := by
    rw [mainValue_direction workers H B k j t dispatch worker η ht hw0 hw hsource htH]
    split_ifs <;> simpa using hγ
  rw [abs_div, abs_of_pos hη]
  apply (div_le_iff₀ hη).2
  exact abs_le.mpr ⟨by linarith [hqv.1, hmv.2], by linarith [hqv.2, hmv.1]⟩

lemma query_direction_later_zero (workers H B K k q j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hk : k < K) (hq : q ∈ querySet H B (k + 1))
    (hjk : k < j) (htH : t < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    (m.queryPoints q).2 (sharpIndex H B j t) = 0 := by
  dsimp only
  rcases Finset.mem_union.mp hq with hi | hi
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    rw [deltaPrefix_initial_records workers H K B u dispatch worker _ ht hw0 hw (Finset.mem_range.mp hu)]
    rfl
  · obtain ⟨l, hl, h, hh, rfl⟩ := by
      simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
    have hl' := Finset.mem_range.mp hl
    have hs := hsource l
    rw [query_direction workers H B K l h j t dispatch worker η ht hw0 hw hsource
      (by omega) (Finset.mem_range.mp hh) htH]
    have hj : ¬j < dispatch l := by omega
    have hlj : l ≠ j := by omega
    simp [hj, hlj]

lemma estimator_future_query_zero (workers H B K k h q : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hk : k < K) (hh : h < H)
    (hq : q ∈ querySet H B K) (hfuture : q ∉ querySet H B (k + 1)) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    (m.sharpInputs (sharpIndex H B k h)).1 q = 0 := by
  dsimp only
  rw [(deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k) hk hh).2]
  apply localRaw_future_zero
  · exact source_buffer_future_zero workers H B k dispatch worker _ ht hw0 hw (hsource k)
  · rcases Finset.mem_union.mp hq with hi | hi
    · exact False.elim (hfuture (Finset.mem_union_left _ hi))
    · obtain ⟨l, hl, u, hu, rfl⟩ := by
        simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
      have hkl : k + 1 ≤ l := by
        by_contra he
        apply hfuture
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨l, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
      have hm := Nat.mul_le_mul_right (4 * H + 8) hkl
      rw [Nat.add_mul] at hm
      dsimp [queryIndex]
      omega

lemma query_direction_recent (workers H B R K k q j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hk : k < K)
    (hq : q ∈ querySet H B (k + 1)) (hrecent : q ∉ querySet H B (j + R + 1))
    (hjk : j < k) (htH : t < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    (m.queryPoints q).2 (sharpIndex H B j t) =
      (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t) := by
  dsimp only
  rcases Finset.mem_union.mp hq with hi | hi
  · exact False.elim (hrecent (Finset.mem_union_left _ hi))
  · obtain ⟨l, hl, u, hu, rfl⟩ := by
      simpa only [Finset.mem_biUnion, packetQueries, Finset.mem_image] using hi
    have hl' := Finset.mem_range.mp hl
    have hjl : j + R + 1 ≤ l := by
      by_contra he
      apply hrecent
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨l, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    have hs := hsource l
    have hjs : j < dispatch l := by omega
    have hlj : l ≠ j := by omega
    rw [query_direction workers H B K l u j t dispatch worker η ht hw0 hw (fun k => (hsource k).1)
      (by omega) (Finset.mem_range.mp hu) htH,
      mainValue_direction workers H B k j t dispatch worker η ht hw0 hw (fun k => (hsource k).1) htH]
    simp [hjs, hlj, hjk]

noncomputable def queryTransport (H B K : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (k h j t : ℕ) : ℝ :=
  let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
  ∑ q ∈ querySet H B K, |(m.sharpInputs (sharpIndex H B k h)).1 q| *
    |((m.queryPoints q).2 (sharpIndex H B j t) -
      (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t)) / η|

lemma sharpIndex_mem (H B K k h : ℕ) (hk : k < K) (hh : h < H) :
    sharpIndex H B k h ∈ sharpSet H B K :=
  Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk,
    Finset.mem_image.mpr ⟨h, Finset.mem_range.mpr hh, rfl⟩⟩

lemma estimator_mass_bounds (workers H B R K k h : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hk : k < K) (hh : h < H) :
    let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
    (∀ q, 0 ≤ (m.sharpInputs (sharpIndex H B k h)).1 q) ∧
      (∑ q ∈ querySet H B K, (m.sharpInputs (sharpIndex H B k h)).1 q) = 1 := by
  intro m
  have hr := (deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k).1 hk hh).2
  constructor
  · intro q
    rw [hr]
    exact (local_buffer_coefficient_bounds workers H B R k (h + 1) dispatch worker η ht hw0 hw hsource hB hlam hdelay q).1
  · have hs := deltaPrefix_sets workers H K B dispatch worker (canonicalTuning η B) ht hw0 hw
    have he : sharpIndex H B k h ∈ m.sharps := by rw [hs.2.1]; exact sharpIndex_mem H B K k h hk hh
    have hm := (deltaPrefix_estimators workers H K B R dispatch worker η ht hw0 hw hsource hB hlam hdelay _ he).2.1
    rwa [hs.1] at hm

lemma queryTransport_nonneg (H B K : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ) (k h j t : ℕ) :
    0 ≤ queryTransport H B K dispatch worker η k h j t := by
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma queryTransport_le (workers H B R K k h j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B) (hη : 0 < η)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hk : k < K) (hh : h < H) (htH : t < H) :
    queryTransport H B K dispatch worker η k h j t ≤ 1 / (H : ℝ) := by
  have hm := estimator_mass_bounds workers H B R K k h dispatch worker η ht hw0 hw hsource hB hlam hdelay hk hh
  let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
  calc
    _ ≤ ∑ q ∈ querySet H B K, (m.sharpInputs (sharpIndex H B k h)).1 q * (1 / (H : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_of_nonneg (hm.1 q)]
      exact mul_le_mul_of_nonneg_left
        (query_distance_le workers H B K k q j t dispatch worker η ht hw0 hw (fun k => (hsource k).1) hη hq htH) (hm.1 q)
    _ = _ := by rw [← Finset.sum_mul, hm.2, one_mul]

lemma queryTransport_later_zero (workers H B K k h j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k) (hk : k < K) (hh : h < H) (hjk : k < j) (htH : t < H) :
    queryTransport H B K dispatch worker η k h j t = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqp : q ∈ querySet H B (k + 1)
  · rw [query_direction_later_zero workers H B K k q j t dispatch worker η ht hw0 hw hsource hk hqp hjk htH,
      mainValue_direction workers H B k j t dispatch worker η ht hw0 hw hsource htH]
    simp [show ¬j < k by omega]
  · rw [estimator_future_query_zero workers H B K k h q dispatch worker η ht hw0 hw hsource hk hh hq hqp]
    simp

lemma queryTransport_far (workers H B R K k h j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B) (hη : 0 < η)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hk : k < K) (hh : h < H)
    (htH : t < H) (hfar : j + 2 * R + 1 ≤ k) :
    queryTransport H B K dispatch worker η k h j t ≤
      (1 / (H : ℝ)) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) := by
  let m := codeSymbolic (canonicalTuning η B) (deltaPrefix H dispatch worker K B).2
  let term := fun q => |(m.sharpInputs (sharpIndex H B k h)).1 q| *
    |((m.queryPoints q).2 (sharpIndex H B j t) -
      (mainValue H B dispatch worker (canonicalTuning η B) k).2 (sharpIndex H B j t)) / η|
  have hsub : querySet H B (j + R + 1) ⊆ querySet H B K := querySet_mono H B _ K (by omega)
  have hz : ∀ q ∈ querySet H B K, q ∉ querySet H B (j + R + 1) → term q = 0 := by
    intro q hq hqn
    dsimp only [term, m]
    by_cases hqp : q ∈ querySet H B (k + 1)
    · rw [query_direction_recent workers H B R K k q j t dispatch worker η ht hw0 hw hsource hk hqp hqn (by omega) htH]
      simp
    · rw [estimator_future_query_zero workers H B K k h q dispatch worker η ht hw0 hw (fun k => (hsource k).1) hk hh hq hqp]
      simp
  have heq := Finset.sum_subset hsub hz
  have hm := estimator_mass_bounds workers H B R K k h dispatch worker η ht hw0 hw hsource hB hlam hdelay hk hh
  have hpartial : (∑ q ∈ querySet H B (j + R + 1), (m.sharpInputs (sharpIndex H B k h)).1 q) ≤
      ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) := by
    rw [(deltaPrefix_records workers H K B k h dispatch worker η ht hw0 hw (hsource k).1 hk hh).2]
    exact local_old_mass_far workers H B R k (h + 1) j dispatch worker η ht hw0 hw hsource hB hlam hdelay hfar
  change (∑ q ∈ querySet H B K, term q) ≤ _
  rw [← heq]
  calc
    _ ≤ ∑ q ∈ querySet H B (j + R + 1), (m.sharpInputs (sharpIndex H B k h)).1 q * (1 / (H : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      dsimp only [term]
      rw [abs_of_nonneg (hm.1 q)]
      exact mul_le_mul_of_nonneg_left
        (query_distance_le workers H B K k q j t dispatch worker η ht hw0 hw (fun k => (hsource k).1) hη (hsub hq) htH) (hm.1 q)
    _ = (∑ q ∈ querySet H B (j + R + 1), (m.sharpInputs (sharpIndex H B k h)).1 q) * (1 / (H : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpartial (by positivity : 0 ≤ 1 / (H : ℝ))

lemma queryTransport_envelope (workers H B R K k h j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B) (hη : 0 < η)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hk : k < K) (hh : h < H) (htH : t < H) :
    queryTransport H B K dispatch worker η k h j t ≤
      if j ≤ k then (1 / (H : ℝ)) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) else 0 := by
  by_cases hjk : j ≤ k
  · rw [ite_eq_left hjk]
    by_cases hfar : j + 2 * R + 1 ≤ k
    · exact queryTransport_far workers H B R K k h j t dispatch worker η ht hw0 hw hsource hB hη hlam hdelay hk hh htH hfar
    · have he : k - j - 2 * R - 1 = 0 := by omega
      rw [he, pow_zero, mul_one]
      exact queryTransport_le workers H B R K k h j t dispatch worker η ht hw0 hw hsource hB hη hlam hdelay hk hh htH
  · rw [ite_eq_right hjk, queryTransport_later_zero workers H B K k h j t dispatch worker η ht hw0 hw
      (fun k => (hsource k).1) hk hh (by omega) htH]

lemma sharpSet_sum {α : Type*} [AddCommMonoid α] (H B K : ℕ) (f : ℕ → α) :
    (∑ e ∈ sharpSet H B K, f e) = ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, f (sharpIndex H B k h) := by
  have he : sharpSet H B K = ((Finset.range K) ×ˢ (Finset.range H)).image (fun z => sharpIndex H B z.1 z.2) := by
    ext e
    constructor
    · intro he
      obtain ⟨k, hk, h, hh, he⟩ := by
        simpa only [sharpSet, packetSharps, Finset.mem_biUnion, Finset.mem_image] using he
      exact Finset.mem_image.mpr ⟨(k, h), Finset.mem_product.mpr ⟨hk, hh⟩, he⟩
    · intro he
      obtain ⟨⟨k, h⟩, hkh, he⟩ := Finset.mem_image.mp he
      exact Finset.mem_biUnion.mpr ⟨k, (Finset.mem_product.mp hkh).1,
        Finset.mem_image.mpr ⟨h, (Finset.mem_product.mp hkh).2, he⟩⟩
  rw [he, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy he
    have h := sharpIndex_injective H B x.1 x.2 y.1 y.2
      (Finset.mem_range.mp (Finset.mem_product.mp hx).2)
      (Finset.mem_range.mp (Finset.mem_product.mp hy).2) he
    exact Prod.ext h.1 h.2

def owner (H B e : ℕ) : ℕ := (e - (B + 6)) / (4 * H + 8)

lemma owner_sharp (H B k h : ℕ) (hh : h < H) : owner H B (sharpIndex H B k h) = k := by
  have he : sharpIndex H B k h - (B + 6) = 4 * h + (4 * H + 8) * k := by
    dsimp [sharpIndex, queryIndex]
    rw [Nat.mul_comm (4 * H + 8) k]
    omega
  dsimp only [owner]
  rw [he, Nat.add_mul_div_left _ _ (by omega : 0 < 4 * H + 8), Nat.div_eq_of_lt (by omega), Nat.zero_add]

lemma transport_row (workers H B R K k h : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B) (hη : 0 < η)
    (hH : 0 < H) (hlam0 : 0 < 1 - (1 - 1 / (B : ℝ)) ^ H)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hk : k < K) (hh : h < H) :
    (∑ j ∈ Finset.range K, ∑ t ∈ Finset.range H, queryTransport H B K dispatch worker η k h j t) ≤
      (2 * (R : ℝ) + 1) + 1 / (1 - (1 - 1 / (B : ℝ)) ^ H) := by
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hρ : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  calc
    _ ≤ ∑ j ∈ Finset.range K, ∑ _t ∈ Finset.range H,
        if j ≤ k then (1 / (H : ℝ)) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro t htH
      exact queryTransport_envelope workers H B R K k h j t dispatch worker η ht hw0 hw hsource hB hη hlam hdelay hk hh (Finset.mem_range.mp htH)
    _ = ∑ j ∈ Finset.range K, if j ≤ k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - (2 * R + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      have he : k - j - 2 * R - 1 = k - j - (2 * R + 1) := by omega
      by_cases hj : j ≤ k <;> simp [hj, he, hHr]
    _ ≤ _ := by
      have hp := truncated_geometric_row ((1 - 1 / (B : ℝ)) ^ H) (2 * R + 1) K k hρ (by linarith) hk
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hp

lemma transport_column (workers H B R K j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hB : 0 < B) (hη : 0 < η)
    (hH : 0 < H) (hlam0 : 0 < 1 - (1 - 1 / (B : ℝ)) ^ H)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hj : j < K) (htH : t < H) :
    (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, queryTransport H B K dispatch worker η k h j t) ≤
      (2 * (R : ℝ) + 1) + 1 / (1 - (1 - 1 / (B : ℝ)) ^ H) := by
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have hα : 1 / (B : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)
  have hρ : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  calc
    _ ≤ ∑ k ∈ Finset.range K, ∑ _h ∈ Finset.range H,
        if j ≤ k then (1 / (H : ℝ)) * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 2 * R - 1) else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro h hh
      exact queryTransport_envelope workers H B R K k h j t dispatch worker η ht hw0 hw hsource hB hη hlam hdelay
        (Finset.mem_range.mp hk) (Finset.mem_range.mp hh) htH
    _ = ∑ k ∈ Finset.range K, if j ≤ k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - (2 * R + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      have he : k - j - 2 * R - 1 = k - j - (2 * R + 1) := by omega
      by_cases hj : j ≤ k <;> simp [hj, he, hHr]
    _ ≤ _ := by
      have hp := truncated_geometric_column ((1 - 1 / (B : ℝ)) ^ H) (2 * R + 1) K j hρ (by linarith) hj
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hp

lemma transport_schur (workers H B R K j t : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hH : 0 < H) (hB : 2 * H ≤ B) (hη : 0 < η)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) (hj : j < K) (htH : t < H) :
    (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, (1 / (H : ℝ)) *
      (∑ l ∈ Finset.range K, ∑ u ∈ Finset.range H, queryTransport H B K dispatch worker η k h l u) *
        queryTransport H B K dispatch worker η k h j t) ≤
      (3 * (R : ℝ) + 2 + 2 * (B : ℝ) / (H : ℝ)) ^ 2 * (1 / (H : ℝ)) := by
  have hB0 : 0 < B := by omega
  have hinv := ema_inverse_le H B hH hB
  let s := (Finset.range K) ×ˢ (Finset.range H)
  let C := fun (x y : ℕ × ℕ) => queryTransport H B K dispatch worker η x.1 x.2 y.1 y.2
  let A := 2 * (R : ℝ) + 1 + 1 / (1 - (1 - 1 / (B : ℝ)) ^ H)
  let D := 3 * (R : ℝ) + 2 + 2 * (B : ℝ) / (H : ℝ)
  have hlam0 := hinv.1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : A ≤ D := by
    dsimp [A, D]
    have hR : 0 ≤ (R : ℝ) := by positivity
    linarith [hinv.2]
  have hrow : ∀ x ∈ s, ∑ y ∈ s, C x y ≤ A := by
    intro x hx
    have hp := transport_row workers H B R K x.1 x.2 dispatch worker η ht hw0 hw hsource hB0 hη hH hinv.1 hlam hdelay
      (Finset.mem_range.mp (Finset.mem_product.mp hx).1) (Finset.mem_range.mp (Finset.mem_product.mp hx).2)
    simpa only [s, C, Finset.sum_product, A] using hp
  have hcol : ∀ y ∈ s, ∑ x ∈ s, C x y ≤ A := by
    intro y hy
    have hp := transport_column workers H B R K y.1 y.2 dispatch worker η ht hw0 hw hsource hB0 hη hH hinv.1 hlam hdelay
      (Finset.mem_range.mp (Finset.mem_product.mp hy).1) (Finset.mem_range.mp (Finset.mem_product.mp hy).2)
    simpa only [s, C, Finset.sum_product, A] using hp
  have hh := weighted_schur s C (1 / (H : ℝ)) A D (by positivity) hA hD
    (fun x _ y _ => queryTransport_nonneg H B K dispatch worker η x.1 x.2 y.1 y.2) hrow hcol (j, t)
    (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr htH⟩)
  simpa only [s, C, D, Finset.sum_product] using hh

lemma sharpSet_fiber_sum {α : Type*} [AddCommMonoid α] (H B K k : ℕ)
    (hk : k < K) (f : ℕ → α) :
    (∑ e ∈ (sharpSet H B K).filter (fun e => owner H B e = k), f e) =
      ∑ h ∈ Finset.range H, f (sharpIndex H B k h) := by
  rw [Finset.sum_filter, sharpSet_sum]
  have he : (∑ j ∈ Finset.range K, ∑ h ∈ Finset.range H,
      if owner H B (sharpIndex H B j h) = k then f (sharpIndex H B j h) else 0) =
      ∑ j ∈ Finset.range K, if j = k then ∑ h ∈ Finset.range H, f (sharpIndex H B j h) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∑ h ∈ Finset.range H, if j = k then f (sharpIndex H B j h) else 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [owner_sharp H B j h (Finset.mem_range.mp hh)]
      _ = _ := by by_cases hj : j = k <;> simp [hj]
  rw [he]
  simp [Finset.mem_range.mpr hk]

end LongTails.Proofs.BirchNonEuclideanTransport
