import LongTails.Proofs.BirchNonEuclideanBatch
import LongTails.Proofs.BirchNonEuclideanDeltaCertificate

namespace LongTails.Proofs.BirchNonEuclideanBatchCertificate

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanBatch
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_fst_smul linearValue_snd_smul
  linearValue_fst_sum linearValue_snd_sum coefficientMass coefficientMass_single
  codeSymbolic_sharp_mass weighted_single_sum_le)

def owner (B e : ℕ) : ℕ := e / (3 * B + 3)

lemma owner_sharp (B k : ℕ) : owner B (sharpIndex B k) = k := by
  have he : sharpIndex B k = (3 * B + 2) + (3 * B + 3) * k := by dsimp [sharpIndex]; ring
  rw [owner, he, Nat.add_mul_div_left _ _ (by omega : 0 < 3 * B + 3),
    Nat.div_eq_of_lt (by omega : 3 * B + 2 < 3 * B + 3), Nat.zero_add]

lemma sharpIndex_injective (B : ℕ) : Function.Injective (sharpIndex B) := by
  intro k j h
  have hh := congrArg (owner B) h
  simpa only [owner_sharp] using hh

lemma sharpSet_sum {α : Type*} [AddCommMonoid α] (B K : ℕ) (f : ℕ → α) :
    (∑ e ∈ sharpSet B K, f e) = ∑ k ∈ Finset.range K, f (sharpIndex B k) := by
  rw [sharpSet, Finset.sum_image]
  exact fun _ _ _ _ h => sharpIndex_injective B h

lemma sharpSet_fiber_sum {α : Type*} [AddCommMonoid α] (B K k : ℕ)
    (hk : k < K) (f : ℕ → α) :
    (∑ e ∈ (sharpSet B K).filter (fun e => owner B e = k), f e) = f (sharpIndex B k) := by
  rw [Finset.sum_filter, sharpSet_sum]
  simp only [owner_sharp]
  simp [Finset.mem_range.mpr hk]

noncomputable def batchRaw (B k : ℕ) : ℕ →₀ ℝ :=
  (1 / (B : ℝ)) • ∑ h ∈ Finset.range B, Finsupp.single (queryIndex B k h) 1

lemma batchRaw_nonneg (B k q : ℕ) : 0 ≤ batchRaw B k q := by
  simp only [batchRaw, Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro h _
  exact Finsupp.single_nonneg.mpr (by norm_num) q

lemma batchRaw_le (B k q : ℕ) : batchRaw B k q ≤ 1 / (B : ℝ) := by
  have hh := weighted_single_sum_le (Finset.range B) (queryIndex B k) (fun _ => 1 / (B : ℝ))
    (1 / (B : ℝ)) q (by positivity)
    (by intro i _ j _ he; dsimp [queryIndex] at he; omega) (by intro _ _; exact le_rfl)
  simpa only [batchRaw, Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply, Finset.mul_sum] using hh

lemma batchRaw_outside (B k q : ℕ) (hq : q ∉ (Finset.range B).image (queryIndex B k)) : batchRaw B k q = 0 := by
  simp only [batchRaw, Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
  suffices (∑ h ∈ Finset.range B, Finsupp.single (queryIndex B k h) (1 : ℝ) q) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro h hh
  have he : queryIndex B k h ≠ q := fun he => hq (Finset.mem_image.mpr ⟨h, hh, he⟩)
  simp [he]

lemma batchRaw_mass (B k : ℕ) (hB : 0 < B) : coefficientMass (batchRaw B k) = 1 := by
  simp only [batchRaw, map_smul, map_sum, coefficientMass_single]
  simp [smul_eq_mul, ne_of_gt hB]

lemma family_symbolic (worker : ℕ → ℕ) (K B : ℕ) (t : Tuning) :
    ((minibatchFamily worker).instantiate K B t).symbolic = codeSymbolic t (iteratePrefix worker K B).2 := rfl

lemma family_main (worker : ℕ → ℕ) (K B j : ℕ) (η : ℝ) (hj : j ≤ K) :
    (((minibatchFamily worker).instantiate K B (canonicalTuning η B)).symbolic.points (mainIndex B j)) =
      mainValue worker B η j := iteratePrefix_old worker K B j _ hj

lemma family_output (worker : ℕ → ℕ) (K B : ℕ) (t : Tuning) (hK : 0 < K) :
    let a := (minibatchFamily worker).instantiate K B t
    a.outputCount + 1 = K ∧ ∀ j, a.outputPoint j = mainIndex B j.val := by
  constructor
  · change K - 1 + 1 = K
    omega
  · intro j
    change (iteratePrefix worker K B).1 j.val = mainIndex B j.val
    exact iteratePrefix_registers worker K B j.val (by have := j.isLt; change j.val < K - 1 + 1 at this; omega)

lemma family_estimator (worker : ℕ → ℕ) (K B k : ℕ) (η : ℝ) (hB : 0 < B) (hk : k < K) :
    let a := (minibatchFamily worker).instantiate K B (canonicalTuning η B)
    (a.symbolic.sharpInputs (sharpIndex B k)).1 = batchRaw B k ∧
      (a.symbolic.sharpInputs (sharpIndex B k)).2 = 0 := by
  dsimp only
  rw [family_symbolic, (iteratePrefix_records worker K B k 0 η hk hB).2]
  simp only [linearValue_fst_smul, linearValue_fst_sum, linearValue_snd_smul, linearValue_snd_sum,
    Finset.sum_const_zero, smul_zero]
  exact ⟨rfl, trivial⟩

lemma family_transport_zero (worker : ℕ → ℕ) (K B k t : ℕ) (η : ℝ)
    (hB : 0 < B) (hk : k < K) :
    transportCoefficient ((minibatchFamily worker).instantiate K B (canonicalTuning η B))
      (mainIndex B) (owner B) η (sharpIndex B k) t = 0 := by
  unfold transportCoefficient
  rw [owner_sharp, family_main worker K B k η hk.le]
  apply Finset.sum_eq_zero
  intro q _
  rw [(family_estimator worker K B k η hB hk).1]
  by_cases hq : q ∈ (Finset.range B).image (queryIndex B k)
  · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hq
    rw [family_symbolic, (iteratePrefix_records worker K B k h η hk (Finset.mem_range.mp hh)).1]
    simp
  · rw [batchRaw_outside B k q hq]
    simp

noncomputable def familyCertificate (worker : ℕ → ℕ) (K B : ℕ) (η : ℝ)
    (hK : 0 < K) (hB : 0 < B) :
    ProgramCertificate ((minibatchFamily worker).instantiate K B (canonicalTuning η B)) K η 0 (1 / (B : ℝ)) := by
  let a := (minibatchFamily worker).instantiate K B (canonicalTuning η B)
  have hsets := iteratePrefix_sets worker K B η
  have hsh : a.symbolic.sharps = sharpSet B K := hsets.2.1
  have hmain : ∀ j ≤ K, a.symbolic.points (mainIndex B j) = mainValue worker B η j :=
    fun j hj => family_main worker K B j η hj
  have hest : ∀ e ∈ a.symbolic.sharps, (a.symbolic.sharpInputs e).2 = 0 ∧
      (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q) = 1 ∧
      (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) ≤ 1 / (B : ℝ) := by
    intro e he
    rw [hsh] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    have hh := family_estimator worker K B k η hB (Finset.mem_range.mp hk)
    have hm : (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs (sharpIndex B k)).1 q) = 1 := by
      rw [family_symbolic, ← codeSymbolic_sharp_mass]
      change coefficientMass (a.symbolic.sharpInputs (sharpIndex B k)).1 = 1
      rw [hh.1, batchRaw_mass B k hB]
    refine ⟨hh.2, hm, ?_⟩
    apply LongTails.Proofs.BirchDelayedCoefficients.coefficient_square_sum_le a.symbolic.queries _ _ ?_ ?_ hm
    · intro q _
      rw [hh.1]
      exact batchRaw_nonneg B k q
    · intro q _
      rw [hh.1]
      exact batchRaw_le B k q
  refine {
    main := mainIndex B
    owner := owner B
    weight := fun _ => 1
    positive_horizon := hK
    sharp_only := hsets.2.2
    estimator_linear := fun e he => (hest e he).1
    estimator_mass := fun e he => (hest e he).2.1
    query_linear := ?_
    main_initial := by simp [mainIndex]
    main_linear := ?_
    weight_nonneg := fun _ _ => by norm_num
    owner_lt := ?_
    partition := ?_
    chain := ?_
    output_count := (family_output worker K B _ hK).1
    output_indices := (family_output worker K B _ hK).2
    transport := ?_
    noise := ?_ }
  · intro q hq
    rw [family_symbolic, hsets.1] at hq
    obtain ⟨k, hk, h, hh, rfl⟩ := by
      simpa only [querySet, Finset.mem_biUnion, Finset.mem_image] using hq
    rw [family_symbolic, (iteratePrefix_records worker K B k h η (Finset.mem_range.mp hk) (Finset.mem_range.mp hh)).1]
    exact mainValue_raw worker B η k
  · intro k hk
    rw [hmain k hk]
    exact mainValue_raw worker B η k
  · intro e he
    rw [hsh] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    rw [owner_sharp]
    exact Finset.mem_range.mp hk
  · intro k hk
    rw [hsh, sharpSet_fiber_sum B K k hk]
  · intro k hk
    rw [hmain (k + 1) (by omega), hmain k hk.le, hsh, sharpSet_fiber_sum B K k hk, mainValue_succ]
    simp only [Prod.snd_add, linearValue_snd_smul, one_smul]
  · intro t _
    rw [hsh, sharpSet_sum]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    rw [family_transport_zero worker K B k t η hB (Finset.mem_range.mp hk), mul_zero]
  · calc
      _ ≤ ∑ e ∈ a.symbolic.sharps, 1 / (B : ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        simpa only [one_mul] using (hest e he).2.2
      _ = _ := by rw [hsh, sharpSet_sum]; simp

lemma minibatchProfile_valid : LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile.Valid := by
  norm_num [StructuralProfile.Valid, LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile]

lemma family_structural (p : Params) (worker : ℕ → ℕ)
    (hw0 : 0 < p.workers) (hw : ∀ k, worker k < p.workers)
    (hp : p.protocol = minibatchFamily worker)
    (hc : p.profile = LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile)
    (hq : p.callCount = LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchCalls) : Structural p := by
  intro K B hK hB η hη
  rw [hc] at hB
  have hB0 : 0 < B := hB
  have ht := LongTails.Proofs.BirchNonEuclideanDeltaCertificate.canonical_valid η B hη.le hB0
  rw [hp, hc, hq]
  refine ⟨minibatchFamily_legal p.workers _ ht worker K B hw0 hw,
    minibatchFamily_calls worker K B _, ?_⟩
  simpa only [LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile,
    zero_mul, zero_add, zero_div, add_zero] using Nonempty.intro (familyCertificate worker K B η hK hB0)

end LongTails.Proofs.BirchNonEuclideanBatchCertificate
