import LongTails.Proofs.BirchNonEuclideanSharedSchur
import LongTails.Proofs.BirchNonEuclideanDeltaCertificate

namespace LongTails.Proofs.BirchNonEuclideanSharedCertificate

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanProfiles
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanShared
open LongTails.Proofs.BirchNonEuclideanSharedCoefficients
open LongTails.Proofs.BirchNonEuclideanSharedTransport
open LongTails.Proofs.BirchNonEuclideanSharedSchur
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_snd_smul linearValue_snd_sum)
open LongTails.Proofs.BirchNonEuclideanDeltaCertificate (canonical_valid)

lemma sharedFamily_symbolic (m H K B : ℕ) (t : Tuning) :
    ((sharedMomentumFamily m H).instantiate K B t).symbolic =
      codeSymbolic t (sharedPrefix m H K B).2 := rfl

lemma sharedFamily_output (m H K B : ℕ) (t : Tuning) (hK : 0 < K) :
    let a := (sharedMomentumFamily m H).instantiate K B t
    a.outputCount + 1 = K ∧ ∀ j, a.outputPoint j = mainIndex m H B j.val := by
  constructor
  · change K - 1 + 1 = K
    omega
  · intro j
    change (sharedPrefix m H K B).1.1 j.val = mainIndex m H B j.val
    exact (sharedPrefix_registers m H K B).1 j.val
      (by have := j.isLt; change j.val < K - 1 + 1 at this; omega)

lemma sharedFamily_main (workers m H K B j : ℕ) (t : Tuning)
    (ht : t.Valid) (hw0 : 0 < workers) (hw : m < workers) (hj : j ≤ K) :
    (((sharedMomentumFamily m H).instantiate K B t).symbolic.points (mainIndex m H B j)) =
      mainValue m H B t j :=
  (sharedPrefix_old workers m H K B j t ht hw0 hw hj).1

lemma sharedFamily_transport (workers m H K B k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hk : k < K) (hi : i < m) (hh : h < H) :
    transportCoefficient ((sharedMomentumFamily m H).instantiate K B (canonicalTuning η B))
      (mainIndex m H B) (owner m H B) η (sharpIndex m H B k i h) (sharpIndex m H B j v l) =
        queryTransport m H B K η k i h j v l := by
  unfold transportCoefficient
  rw [owner_sharp m H B k i h hi hh,
    sharedFamily_main workers m H K B k (canonicalTuning η B) ht hw0 hw hk.le,
    sharedFamily_symbolic, (sharedPrefix_sets workers m H K B (canonicalTuning η B) ht hw0 hw).1,
    (sharedPrefix_records workers m H K B k i h η ht hw0 hw hk hi hh).2]
  rfl

noncomputable def sharedFamilyCertificate (workers m H K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hK : 0 < K) (hH : 0 < H) (hB : 2 * H ≤ B) (hη : 0 < η) :
    ProgramCertificate ((sharedMomentumFamily m H).instantiate K B (canonicalTuning η B)) K η
      (2 + 2 * (B : ℝ) / H) (1 / ((m : ℝ) * B) + (H : ℝ) / B ^ 2) := by
  let a := (sharedMomentumFamily m H).instantiate K B (canonicalTuning η B)
  have hB0 : 0 < B := by omega
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hsets := sharedPrefix_sets workers m H K B (canonicalTuning η B) ht hw0 hw
  have hest := sharedPrefix_estimators workers m H K B η ht hw0 hw hm hB0
  have hsh : a.symbolic.sharps = sharpSet m H B K := hsets.2.1
  have hmain : ∀ j ≤ K, a.symbolic.points (mainIndex m H B j) = mainValue m H B (canonicalTuning η B) j :=
    fun j hj => sharedFamily_main workers m H K B j (canonicalTuning η B) ht hw0 hw hj
  refine {
    main := mainIndex m H B
    owner := owner m H B
    weight := fun _ => 1 / ((m : ℝ) * H)
    positive_horizon := hK
    sharp_only := hsets.2.2
    estimator_linear := fun e he => (hest e he).1
    estimator_mass := fun e he => (hest e he).2.1
    query_linear := sharedPrefix_query_linear workers m H K B η ht hw0 hw
    main_initial := by simp [mainIndex]
    main_linear := ?_
    weight_nonneg := fun _ _ => by positivity
    owner_lt := ?_
    partition := ?_
    chain := ?_
    output_count := (sharedFamily_output m H K B _ hK).1
    output_indices := (sharedFamily_output m H K B _ hK).2
    transport := ?_
    noise := ?_ }
  · intro k hk
    rw [hmain k hk]
    exact mainValue_raw workers m H B η ht hw0 hw k
  · intro e he
    rw [hsh] at he
    obtain ⟨k, hk, i, hi, h, hh, rfl⟩ := by
      simpa only [sharpSet, roundSharps, Finset.mem_biUnion, Finset.mem_image] using he
    rw [owner_sharp m H B k i h (Finset.mem_range.mp hi) (Finset.mem_range.mp hh)]
    exact Finset.mem_range.mp hk
  · intro k hk
    rw [hsh, sharpSet_fiber_sum m H B K k hk]
    simp [hmr, hHr]
  · intro k hk
    rw [hmain (k + 1) (by omega), hmain k hk.le, hsh, sharpSet_fiber_sum m H B K k hk,
      (shared_recurrences workers m H k B η ht hw0 hw).1]
    simp only [Prod.snd_add, linearValue_snd_smul, linearValue_snd_sum]
    congr 1
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    ring
  · intro e he
    rw [hsh] at he ⊢
    obtain ⟨j, hj, v, hv, l, hl, rfl⟩ := by
      simpa only [sharpSet, roundSharps, Finset.mem_biUnion, Finset.mem_image] using he
    rw [sharpSet_sum]
    have heq : (∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
        (1 / ((m : ℝ) * H)) *
          (∑ e ∈ sharpSet m H B K, transportCoefficient a (mainIndex m H B) (owner m H B) η (sharpIndex m H B k i h) e) *
            transportCoefficient a (mainIndex m H B) (owner m H B) η (sharpIndex m H B k i h) (sharpIndex m H B j v l)) =
        ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
          (1 / ((m : ℝ) * H)) *
            (∑ r ∈ Finset.range K, ∑ u ∈ Finset.range m, ∑ z ∈ Finset.range H,
              queryTransport m H B K η k i h r u z) * queryTransport m H B K η k i h j v l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro h hh
      rw [sharpSet_sum]
      simp only [a, sharedFamily_transport workers m H K B k i h _ _ _ η ht hw0 hw
        (Finset.mem_range.mp hk) (Finset.mem_range.mp hi) (Finset.mem_range.mp hh)]
    rw [heq]
    exact transport_schur workers m H B K j v l η ht hw0 hw hm hH hB hη
      (Finset.mem_range.mp hj) (Finset.mem_range.mp hv) (Finset.mem_range.mp hl)
  · calc
      _ ≤ ∑ e ∈ a.symbolic.sharps, (1 / ((m : ℝ) * H)) *
          (1 / ((m : ℝ) * B) + (H : ℝ) / B ^ 2) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hest e he).2.2 (by positivity)
      _ = _ := by
        rw [hsh, sharpSet_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

lemma sharedProfile_valid (m H : ℕ) (hm : 0 < m) (hH : 0 < H) : (sharedProfile m H).Valid := by
  refine ⟨by dsimp [sharedProfile]; omega, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [sharedProfile] <;> positivity

lemma sharedFamily_structural (p : Params) (m H : ℕ)
    (hm : 0 < m) (hH : 0 < H) (hw0 : 0 < p.workers) (hw : m < p.workers)
    (hp : p.protocol = sharedMomentumFamily m H)
    (hc : p.profile = sharedProfile m H) (hq : p.callCount = sharedCalls m H) : Structural p := by
  intro K B hK hB η hη
  rw [hc] at hB
  change 2 * H ≤ B at hB
  have hB0 : 0 < B := by omega
  have ht := canonical_valid η B hη.le hB0
  rw [hp, hc, hq]
  refine ⟨sharedFamily_legal p.workers m H K B _ ht hw0 hw,
    sharedFamily_calls m H K B _, ?_⟩
  have hcert := sharedFamilyCertificate p.workers m H K B η ht hw0 hw hm hK hH hB hη
  simpa only [sharedProfile, div_mul_eq_mul_div, div_div] using Nonempty.intro hcert

end LongTails.Proofs.BirchNonEuclideanSharedCertificate
