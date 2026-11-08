import LongTails.Proofs.BirchNonEuclideanTransport
import LongTails.Algorithms.BirchNonEuclideanProfiles

namespace LongTails.Proofs.BirchNonEuclideanDeltaCertificate

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanTransport
open LongTails.Algorithms.BirchNonEuclideanProfiles

lemma deltaFamily_symbolic (H K B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) :
    ((deltaMomentumFamily H dispatch worker).instantiate K B t).symbolic =
      codeSymbolic t (deltaPrefix H dispatch worker K B).2 := rfl

lemma deltaFamily_output (H K B : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning) (hK : 0 < K) :
    let a := (deltaMomentumFamily H dispatch worker).instantiate K B t
    a.outputCount + 1 = K ∧ ∀ j, a.outputPoint j = mainIndex H B j.val := by
  constructor
  · change K - 1 + 1 = K
    omega
  · intro j
    change (deltaPrefix H dispatch worker K B).1.1 j.val = mainIndex H B j.val
    exact (deltaPrefix_registers H dispatch worker K B).1 j.val (by have := j.isLt; change j.val < K - 1 + 1 at this; omega)

lemma deltaFamily_main (workers H K B j : ℕ) (dispatch worker : ℕ → ℕ) (t : Tuning)
    (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) (hj : j ≤ K) :
    (((deltaMomentumFamily H dispatch worker).instantiate K B t).symbolic.points (mainIndex H B j)) =
      mainValue H B dispatch worker t j :=
  (deltaPrefix_old workers H K B j dispatch worker t ht hw0 hw hj).1

lemma deltaFamily_transport (workers H K B k h j u : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hk : k < K) (hh : h < H) :
    transportCoefficient ((deltaMomentumFamily H dispatch worker).instantiate K B (canonicalTuning η B))
      (mainIndex H B) (owner H B) η (sharpIndex H B k h) (sharpIndex H B j u) =
        queryTransport H B K dispatch worker η k h j u := by
  unfold transportCoefficient
  rw [owner_sharp H B k h hh,
    deltaFamily_main workers H K B k dispatch worker (canonicalTuning η B) ht hw0 hw hk.le,
    deltaFamily_symbolic, (deltaPrefix_sets workers H K B dispatch worker (canonicalTuning η B) ht hw0 hw).1]
  rfl

noncomputable def deltaFamilyCertificate (workers H K B R : ℕ) (dispatch worker : ℕ → ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R) (hK : 0 < K) (hH : 0 < H)
    (hB : 2 * H ≤ B) (hη : 0 < η)
    (hlam : 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2)
    (hdelay : 4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1) :
    ProgramCertificate ((deltaMomentumFamily H dispatch worker).instantiate K B (canonicalTuning η B)) K η
      (3 * (R : ℝ) + 2 + 2 * (B : ℝ) / (H : ℝ)) (1 / (B : ℝ)) := by
  let a := (deltaMomentumFamily H dispatch worker).instantiate K B (canonicalTuning η B)
  have hB0 : 0 < B := by omega
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have hsets := deltaPrefix_sets workers H K B dispatch worker (canonicalTuning η B) ht hw0 hw
  have hest := deltaPrefix_estimators workers H K B R dispatch worker η ht hw0 hw hsource hB0 hlam hdelay
  have hsh : a.symbolic.sharps = sharpSet H B K := hsets.2.1
  have hmain : ∀ j ≤ K, a.symbolic.points (mainIndex H B j) = mainValue H B dispatch worker (canonicalTuning η B) j :=
    fun j hj => deltaFamily_main workers H K B j dispatch worker (canonicalTuning η B) ht hw0 hw hj
  refine {
    main := mainIndex H B
    owner := owner H B
    weight := fun _ => 1 / (H : ℝ)
    positive_horizon := hK
    sharp_only := hsets.2.2
    estimator_linear := fun e he => (hest e he).1
    estimator_mass := fun e he => (hest e he).2.1
    query_linear := deltaPrefix_query_linear workers H K B dispatch worker η ht hw0 hw (fun k => (hsource k).1)
    main_initial := by simp [mainIndex]
    main_linear := ?_
    weight_nonneg := fun _ _ => by positivity
    owner_lt := ?_
    partition := ?_
    chain := ?_
    output_count := (deltaFamily_output H K B dispatch worker _ hK).1
    output_indices := (deltaFamily_output H K B dispatch worker _ hK).2
    transport := ?_
    noise := ?_ }
  · intro k hk
    rw [hmain k hk]
    exact mainValue_raw workers H B k dispatch worker η ht hw0 hw (fun k => (hsource k).1)
  · intro e he
    rw [hsh] at he
    obtain ⟨k, hk, h, hh, rfl⟩ := by
      simpa only [sharpSet, packetSharps, Finset.mem_biUnion, Finset.mem_image] using he
    rw [owner_sharp H B k h (Finset.mem_range.mp hh)]
    exact Finset.mem_range.mp hk
  · intro k hk
    rw [hsh, sharpSet_fiber_sum H B K k hk]
    simp [hHr]
  · intro k hk
    rw [hmain (k + 1) (by omega), hmain k hk.le, hsh, sharpSet_fiber_sum H B K k hk,
      (delta_recurrences workers H k B dispatch worker η ht hw0 hw (hsource k).1).1]
    simp only [Prod.snd_add, linearValue_snd_smul, linearValue_snd_sum]
    rw [← Finset.smul_sum, smul_smul, mul_comm η]
  · intro e he
    rw [hsh] at he ⊢
    obtain ⟨j, hj, u, hu, rfl⟩ := by
      simpa only [sharpSet, packetSharps, Finset.mem_biUnion, Finset.mem_image] using he
    rw [sharpSet_sum]
    have heq : (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, (1 / (H : ℝ)) *
        (∑ v ∈ sharpSet H B K, transportCoefficient a (mainIndex H B) (owner H B) η (sharpIndex H B k h) v) *
          transportCoefficient a (mainIndex H B) (owner H B) η (sharpIndex H B k h) (sharpIndex H B j u)) =
        ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, (1 / (H : ℝ)) *
          (∑ l ∈ Finset.range K, ∑ t ∈ Finset.range H, queryTransport H B K dispatch worker η k h l t) *
            queryTransport H B K dispatch worker η k h j u := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro h hh
      rw [sharpSet_sum]
      simp only [a, deltaFamily_transport workers H K B k h _ _ dispatch worker η ht hw0 hw
        (Finset.mem_range.mp hk) (Finset.mem_range.mp hh)]
    rw [heq]
    exact transport_schur workers H B R K j u dispatch worker η ht hw0 hw hsource hH hB hη hlam hdelay
      (Finset.mem_range.mp hj) (Finset.mem_range.mp hu)
  · calc
      _ ≤ ∑ e ∈ a.symbolic.sharps, (1 / (H : ℝ)) * (1 / (B : ℝ)) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hest e he).2.2 (by positivity)
      _ = _ := by
        rw [hsh, sharpSet_sum]
        simp [hHr]

lemma deltaProfile_valid (H R : ℕ) (hH : 0 < H) : (deltaProfile H R).Valid := by
  refine ⟨lt_of_lt_of_le (by omega : 0 < 2 * H) (le_max_left _ _), ?_, ?_, ?_, ?_⟩ <;>
    dsimp [deltaProfile] <;> positivity

lemma canonical_valid (η : ℝ) (B : ℕ) (hη : 0 ≤ η) (hB : 0 < B) :
    (canonicalTuning η B).Valid := by
  refine ⟨fun _ => hη, fun _ => ⟨by dsimp [canonicalTuning]; positivity, ?_⟩⟩
  change 1 / (B : ℝ) ≤ 1
  exact (div_le_one (by exact_mod_cast hB)).2 (by exact_mod_cast hB)

lemma deltaProfile_conditions (H R B : ℕ) (hH : 0 < H) (hB : (deltaProfile H R).minimumBatch ≤ B) :
    2 * H ≤ B ∧ 1 - (1 - 1 / (B : ℝ)) ^ H ≤ 1 / 2 ∧
      4 * (1 - (1 - 1 / (B : ℝ)) ^ H) * (R : ℝ) ≤ 1 := by
  have hb := max_le_iff.mp hB
  have hB0 : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hhalf : (H : ℝ) * (1 / (B : ℝ)) ≤ 1 / 2 := by
    have h := (show (2 : ℝ) * H ≤ B by exact_mod_cast hb.1)
    rw [mul_one_div]
    apply (div_le_iff₀ hBr).2
    linarith
  have hema := LongTails.Proofs.BirchDelayedCoefficients.ema_block_bounds (1 / (B : ℝ)) H
    (by positivity) ((div_le_one hBr).2 (by exact_mod_cast hB0)) hhalf
  refine ⟨hb.1, hema.2.trans hhalf, ?_⟩
  calc
    _ ≤ 4 * ((H : ℝ) * (1 / (B : ℝ))) * R := by gcongr; exact hema.2
    _ ≤ 1 := by
      have hr : (4 : ℝ) * H * R ≤ B := by exact_mod_cast hb.2
      have he : 4 * ((H : ℝ) * (1 / (B : ℝ))) * R = (4 * H * R) / B := by ring
      rw [he]
      exact (div_le_one hBr).2 hr

lemma deltaFamily_structural (p : Params) (H R : ℕ) (dispatch worker : ℕ → ℕ)
    (hH : 0 < H) (hw0 : 0 < p.workers) (hw : ∀ k, worker k < p.workers)
    (hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R)
    (hp : p.protocol = deltaMomentumFamily H dispatch worker)
    (hc : p.profile = deltaProfile H R) (hq : p.callCount = deltaCalls H) : Structural p := by
  intro K B hK hB η hη
  rw [hc] at hB
  have hconds := deltaProfile_conditions H R B hH hB
  have hB0 : 0 < B := by omega
  have ht := canonical_valid η B hη.le hB0
  rw [hp, hc, hq]
  refine ⟨deltaFamily_legal p.workers H K B dispatch worker _ ht hw0 hw,
    deltaFamily_calls H dispatch worker K B _, ?_⟩
  have hcert := deltaFamilyCertificate p.workers H K B R dispatch worker η ht hw0 hw hsource hK hH
    hconds.1 hη hconds.2.1 hconds.2.2
  simpa only [deltaProfile, zero_div, add_zero, div_mul_eq_mul_div] using Nonempty.intro hcert

end LongTails.Proofs.BirchNonEuclideanDeltaCertificate
