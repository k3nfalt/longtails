import LongTails.Proofs.BirchNonEuclideanUnused
import LongTails.Proofs.BirchNonEuclideanScheduling

namespace LongTails.Proofs.BirchNonEuclideanPhysicalCertificate

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanDeltaCertificate
open LongTails.Proofs.BirchNonEuclideanUnused
open LongTails.Proofs.BirchNonEuclideanScheduling
open LongTails.Proofs.BirchNonEuclideanExtensions

lemma physicalLocalCode_properties {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (η : ℝ)
    (hK : 0 < K) (hm : 0 < m) (ht : (canonicalTuning η B).Valid) (hB : 0 < B)
    (hc : Clean (codeSymbolic (canonicalTuning η B)
      (deltaPrefix H (packetSource (finalSchedule H K B word).accepted)
        (packetWorker (finalSchedule H K B word).accepted) K B).2)) :
    let z := deltaPrefix H (packetSource (finalSchedule H K B word).accepted)
      (packetWorker (finalSchedule H K B word).accepted) K B
    let r := (physicalLocalCode H K B word).run {}
    CodeValid (m + 1) (canonicalTuning η B) r.2 ∧
      Retains (canonicalTuning η B) z.2 r.2 ∧ CodeExtends z.2 r.2 ∧
        Clean (codeSymbolic (canonicalTuning η B) r.2) := by
  let schedule := finalSchedule H K B word
  let dispatch := packetSource schedule.accepted
  let worker := packetWorker schedule.accepted
  let t := canonicalTuning η B
  let z := deltaPrefix H dispatch worker K B
  have hw : ∀ k, worker k < m + 1 := packetWorker_bound schedule.accepted
  have hsource : ∀ k, dispatch k ≤ k := fun k =>
    (packetSource_valid (packetCutoff H B) schedule.accepted
      (scheduleRun_accepted_valid K (packetCutoff H B) word _) k).1
  have hv := deltaPrefix_valid (m + 1) H K B dispatch worker t ht (by omega) hw
  have hregs := deltaPrefix_registers H dispatch worker K B
  have hsrc := ignored_sources H K B word hK hm
  have hbuffer := buffer_mass_direction (m + 1) H B dispatch worker η ht (by omega) hw hsource hB
  have hh := unusedPackets_properties (ignored schedule)
    (fun job => job.worker.val + 1) (fun job => z.1.1 job.source) (fun job => z.1.2 job.source)
    (m + 1) H η B z.2 ht (by omega) hv.1 hc
    (fun job _ => by have := job.worker.isLt; omega)
    (fun job _ => hv.2.1 job.source) (fun job _ => hv.2.2 job.source)
    (fun job hj => by
      change ((codeSymbolic t z.2).points (z.1.1 job.source)).1 = 0
      rw [hregs.1 job.source (hsrc job hj).le,
        (deltaPrefix_old (m + 1) H K B job.source dispatch worker t ht (by omega) hw (hsrc job hj).le).1]
      exact mainValue_raw (m + 1) H B job.source dispatch worker η ht (by omega) hw hsource)
    (fun job hj => by
      change ((codeSymbolic t z.2).vectors (z.1.2 job.source)).2 = 0
      rw [hregs.2 job.source (hsrc job hj).le,
        (deltaPrefix_old (m + 1) H K B job.source dispatch worker t ht (by omega) hw (hsrc job hj).le).2]
      exact (hbuffer job.source).2)
    (fun job hj => by
      change coefficientMass ((codeSymbolic t z.2).vectors (z.1.2 job.source)).1 = 1
      rw [hregs.2 job.source (hsrc job hj).le,
        (deltaPrefix_old (m + 1) H K B job.source dispatch worker t ht (by omega) hw (hsrc job hj).le).2]
      exact (hbuffer job.source).1)
  rw [physicalLocalCode_run]
  exact hh

noncomputable def certificateDriftMono {a : Program} {K : ℕ} {η D D' V : ℝ}
    (C : ProgramCertificate a K η D V) (hD : 0 ≤ D) (hDD : D ≤ D') :
    ProgramCertificate a K η D' V := by
  refine { C with transport := ?_ }
  intro t ht
  exact (C.transport t ht).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hD (hD.trans hDD)).2 hDD) (C.weight_nonneg t ht))

lemma physicalLocalFamily_output {m : ℕ} (H K B : ℕ) (word : ℕ → ℕ → ℕ → Fin m)
    (t : Tuning) (hK : 0 < K) :
    let a := (physicalLocalFamily H word).instantiate K B t
    a.outputCount + 1 = K ∧ ∀ j, a.outputPoint j = mainIndex H B j.val := by
  constructor
  · change K - 1 + 1 = K
    omega
  · intro j
    change ((physicalLocalCode H K B (word K B)).run {}).1 j.val = mainIndex H B j.val
    rw [physicalLocalCode_points]
    exact (deltaPrefix_registers H _ _ K B).1 j.val (by
      have hj := j.isLt
      change j.val < K - 1 + 1 at hj
      omega)

lemma physicalLocalFamily_extensionData {m : ℕ} (H K B : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (η : ℝ) (hK : 0 < K) (hm : 0 < m)
    (hB0 : 0 < B) (ht : (canonicalTuning η B).Valid)
    (hclean : Clean (codeSymbolic (canonicalTuning η B)
      (deltaPrefix H (packetSource (finalSchedule H K B (word K B)).accepted)
        (packetWorker (finalSchedule H K B (word K B)).accepted) K B).2)) :
    CertificateExtension ((deltaMomentumFamily H
      (packetSource (finalSchedule H K B (word K B)).accepted)
      (packetWorker (finalSchedule H K B (word K B)).accepted)).instantiate K B (canonicalTuning η B))
      ((physicalLocalFamily H word).instantiate K B (canonicalTuning η B)) (mainIndex H B) K := by
  let schedule := finalSchedule H K B (word K B)
  let dispatch := packetSource schedule.accepted
  let worker := packetWorker schedule.accepted
  let t := canonicalTuning η B
  let z := deltaPrefix H dispatch worker K B
  let r := (physicalLocalCode H K B (word K B)).run {}
  let a := (deltaMomentumFamily H dispatch worker).instantiate K B t
  let b := (physicalLocalFamily H word).instantiate K B t
  have hw : ∀ k, worker k < m + 1 := packetWorker_bound schedule.accepted
  have hp := physicalLocalCode_properties H K B (word K B) η hK hm ht hB0 hclean
  have hv := deltaPrefix_valid (m + 1) H K B dispatch worker t ht (by omega) hw
  have hmain : ∀ k ≤ K, mainIndex H B k < (codeSymbolic t z.2).next := by
    intro k hk
    rw [← codeValid_symbolic_next (m + 1) t z.2 hv.1, deltaPrefix_next]
    exact mainIndex_lt H B k K hk
  obtain ⟨hoc, hop⟩ := output_agreement a b (mainIndex H B) K
    (deltaFamily_output H K B dispatch worker t hK) (physicalLocalFamily_output H K B word t hK)
  exact clean_append_extension z.2 r.2 t a b (mainIndex H B) K rfl rfl hp.2.2.1 hmain hp.2.2.2 hoc hop

lemma physicalLocalFamily_extension {m : ℕ} (H K B : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (η : ℝ) (hK : 0 < K) (hm : 0 < m)
    (hB0 : 0 < B) (ht : (canonicalTuning η B).Valid) (D V : ℝ)
    (C : ProgramCertificate ((deltaMomentumFamily H
      (packetSource (finalSchedule H K B (word K B)).accepted)
      (packetWorker (finalSchedule H K B (word K B)).accepted)).instantiate K B (canonicalTuning η B)) K η D V)
    (hCm : C.main = mainIndex H B) :
    Nonempty (ProgramCertificate ((physicalLocalFamily H word).instantiate K B (canonicalTuning η B)) K η D V) := by
  have hclean : Clean (codeSymbolic (canonicalTuning η B)
      (deltaPrefix H (packetSource (finalSchedule H K B (word K B)).accepted)
        (packetWorker (finalSchedule H K B (word K B)).accepted) K B).2) := by
    refine ⟨C.sharp_only, C.query_linear, ?_⟩
    intro e he
    refine ⟨C.estimator_linear e he, ?_⟩
    rw [codeSymbolic_sharp_mass]
    exact C.estimator_mass e he
  have E := physicalLocalFamily_extensionData H K B word η hK hm hB0 ht hclean
  rw [← hCm] at E
  exact ⟨extendCertificate C E⟩

lemma physicalLocalFamily_certificate {m : ℕ} (H K B : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (η : ℝ) (hK : 0 < K) (hm : 0 < m)
    (hH : 0 < H) (hB : 8 * H ≤ B) (hη : 0 < η) :
    Nonempty (ProgramCertificate ((physicalLocalFamily H word).instantiate K B (canonicalTuning η B)) K η
      (2 + 3 * (B : ℝ) / (H : ℝ)) (1 / (B : ℝ))) := by
  let schedule := finalSchedule H K B (word K B)
  let dispatch := packetSource schedule.accepted
  let worker := packetWorker schedule.accepted
  let R := packetCutoff H B
  have hB0 : 0 < B := by omega
  have ht := canonical_valid η B hη.le hB0
  have hw : ∀ k, worker k < m + 1 := packetWorker_bound schedule.accepted
  have hsource : ∀ k, dispatch k ≤ k ∧ k - dispatch k ≤ R :=
    packetSource_valid R schedule.accepted (scheduleRun_accepted_valid K R (word K B) _)
  have hcut := packetCutoff_conditions H B hH hB
  have hconds := deltaProfile_conditions H R B hH hcut.1
  let C := deltaFamilyCertificate (m + 1) H K B R dispatch worker η ht (by omega) hw hsource
    hK hH hconds.1 hη hconds.2.1 hconds.2.2
  obtain ⟨E⟩ := physicalLocalFamily_extension H K B word η hK hm hB0 ht _ _ C rfl
  exact ⟨certificateDriftMono E (by positivity) hcut.2⟩

lemma physicalLocalFamily_legal {m : ℕ} (H K B : ℕ) (word : ℕ → ℕ → ℕ → Fin m)
    (t : Tuning) (ht : t.Valid) : ((physicalLocalFamily H word).instantiate K B t).Legal (m + 1) := by
  let schedule := finalSchedule H K B (word K B)
  let dispatch := packetSource schedule.accepted
  let worker := packetWorker schedule.accepted
  let z := deltaPrefix H dispatch worker K B
  let r := (physicalLocalCode H K B (word K B)).run {}
  have hv := deltaPrefix_valid (m + 1) H K B dispatch worker t ht (by omega) (packetWorker_bound _)
  let Inv := fun (_ : Unit) (s : CodeState) => CodeValid (m + 1) t s ∧ Retains t z.2 s
  have hh := state_forIn_invariant
    (fun job (_ : Unit) => unusedPacket (job.worker.val + 1) (z.1.1 job.source) (z.1.2 job.source) H 0)
    (ignored schedule) Inv (fun job _ _ s hs => by
      have hp := unusedPacket_valid (m + 1) (job.worker.val + 1) (z.1.1 job.source) (z.1.2 job.source)
        H 0 t ht s hs.1 (by have := job.worker.isLt; omega) (by omega)
        ((hs.2 0).1 (hv.2.1 job.source)) ((hs.2 0).2 (hv.2.2 job.source))
      exact ⟨hp.1, retains_trans t z.2 s _ hs.2 hp.2⟩) () z.2 ⟨hv.1, retains_refl t z.2⟩
  have hprops : CodeValid (m + 1) t r.2 ∧ Retains t z.2 r.2 := by
    dsimp only [r]
    rw [physicalLocalCode_run]
    exact hh
  refine ⟨hprops.1.2, by change 0 < m + 1; omega, ?_⟩
  intro j
  change r.1 j.val ∈ (codeLayout t r.2).points 0
  have houtput : r.1 = z.1.1 := by dsimp only [r]; rw [physicalLocalCode_run]
  rw [houtput]
  exact (hprops.2 0).1 (hv.2.1 j.val)

lemma physicalLocalProfile_valid (H : ℕ) (hH : 0 < H) : (physicalLocalProfile H).Valid := by
  refine ⟨by dsimp [physicalLocalProfile]; omega, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [physicalLocalProfile] <;> positivity

lemma physicalLocalFamily_structural (p : Params) {m : ℕ} (H : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (hH : 0 < H) (hm : 0 < m)
    (hw : p.workers = m + 1) (hp : p.protocol = physicalLocalFamily H word)
    (hc : p.profile = physicalLocalProfile H) (hq : p.callCount = physicalLocalCalls H word) :
    Structural p := by
  intro K B hK hB η hη
  rw [hc] at hB
  change 8 * H ≤ B at hB
  have hB0 : 0 < B := by omega
  have ht := canonical_valid η B hη.le hB0
  rw [hp, hc, hq, hw]
  refine ⟨physicalLocalFamily_legal H K B word _ ht, physicalLocalFamily_calls H K B word _, ?_⟩
  have C := physicalLocalFamily_certificate H K B word η hK hm hH hB hη
  simpa only [physicalLocalProfile, zero_div, add_zero, div_mul_eq_mul_div] using C

end LongTails.Proofs.BirchNonEuclideanPhysicalCertificate
