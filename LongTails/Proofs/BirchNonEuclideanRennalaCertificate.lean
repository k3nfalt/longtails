import LongTails.Proofs.BirchNonEuclideanRennalaHistoryLoop
import LongTails.Proofs.BirchNonEuclideanDeltaCertificate

namespace LongTails.Proofs.BirchNonEuclideanRennalaCertificate

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaHistory
open LongTails.Proofs.BirchNonEuclideanRennalaHistoryLoop
open LongTails.Proofs.BirchNonEuclideanRennalaMean

lemma history_sum_sharps {α : Type*} [AddCommMonoid α] {m : ℕ} {η : ℝ} {B K : ℕ}
    {regs : Registers m} {s : CodeState} (hh : History η B K regs s) (f : ℕ → α) :
    (∑ e ∈ (codeSymbolic (canonicalTuning η B) s).sharps, f e) =
      ∑ k ∈ Finset.range K, f (regs.sharps k) := by
  rw [hh.sharps, Finset.sum_image]
  intro j hj k hk he
  have hh' := congrArg regs.owner he
  simpa only [hh.owners j (Finset.mem_range.mp hj), hh.owners k (Finset.mem_range.mp hk)] using hh'

lemma history_fiber_sum {α : Type*} [AddCommMonoid α] {m : ℕ} {η : ℝ} {B K : ℕ}
    {regs : Registers m} {s : CodeState} (hh : History η B K regs s) (k : ℕ) (hk : k < K) (f : ℕ → α) :
    (∑ e ∈ (codeSymbolic (canonicalTuning η B) s).sharps.filter (fun e => regs.owner e = k), f e) =
      f (regs.sharps k) := by
  rw [Finset.sum_filter, history_sum_sharps hh]
  calc
    _ = ∑ j ∈ Finset.range K, if j = k then f (regs.sharps j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hh.owners j (Finset.mem_range.mp hj)]
    _ = _ := by simp [Finset.mem_range.mpr hk]

lemma eventsProgram_symbolic {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning) :
    (eventsProgram K B events t).symbolic = codeSymbolic t (eventsStateCode K B events {}).2 := rfl

lemma eventsProgram_output {m : ℕ} (K B : ℕ) (events : List (Event m)) (t : Tuning) (hK : 0 < K) :
    (eventsProgram K B events t).outputCount + 1 = K ∧
      ∀ j, (eventsProgram K B events t).outputPoint j = (eventsStateCode K B events {}).1.2.points j.val := by
  constructor
  · change K - 1 + 1 = K
    omega
  · intro j
    rfl

noncomputable def completeTraceCertificate {m : ℕ} (K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (events : List (Event m))
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    ProgramCertificate (eventsProgram K B events (canonicalTuning η B)) K η 0 (1 / (B : ℝ)) := by
  let a := eventsProgram K B events (canonicalTuning η B)
  let z := eventsStateCode K B events {}
  have hh : History η B K z.1.2 z.2 := completeTrace_history K B η ht events hK hB he
  have hs : a.symbolic = codeSymbolic (canonicalTuning η B) z.2 := rfl
  have hsh : a.symbolic.sharps = (Finset.range K).image z.1.2.sharps := hh.sharps
  have hest : ∀ e ∈ a.symbolic.sharps, (a.symbolic.sharpInputs e).2 = 0 ∧
      (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q) = 1 ∧
      (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) = 1 / (B : ℝ) := by
    intro e he
    rw [hsh] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hw⟩ := hh.means k (Finset.mem_range.mp hk)
    exact hw.estimator hB
  have htransport : ∀ e ∈ a.symbolic.sharps, ∀ j,
      transportCoefficient a z.1.2.points z.1.2.owner η e j = 0 := by
    intro e he j
    rw [hsh] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    have howner := hh.owners k (Finset.mem_range.mp hk)
    obtain ⟨hw⟩ := hh.means k (Finset.mem_range.mp hk)
    unfold transportCoefficient
    rw [howner]
    exact hw.transport_zero η j
  refine {
    main := z.1.2.points
    owner := z.1.2.owner
    weight := fun _ => 1
    positive_horizon := hK
    sharp_only := hh.units
    estimator_linear := fun e he => (hest e he).1
    estimator_mass := fun e he => (hest e he).2.1
    query_linear := hh.queries_linear
    main_initial := hh.initial
    main_linear := hh.main_linear
    weight_nonneg := fun _ _ => by norm_num
    owner_lt := ?_
    partition := ?_
    chain := ?_
    output_count := (eventsProgram_output K B events _ hK).1
    output_indices := (eventsProgram_output K B events _ hK).2
    transport := ?_
    noise := ?_ }
  · intro e he
    rw [hsh] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    rw [hh.owners k (Finset.mem_range.mp hk)]
    exact Finset.mem_range.mp hk
  · intro k hk
    exact history_fiber_sum hh k hk (fun _ => (1 : ℝ))
  · intro k hk
    rw [hs, history_fiber_sum hh k hk, hh.chain k hk]
    simp only [one_smul, Prod.snd_add, LongTails.Proofs.BirchNonEuclideanDelta.linearValue_snd_smul]
  · intro j _
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro e he
    rw [htransport e he j, mul_zero]
  · apply le_of_eq
    calc
      _ = ∑ e ∈ a.symbolic.sharps, 1 / (B : ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [one_mul, (hest e he).2.2]
      _ = _ := by rw [hs, history_sum_sharps hh]; simp

end LongTails.Proofs.BirchNonEuclideanRennalaCertificate
