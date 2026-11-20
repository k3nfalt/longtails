import LongTails.Proofs.ContaminatedCalendarBudget

namespace LongTails.Proofs.ContaminatedValidationCalendar

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (height iterations)

abbrev Seed (p : Params) := Fin (confidence p) → Fin (iterations (network p))

lemma indices_length (p : Params) (z : Seed p) :
    (candidateIndices p z).length ≤ min (iterations (network p)) (confidence p) := by
  unfold candidateIndices
  rw [Finset.length_sort]
  split_ifs with h
  · simp [min_eq_left h]
  · apply le_min
    · simpa only [Fintype.card_fin] using Finset.card_le_univ (Finset.univ.image z)
    · simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_image_le (s := Finset.univ) (f := z)

lemma indices_sorted (p : Params) (z : Seed p) : (candidateIndices p z).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ _

lemma draw_mem (p : Params) (z : Seed p) (i : Fin (confidence p)) : z i ∈ candidateIndices p z := by
  unfold candidateIndices
  rw [Finset.mem_sort]
  split_ifs <;> simp

lemma validate_length {N : ℕ} (H) (u) (xs : List (Fin N)) :
    (validationOps H u xs).length = xs.length := by
  induction xs generalizing u with
  | nil => rfl
  | cons j xs ih => simp [validationOps,ih]

lemma validate_precision (p : Params) {N : ℕ} (H) (u) (xs : List (Fin N)) :
    ((validationOps H u xs).map (Operation.precision p)).sum = xs.length*(2*confidence p) := by
  induction xs generalizing u with
  | nil => simp [validationOps]
  | cons j xs ih => simp [validationOps,Operation.precision,ih,Nat.add_mul,Nat.add_comm]

lemma clog_gap (n : ℕ) : Nat.clog 4 (1+n) ≤ n := by
  apply Nat.clog_le_of_le_pow
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

lemma validate_gaps {N : ℕ} (H k : ℕ) (xs : List (Fin N)) (hs : xs.Pairwise (· ≤ ·))
    (hk : ∀ j ∈ xs, k ≤ j.val) :
    ((validationOps H (some k) xs).map Operation.level).sum ≤ N-k := by
  induction xs generalizing k with
  | nil => simp [validationOps]
  | cons j xs ih =>
    obtain ⟨hle,hs⟩ := List.pairwise_cons.mp hs
    have h₀ := hk j List.mem_cons_self
    have h₁ := ih j.val hs (fun a ha => hle a ha)
    have h₂ := clog_gap (j.val-k)
    simp only [validationOps,Option.elim_some,List.map_cons,Operation.level,List.sum_cons]
    omega

lemma validate_width {N : ℕ} (H : ℕ) (xs : List (Fin N)) (hs : xs.Pairwise (· ≤ ·)) :
    ((validationOps H none xs).map Operation.level).sum ≤ H+N := by
  cases xs with
  | nil => simp [validationOps]
  | cons j xs =>
    obtain ⟨hle,hs⟩ := List.pairwise_cons.mp hs
    have hh := validate_gaps H j.val xs hs (fun a ha => hle a ha)
    simp only [validationOps,Option.elim_none,List.map_cons,Operation.level,List.sum_cons]
    omega

end LongTails.Proofs.ContaminatedValidationCalendar
