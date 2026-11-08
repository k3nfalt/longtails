import LongTails.Proofs.BirchCollectionLegality
import LongTails.Proofs.BirchRetainedSampling

namespace LongTails.Proofs.BirchCollectionSampling

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchNonEuclideanExecution (queryCount)

abbrev CollectionOrdering := LongTails.Setups.BirchCollections.Ordering

def RawChronology (s : TraceState) (r : Registers)
    (code : List LongTails.Setups.BirchNonEuclidean.Instruction) : Prop :=
  ∀ q, q < s.nextRaw → queryCount (code.take (r.raw q - 1)) = q

lemma rawChronology_step (τ : ℝ) (c : Compilation) (e : Event)
    (hb : RegisterBounds c.trace c.registers)
    (hn : c.registers.next = c.code.length + 1)
    (hc : queryCount c.code = c.trace.nextRaw)
    (h : RawChronology c.trace c.registers c.code) :
    RawChronology (compileStep τ c e).trace (compileStep τ c e).registers
      (compileStep τ c e).code := by
  intro q hq
  by_cases hold : q < c.trace.nextRaw
  · simp only [compileStep]
    rw [registerStep_old_raw τ c.trace c.registers e q hold]
    have hbound : c.registers.raw q - 1 ≤ c.code.length := by
      have hh := hb.2.2.1 q hold
      omega
    rw [List.take_append_of_le_length hbound]
    exact h q hold
  · cases e <;> simp only [compileStep, step] at hq ⊢
    all_goals try omega
    rename_i collection worker
    have hqe : q = c.trace.nextRaw := by omega
    subst q
    simp only [registerStep, Function.update_self, Nat.add_sub_cancel, eventCode, hn]
    simp only [queryCount, List.take_append, List.map_append, List.sum_append,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.map_take, Nat.add_sub_cancel_left, add_zero,
      LongTails.Setups.BirchNonEuclidean.Instruction.oracleCost]
    rw [List.take_of_length_le (by simp)]
    exact hc

lemma rawChronology_fold (τ : ℝ) (events : List Event) (c : Compilation)
    (hb : RegisterBounds c.trace c.registers)
    (hn : c.registers.next = c.code.length + 1)
    (hc : queryCount c.code = c.trace.nextRaw)
    (h : RawChronology c.trace c.registers c.code) :
    let z := events.foldl (compileStep τ) c
    RawChronology z.trace z.registers z.code := by
  induction events generalizing c with
  | nil => exact h
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · exact registerBounds_step τ c.trace c.registers e hb
      · simp only [compileStep, registerStep_next, List.length_append, hn]
        omega
      · simp only [compileStep, step_raw]
        simp only [queryCount, List.map_append, List.sum_append]
        change queryCount c.code + queryCount (eventCode τ c.trace c.registers e) = _
        rw [hc, eventCode_calls]
      · exact rawChronology_step τ c e hb hn hc h

lemma rawChronology_compile (τ : ℝ) (events : List Event) :
    let z := compile τ events
    RawChronology z.trace z.registers z.code :=
  rawChronology_fold τ events {} registerBounds_initial rfl rfl (by simp [RawChronology])

def instructionRaw (o : CollectionOrdering) (s : TraceState) (r : Registers) (n : ℕ) : Finset ℕ :=
  (o.raw s n).image r.raw

lemma instructionRaw_card (o : CollectionOrdering) (s : TraceState) (r : Registers) (K : ℕ)
    (hl : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K)
    (hi : LabelInjective s r) (n : ℕ) (hn : n < o.labels.length) :
    (instructionRaw o s r n).card = (o.raw s n).card := by
  apply card_image_of_injOn
  exact hi.raw.mono (ordering_raw_subset s o K hl hc ho n hn)

lemma instructionRaw_subset (o : CollectionOrdering) (s : TraceState) (r : Registers)
    (m : LongTails.Setups.BirchNonEuclidean.SymbolicMemory) (K : ℕ)
    (hl : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K)
    (hs : LabelSets s r m) (n : ℕ) (hn : n < o.labels.length) :
    instructionRaw o s r n ⊆ m.queries := by
  rw [hs.queries]
  exact image_subset_image (ordering_raw_subset s o K hl hc ho n hn)

lemma instructionRaw_disjoint (o : CollectionOrdering) (s : TraceState) (r : Registers) (K : ℕ)
    (hl : RawLedger s) (hc : CompletedLedger s) (ho : o.Valid s K)
    (hi : LabelInjective s r) :
    ((range o.labels.length : Finset ℕ) : Set ℕ).PairwiseDisjoint (instructionRaw o s r) := by
  intro i hiN j hjN hij
  apply disjoint_left.mpr
  intro q hqi hqj
  obtain ⟨a, ha, heqa⟩ := mem_image.mp hqi
  obtain ⟨b, hb, heqb⟩ := mem_image.mp hqj
  have hae := hi.raw
    (ordering_raw_subset s o K hl hc ho i (mem_range.mp hiN) ha)
    (ordering_raw_subset s o K hl hc ho j (mem_range.mp hjN) hb) (heqa.trans heqb.symm)
  subst b
  exact disjoint_left.mp (ordering_raw_disjoint s o K hl hc ho hiN hjN hij) ha hb

lemma instructionRaw_nonempty (o : CollectionOrdering) (s : TraceState) (r : Registers) (K : ℕ)
    (hp : CollectionParameters s) (hc : CompletedLedger s) (ho : o.Valid s K)
    (n : ℕ) (hn : n < o.labels.length) : (instructionRaw o s r n).Nonempty := by
  have hlabel := ho.2.2.2.2.2.2.1 n hn
  have hlen := (direction_parameters s hp hc (o.label n) hlabel).1
  have hne : (s.directions (o.label n)).raw ≠ [] := by
    intro heq
    simp [heq] at hlen
  have hraw : (o.raw s n).Nonempty := by
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨q, List.mem_toFinset.mpr hq⟩
  exact hraw.image r.raw

end LongTails.Proofs.BirchCollectionSampling
