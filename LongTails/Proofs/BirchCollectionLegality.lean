import LongTails.Proofs.BirchCollectionReplay
import LongTails.Proofs.BirchCollectionOrdering
import LongTails.Proofs.BirchNonEuclideanConstruction

namespace LongTails.Proofs.BirchCollectionLegality

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Setups.BirchNonEuclidean (Layout Instruction LegalFrom)
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchNonEuclideanConstruction (layout_points_mono layout_vectors_mono)

noncomputable def layoutStep (τ : ℝ) (s : TraceState) (r : Registers) (l : Layout) (e : Event) : Layout :=
  (eventCode τ s r e).foldl (fun l i => i.layout l) l

lemma layout_fold_retains (code : List Instruction) (l : Layout) (w : ℕ) :
    l.points w ⊆ (code.foldl (fun l i => i.layout l) l).points w ∧
      l.vectors w ⊆ (code.foldl (fun l i => i.layout l) l).vectors w := by
  induction code generalizing l with
  | nil => exact ⟨fun _ h => h, fun _ h => h⟩
  | cons i rest ih =>
      exact ⟨(layout_points_mono l i w).trans (ih (i.layout l)).1,
        (layout_vectors_mono l i w).trans (ih (i.layout l)).2⟩

lemma layoutStep_next (τ : ℝ) (s : TraceState) (r : Registers) (l : Layout)
    (e : Event) (hn : l.next = r.next) : (layoutStep τ s r l e).next =
      (registerStep τ s r e).next := by
  rw [registerStep_next, layoutStep,
    LongTails.Proofs.BirchNonEuclideanConstruction.layout_length, hn]

structure Ownership (workers : ℕ) (s : TraceState) (r : Registers) (l : Layout) : Prop where
  state : ∀ a, a < s.nextState → (s.states a).owner < workers ∧
    r.point a ∈ l.points (s.states a).owner ∧ r.momentum a ∈ l.vectors (s.states a).owner
  collection : ∀ c, c < s.nextCollection → (s.collections c).owner < workers ∧
    0 ≤ (s.collections c).movement ∧
    r.point (s.collections c).source ∈ l.points (s.collections c).owner ∧
    r.momentum (s.collections c).source ∈ l.vectors (s.collections c).owner
  raw : ∀ q, q < s.nextRaw → (s.raws q).worker < workers ∧
    r.raw q ∈ l.vectors (s.raws q).worker
  delivered : ∀ c, c < s.nextCollection → ∀ q ∈ (s.collections c).delivered,
    r.raw q ∈ l.vectors (s.collections c).owner
  marker : ∀ a ∈ s.markers, r.point a ∈ l.points 0

lemma ownership_initial (workers : ℕ) (hw : 0 < workers) : Ownership workers {} {} {} := by
  constructor <;> simp [hw]

lemma eventCode_legal (τ : ℝ) (workers : ℕ) (s : TraceState) (r : Registers)
    (l : Layout) (e : Event) (hτ : 0 ≤ τ) (hw : 0 < workers) (hn : l.next = r.next)
    (ho : Ownership workers s r l) (hl : RawLedger s) (he : e.Valid workers s) :
    LegalFrom workers l (eventCode τ s r e) := by
  cases e with
  | capture worker source size refresh movement =>
      have hs := ho.state source he.2.1
      simp [eventCode, LegalFrom, Instruction.Legal, Instruction.layout, he.1, hs.1,
        hs.2.1, hs.2.2]
  | issue c worker =>
      have hc := ho.collection c he.1
      simp [eventCode, LegalFrom, Instruction.Legal, Instruction.layout, hc.1, he.2.1, hc.2.2.1]
  | receive q =>
      have hq := ho.raw q he.1
      have hc := ho.collection _ (hl.assignment q he.1)
      simp [eventCode, LegalFrom, Instruction.Legal, hq.1, hq.2, hc.1]
  | finish c =>
      have hc := ho.collection c he.1
      have hd := ho.delivered c he.1
      have ht : 0 ≤ τ * (s.collections c).movement := mul_nonneg hτ hc.2.1
      simp [eventCode, LegalFrom, Instruction.Legal, Instruction.layout, hc.1,
        hc.2.2.1, hc.2.2.2, ht, hn, Nat.add_assoc]
      intro q hq
      exact hd q hq
  | merge worker left right common =>
      have hl := ho.state left he.2.1
      have hr := ho.state right he.2.2.1
      have hc := ho.state common he.2.2.2.1
      simp [eventCode, LegalFrom, Instruction.Legal, Instruction.layout, he.1,
        hl.1, hr.1, hc.1, hl.2.1, hl.2.2,
        hn, Nat.add_assoc, Function.update_apply]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> simp_all
  | mark source =>
      have hs := ho.state source he.1
      simp [eventCode, LegalFrom, Instruction.Legal, hs.1, hs.2.1, hw]
  | discard _ | cancel _ => trivial

lemma ownership_step (τ : ℝ) (workers : ℕ) (s : TraceState) (r : Registers)
    (l : Layout) (e : Event) (hn : l.next = r.next)
    (hh : Histories s) (hl : RawLedger s) (ho : Ownership workers s r l)
    (hm : ∀ a ∈ s.markers, a < s.nextState) (he : e.Valid workers s) :
    Ownership workers (step s e) (registerStep τ s r e) (layoutStep τ s r l e) := by
  have hretain := layout_fold_retains (eventCode τ s r e) l
  have holdowner (c : ℕ) (hc : c < s.nextCollection) :
      ((step s e).collections c).owner = (s.collections c).owner :=
    congrArg Prod.fst (step_old_collection s e c hc)
  have holdmovement (c : ℕ) (hc : c < s.nextCollection) :
      ((step s e).collections c).movement = (s.collections c).movement :=
    congrArg (fun h => h.2.2.2.2) (step_old_collection s e c hc)
  constructor
  · intro a ha
    by_cases hold : a < s.nextState
    · rw [step_old_state s e a hold, (registerStep_old_state τ s r e a hold).1,
        (registerStep_old_state τ s r e a hold).2]
      exact ⟨(ho.state a hold).1, (hretain _).1 (ho.state a hold).2.1,
        (hretain _).2 (ho.state a hold).2.2⟩
    · cases e <;> simp only [step] at ha ⊢
      all_goals try omega
      · rename_i c
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        simp [registerStep, layoutStep, eventCode, Instruction.layout, hn,
          (ho.collection c he.1).1, Nat.add_assoc]
      · rename_i worker left right common
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        simp [registerStep, layoutStep, eventCode, Instruction.layout, hn, he.1, Nat.add_assoc]
  · intro c hc
    by_cases hold : c < s.nextCollection
    · have hs := hh.source c hold
      rw [holdowner c hold, holdmovement c hold, step_old_collection_source s e c hold,
        (registerStep_old_state τ s r e _ hs).1, (registerStep_old_state τ s r e _ hs).2]
      exact ⟨(ho.collection c hold).1, (ho.collection c hold).2.1,
        (hretain _).1 (ho.collection c hold).2.2.1,
        (hretain _).2 (ho.collection c hold).2.2.2⟩
    · cases e <;> simp only [step] at hc ⊢
      all_goals try omega
      rename_i worker source size refresh movement
      have hce : c = s.nextCollection := by omega
      rw [hce, Function.update_self]
      simp [registerStep, layoutStep, eventCode, Instruction.layout, he.1, he.2.2.2.1]
  · intro q hq
    by_cases hold : q < s.nextRaw
    · rw [step_old_raw s e q hold, registerStep_old_raw τ s r e q hold]
      exact ⟨(ho.raw q hold).1, (hretain _).2 (ho.raw q hold).2⟩
    · cases e <;> simp only [step] at hq ⊢
      all_goals try omega
      rename_i c worker
      have hqe : q = s.nextRaw := by omega
      rw [hqe, Function.update_self]
      simp [registerStep, layoutStep, eventCode, Instruction.layout, hn, he.2.1]
  · intro c hc q hq
    by_cases hold : c < s.nextCollection
    · have hprevious (q : ℕ) (hq : q ∈ (s.collections c).delivered) :
          (registerStep τ s r e).raw q ∈ (layoutStep τ s r l e).vectors
            ((step s e).collections c).owner := by
        rw [holdowner c hold, registerStep_old_raw τ s r e q ((hl.delivered c hold).2 q hq).1]
        exact (hretain _).2 (ho.delivered c hold q hq)
      rcases step_delivered s e c hold with hd | ⟨q', heq, hassign, hd⟩
      · rw [hd] at hq
        exact hprevious q hq
      · rw [hd] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hprevious q hq
        · have hqe : q = q' := by simpa using hq
          subst q
          subst e
          rw [holdowner c hold]
          simp [registerStep, layoutStep, eventCode, Instruction.layout, hassign]
    · cases e <;> simp only [step] at hc hq
      all_goals try omega
      have hce : c = s.nextCollection := by omega
      simp [hce] at hq
  · intro a ha
    have hprevious (a : ℕ) (ha : a ∈ s.markers) :
        (registerStep τ s r e).point a ∈ (layoutStep τ s r l e).points 0 := by
      rw [(registerStep_old_state τ s r e a (hm a ha)).1]
      exact (hretain 0).1 (ho.marker a ha)
    cases e with
    | mark source =>
        rcases List.mem_append.mp ha with ha | ha
        · exact hprevious a ha
        · have hae : a = source := by simpa using ha
          simp [hae, registerStep, layoutStep, eventCode, Instruction.layout]
    | _ => exact hprevious a ha

lemma compilation_legal_fold (τ : ℝ) (workers : ℕ) (events : List Event) (c : Compilation)
    (hτ : 0 ≤ τ) (hw : 0 < workers)
    (hn : (LongTails.Setups.BirchNonEuclidean.finalLayout c.code).next = c.registers.next)
    (hh : Histories c.trace) (hl : RawLedger c.trace)
    (ho : Ownership workers c.trace c.registers
      (LongTails.Setups.BirchNonEuclidean.finalLayout c.code))
    (hm : ∀ a ∈ c.trace.markers, a < c.trace.nextState)
    (hc : LegalFrom workers {} c.code) (he : ValidFrom workers c.trace events) :
    let z := events.foldl (compileStep τ) c
    (LongTails.Setups.BirchNonEuclidean.finalLayout z.code).next = z.registers.next ∧
      Ownership workers z.trace z.registers
        (LongTails.Setups.BirchNonEuclidean.finalLayout z.code) ∧
      LegalFrom workers {} z.code := by
  induction events generalizing c with
  | nil => exact ⟨hn, ho, hc⟩
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · simpa only [compileStep, LongTails.Setups.BirchNonEuclidean.finalLayout,
          List.foldl_append, layoutStep] using layoutStep_next τ c.trace c.registers
          (LongTails.Setups.BirchNonEuclidean.finalLayout c.code) e hn
      · exact histories_step workers c.trace e hh he.1
      · exact rawLedger_step workers c.trace e hl he.1
      · simpa only [compileStep, LongTails.Setups.BirchNonEuclidean.finalLayout,
          List.foldl_append, layoutStep] using ownership_step τ workers c.trace c.registers
          (LongTails.Setups.BirchNonEuclidean.finalLayout c.code) e hn hh hl ho hm he.1
      · exact LongTails.Proofs.BirchCollectionOrdering.markers_bound_step
          workers c.trace e he.1 hm
      · rw [compileStep, LongTails.Proofs.BirchNonEuclideanConstruction.legalFrom_append]
        exact ⟨hc, eventCode_legal τ workers c.trace c.registers
          (LongTails.Setups.BirchNonEuclidean.finalLayout c.code) e hτ hw hn ho hl he.1⟩
      · exact he.2

lemma compilation_legal (τ : ℝ) (workers : ℕ) (events : List Event)
    (hτ : 0 ≤ τ) (hw : 0 < workers) (he : ValidFrom workers {} events) :
    let z := compile τ events
    (LongTails.Setups.BirchNonEuclidean.finalLayout z.code).next = z.registers.next ∧
      Ownership workers z.trace z.registers
        (LongTails.Setups.BirchNonEuclidean.finalLayout z.code) ∧
      LegalFrom workers {} z.code :=
  compilation_legal_fold τ workers events {} hτ hw rfl histories_initial rawLedger_initial
    (ownership_initial workers hw) (by simp) trivial he

lemma program_legal (p : Params) (hL : 0 < p.L) (hw : 0 < p.workers)
    (he : ValidFrom p.workers {} p.events)
    (hm : (run p.events).markers.length = horizon p + 1) :
    (program p).Legal p.workers := by
  let c := compile (1 / (20 * p.L)) p.events
  have hτ : 0 ≤ 1 / (20 * p.L) := by positivity
  have hc := compilation_legal (1 / (20 * p.L)) p.workers p.events hτ hw he
  refine ⟨hc.2.2, hw, ?_⟩
  intro j
  have hK : 0 < horizon p := by unfold horizon; omega
  have hbound : j.val < c.trace.markers.length := by
    have hj := j.isLt
    change j.val < horizon p - 1 + 1 at hj
    have hlen : c.trace.markers.length = horizon p + 1 := by
      simpa only [c, compile_trace] using hm
    omega
  have hmem : (c.trace.markers[j.val]?.getD 0) ∈ c.trace.markers := by
    simpa only [List.getElem?_eq_getElem hbound, Option.getD_some] using
      List.getElem_mem hbound
  exact hc.2.1.marker _ hmem

end LongTails.Proofs.BirchCollectionLegality
