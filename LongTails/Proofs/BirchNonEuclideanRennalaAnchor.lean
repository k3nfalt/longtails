import LongTails.Proofs.BirchNonEuclideanRennalaRecords
import LongTails.Proofs.BirchNonEuclideanExtensions

namespace LongTails.Proofs.BirchNonEuclideanRennalaAnchor

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaCapture
open LongTails.Proofs.BirchNonEuclideanRennalaRecords
open LongTails.Proofs.BirchNonEuclideanRennalaLabels (reply_ready)

structure RawRecord (t : Tuning) (s : CodeState) (q x : ℕ) : Prop where
  query : q ∈ (codeSymbolic t s).queries
  vector : (codeSymbolic t s).vectors q = (Finsupp.single q 1, 0)
  point : (codeSymbolic t s).queryPoints q = (codeSymbolic t s).points x

lemma codeExtends_queries (t : Tuning) (s s' : CodeState) (he : CodeExtends s s') :
    (codeSymbolic t s).queries ⊆ (codeSymbolic t s').queries := by
  obtain ⟨tail, ht⟩ := he
  have hh := LongTails.Proofs.BirchNonEuclideanExtensions.symbolic_fold_sets_mono
    (tail.map (InstructionTemplate.instantiate t)) (codeSymbolic t s)
  simpa only [codeSymbolic, codeInstructions, ht, List.map_append, List.foldl_append] using hh.1

lemma RawRecord.mono {t : Tuning} {s s' : CodeState} {q x : ℕ} (hr : RawRecord t s q x)
    (he : CodeExtends s s') (hq : q < (codeSymbolic t s).next) (hx : x < (codeSymbolic t s).next) :
    RawRecord t s' q x := by
  have hqr := codeExtends_symbolic t s s' he q hq
  have hxr := codeExtends_symbolic t s s' he x hx
  exact ⟨codeExtends_queries t s s' he hr.query, hqr.2.1.trans hr.vector,
    hqr.2.2.1.trans (hr.point.trans hxr.1.symm)⟩

def ReadyAnchored {m : ℕ} (t : Tuning) (pub : State m) (regs : Registers m) (s : CodeState) : Prop :=
  ∀ w ∈ pub.ready, RawRecord t s (regs.reply w) (regs.point w)

lemma eventCode_anchored {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m)
    (s : CodeState) (t : Tuning) (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s)
    (ha : ReadyAnchored t state.1 state.2 s) :
    let z := eventCode K B e state s
    ReadyAnchored t z.1.1 z.1.2 z.2 := by
  have hn := codeValid_symbolic_next (m + 1) t s hv
  have hbound := codeValid_register_bound (m + 1) t s hv
  have hold : ∀ v ∈ state.1.ready,
      RawRecord t (eventCode K B e state s).2 (state.2.reply v) (state.2.point v) := by
    intro v hv
    apply (ha v hv).mono (eventCode_extends K B e state s)
    · rw [← hn]
      exact hbound.2 _ _ (ho.reply v hv)
    · rw [← hn]
      exact hbound.1 _ _ (ho.point v)
  dsimp only
  cases e with
  | query w =>
      intro v hv
      change v ∈ insert w state.1.ready at hv
      by_cases h : v = w
      · subst v
        have hr := query_symbolic (w.val + 1) (state.2.point w) s t hn
        change RawRecord t (emit (.query (w.val + 1) (state.2.point w)) s).2
          (Function.update state.2.reply w s.next w) (state.2.point w)
        rw [Function.update_self]
        refine ⟨?_, hr.1, ?_⟩
        · rw [hr.2.2.1]
          exact Finset.mem_insert_self _ _
        · rw [hr.2.1, hr.2.2.2.2.2]
      · change RawRecord t (eventCode K B (.query w) state s).2
          (Function.update state.2.reply w s.next v) (state.2.point v)
        rw [Function.update_of_ne h]
        exact hold v ((Finset.mem_insert.mp hv).resolve_left h)
  | reply w =>
      intro v hv
      change v ∈ (step K B state.1 (.reply w)).ready at hv
      rw [reply_ready] at hv
      change RawRecord t (eventCode K B (.reply w) state s).2
        ((replyCode K B w state.1 state.2 s).1.reply v)
        ((replyCode K B w state.1 state.2 s).1.point v)
      rw [replyCode_reply, replyCode_point_other K B state.1 state.2 w v s (Finset.mem_erase.mp hv).1]
      exact hold v (Finset.mem_erase.mp hv).2

lemma loop_anchored {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s)
    (ha : ReadyAnchored t state.1 state.2 s) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    ReadyAnchored t z.1.1 z.1.2 z.2 := by
  induction events generalizing state s with
  | nil => exact ha
  | cons e rest ih =>
      have hv' := eventCode_valid K B t ht e state s hv ho he.1
      have ha' := eventCode_anchored K B e state s t hv ho ha
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by
        rw [eventCode_public]
        exact he.2
      rw [state_forIn_cons]
      exact ih _ _ hv'.1 hv'.2.2 ha' hr

lemma eventsStateCode_anchored {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid)
    (events : List (Event m)) (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    ReadyAnchored t z.1.1 z.1.2 z.2 := by
  have hi := initialCode_valid m t
  rw [eventsStateCode_run]
  apply loop_anchored K B t ht events _ _ hi.1 hi.2 _ he
  intro w hw
  exact False.elim (Finset.notMem_empty w hw)

end LongTails.Proofs.BirchNonEuclideanRennalaAnchor
