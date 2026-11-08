import LongTails.Proofs.BirchNonEuclideanRennalaAnchor
import LongTails.Proofs.BirchNonEuclideanRennalaBatch

namespace LongTails.Proofs.BirchNonEuclideanRennalaBatchAnchor

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaCapture
open LongTails.Proofs.BirchNonEuclideanRennalaRecords
open LongTails.Proofs.BirchNonEuclideanRennalaAnchor
open LongTails.Proofs.BirchNonEuclideanRennalaBatch

def BatchAnchored {m : ℕ} (t : Tuning) (pub : State m) (regs : Registers m) (s : CodeState) : Prop :=
  ∀ term ∈ regs.terms, RawRecord t s term.2 (regs.points pub.round)

lemma eventCode_batchAnchored {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m)
    (s : CodeState) (t : Tuning) (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s)
    (hc : Captured state.1 state.2) (ha : ReadyAnchored t state.1 state.2 s)
    (hb : BatchAnchored t state.1 state.2 s) (he : e.Enabled state.1) :
    let z := eventCode K B e state s
    BatchAnchored t z.1.1 z.1.2 z.2 := by
  have hn := codeValid_symbolic_next (m + 1) t s hv
  have hbound := codeValid_register_bound (m + 1) t s hv
  have hold : ∀ term ∈ state.2.terms,
      RawRecord t (eventCode K B e state s).2 term.2 (state.2.points state.1.round) := by
    intro term ht
    apply (hb term ht).mono (eventCode_extends K B e state s)
    · rw [← hn]
      exact hbound.2 _ _ (ho.terms term ht)
    · rw [← hn]
      exact hbound.1 _ _ (ho.points state.1.round)
  dsimp only
  cases e with
  | query w => exact hold
  | reply w =>
      have hfresh : fresh state.1 w → RawRecord t (replyCode K B w state.1 state.2 s).2
          (state.2.reply w) (state.2.points state.1.round) := by
        intro hf
        have hh := (ha w he.2).mono (replyCode_extends K B w state.1 state.2 s)
          (by rw [← hn]; exact hbound.2 _ _ (ho.reply w he.2))
          (by rw [← hn]; exact hbound.1 _ _ (ho.point w))
        rw [hc w he.1, hf] at hh
        exact hh
      change BatchAnchored t (step K B state.1 (.reply w)) (replyCode K B w state.1 state.2 s).1
        (replyCode K B w state.1 state.2 s).2
      intro term ht
      rw [replyCode_terms] at ht
      by_cases hactive : state.1.round < K
      · by_cases hf : fresh state.1 w
        · by_cases hcommit : commits B state.1 w
          · simp [hactive, hf, hcommit] at ht
          · have hround : (step K B state.1 (.reply w)).round = state.1.round := by
              simp [step, hactive, hcommit]
            rw [hround, replyCode_points_old K B state.1 state.2 w s _ le_rfl]
            simp only [hactive, hf, and_self, ite_true, hcommit, ite_false] at ht
            rcases List.mem_append.mp ht with ht | ht
            · exact hold term ht
            · rw [List.mem_singleton.mp ht]
              exact hfresh hf
        · have hcommit : ¬commits B state.1 w := fun hh => hf hh.1
          have hround : (step K B state.1 (.reply w)).round = state.1.round := by
            simp [step, hactive, hcommit]
          rw [hround, replyCode_points_old K B state.1 state.2 w s _ le_rfl]
          simp only [hf, and_false, ite_false] at ht
          exact hold term ht
      · have hround : (step K B state.1 (.reply w)).round = state.1.round := by
          simp [step, hactive]
        rw [hround, replyCode_points_old K B state.1 state.2 w s _ le_rfl]
        simp only [hactive, false_and, ite_false] at ht
        exact hold term ht

lemma loop_batchAnchored {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hv : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s) (hi : Invariant K B state.1)
    (hc : Captured state.1 state.2) (ha : ReadyAnchored t state.1 state.2 s)
    (hb : BatchAnchored t state.1 state.2 s) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    BatchAnchored t z.1.1 z.1.2 z.2 := by
  induction events generalizing state s with
  | nil => exact hb
  | cons e rest ih =>
      have hv' := eventCode_valid K B t ht e state s hv ho he.1
      have hc' := eventCode_captured K B e state s hi hc
      have ha' := eventCode_anchored K B e state s t hv ho ha
      have hb' := eventCode_batchAnchored K B e state s t hv ho hc ha hb he.1
      have hi' : Invariant K B (eventCode K B e state s).1.1 := by
        rw [eventCode_public]
        exact step_invariant K B state.1 e hi he.1
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by
        rw [eventCode_public]
        exact he.2
      rw [state_forIn_cons]
      exact ih _ _ hv'.1 hv'.2.2 hi' hc' ha' hb' hr

lemma eventsStateCode_batchAnchored {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid)
    (events : List (Event m)) (hK : 0 < K) (hB : 0 < B) (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    BatchAnchored t z.1.1 z.1.2 z.2 := by
  have hi := initialCode_valid m t
  rw [eventsStateCode_run]
  apply loop_batchAnchored K B t ht events _ _ hi.1 hi.2 (invariant_initial K B hK hB) _ _ _ he
  · intro w _
    rw [initialCode_run]
  · intro w hw
    exact False.elim (Finset.notMem_empty w hw)
  · intro term ht
    rw [initialCode_run] at ht
    exact False.elim (List.not_mem_nil ht)

end LongTails.Proofs.BirchNonEuclideanRennalaBatchAnchor
