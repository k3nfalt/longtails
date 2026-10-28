import LongTails.Template
import outputs.Algorithms.FreyaRandomness

open scoped NNReal

namespace outputs.Algorithms.FreyaCollectors

open outputs.Proofs.FreyaModel outputs.Algorithms.FreyaRandomness

structure FullState (d m n : ℕ) where
  original : List (Fin m)
  remaining : List ℕ
  point : Space d
  sum : Space d
  pending : Fin n → Option (Job d m)
  clock : ℝ≥0
  rows : ℕ → ChoiceRow
  nextID : ℕ

structure DifferenceState (d m n : ℕ) where
  target : ℕ
  count : ℕ
  x : Space d
  y : Space d
  sum : Space d
  pending : Fin n → Option (Job d m)
  clock : ℝ≥0
  rows : ℕ → ChoiceRow
  nextID : ℕ

def dispatch {d m : ℕ} (kind : JobKind d) (clock : ℝ≥0) (id : ℕ)
    (component : Option (Fin m)) : Option (Job d m) :=
  component.map fun i => ⟨i, kind, clock, id⟩

def selectedLabel {m : ℕ} (original : List (Fin m)) (remaining : List ℕ)
    (row : ChoiceRow) : Option (Fin m) :=
  (chooseRemaining row remaining).bind fun j => original[j]?

noncomputable def pendingRequest {d m n : ℕ} (clock : ℝ≥0)
    (pending : Fin n → Option (Job d m)) : Option (Request d m n) := by
  classical
  exact if ∃ i, pending i ≠ none then some ⟨clock, pending⟩ else none

def fullInitial {d m : ℕ} (n : ℕ) (labels : List (Fin m)) (x : Space d)
    (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ := 0) : FullState d m n where
  original := labels
  remaining := List.range labels.length
  point := x
  sum := 0
  pending := fun i => dispatch (Sum.inl x) clock (firstID + i.val)
    (selectedLabel labels (List.range labels.length) (rows (firstID + i.val)))
  clock := clock
  rows := rows
  nextID := firstID + n

noncomputable def fullUpdate {d m n : ℕ} (s : FullState d m n) (reply : Reply d n) :
    FullState d m n := by
  classical
  exact if s.remaining.isEmpty then s else
    match reply with
    | none => s
    | some (i, id, c, value) =>
      match s.pending i with
      | none => s
      | some job =>
        if id = job.id ∧ s.clock ≤ c then
          let found := s.remaining.find? fun a => decide (s.original[a]? = some job.component)
          let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
          let sum := if found.isSome then s.sum + value else s.sum
          let next := dispatch (Sum.inl s.point) c s.nextID
            (selectedLabel s.original remaining (s.rows s.nextID))
          { s with
            remaining := remaining
            sum := sum
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID + 1 }
        else s

noncomputable def fullResult {d m n : ℕ} (s : FullState d m n) : Space d :=
  (s.original.length : ℝ)⁻¹ • s.sum

def differenceInitial {d m : ℕ} (n S : ℕ) (x y : Space d) (clock : ℝ≥0)
    (rows : ℕ → ChoiceRow) (firstID : ℕ := 0) : DifferenceState d m n where
  target := S
  count := 0
  x := x
  y := y
  sum := 0
  pending := fun i => if S = 0 then none else
    dispatch (Sum.inr (x, y)) clock (firstID + i.val) (labelAt (rows (firstID + i.val)) m)
  clock := clock
  rows := rows
  nextID := firstID + n

noncomputable def differenceUpdate {d m n : ℕ} (s : DifferenceState d m n)
    (reply : Reply d n) : DifferenceState d m n := by
  classical
  exact if s.target ≤ s.count then s else
    match reply with
    | none => s
    | some (i, id, c, value) =>
      match s.pending i with
      | none => s
      | some job =>
        if id = job.id ∧ s.clock ≤ c then
          let next := dispatch (Sum.inr (s.x, s.y)) c s.nextID (labelAt (s.rows s.nextID) m)
          { s with
            count := s.count + 1
            sum := s.sum + value
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID + 1 }
        else s

noncomputable def differenceResult {d m n : ℕ} (s : DifferenceState d m n) : Space d :=
  (s.target : ℝ)⁻¹ • s.sum

end outputs.Algorithms.FreyaCollectors
