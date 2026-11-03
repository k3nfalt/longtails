import LongTails.Setups.HiddenMixedIntegerLinear
import LongTails.Algorithms.LpBranchAndBound

namespace OracleTemplate.HiddenMixedIntegerLinear

open LongTails.Setups LongTails.Setups.HiddenMixedIntegerLinear

abbrev publicData (Q : Public) : BoundedMixedIntegerLinear.Params :=
  ⟨Q.p, Q.q, 0, 0, 0, 0, Q.c, Q.d, Q.lo, Q.hi⟩

abbrev Entry (Q : Public) := Box Q × WithBot ℝ

structure BestBoundState (Q : Public) where
  nodes : List (Entry Q)
  incumbent : Option (Solution Q)

def KeyLE (Q : Public) (e f : Entry Q) : Prop := e.2 ≤ f.2

noncomputable instance (Q : Public) : DecidableRel (KeyLE Q) := fun _ _ => Classical.dec _

noncomputable def insertEntry (Q : Public) (e : Entry Q) (l : List (Entry Q)) : List (Entry Q) :=
  List.orderedInsert (KeyLE Q) e l

noncomputable def keepEntry (Q : Public) (w : Solution Q) (e : Entry Q) : Bool :=
  open Classical in
  decide (e.2 < (BoundedMixedIntegerLinear.objective (publicData Q)
    (BoundedMixedIntegerLinear.toPoint (publicData Q) w) : WithBot ℝ))

noncomputable def bestBoundNode (Q : Public) (β : Box Q) (rest : List (Entry Q))
    (incumbent : Option (Solution Q)) (x : Point Q) : BestBoundState Q :=
  open Classical in
  if ¬ BoundedMixedIntegerLinear.Improves (publicData Q) incumbent
      (BoundedMixedIntegerLinear.objective (publicData Q) x) then ⟨rest, incumbent⟩
  else if h : ∃ j, Int.fract (x.1 j) ≠ 0 then
    ⟨insertEntry Q (BoundedMixedIntegerLinear.leftChild (publicData Q) β h.choose ⌊x.1 h.choose⌋,
        (BoundedMixedIntegerLinear.objective (publicData Q) x : WithBot ℝ))
      (insertEntry Q
        (BoundedMixedIntegerLinear.rightChild (publicData Q) β h.choose ⌊x.1 h.choose⌋,
          (BoundedMixedIntegerLinear.objective (publicData Q) x : WithBot ℝ)) rest), incumbent⟩
  else ⟨rest.filter (keepEntry Q (fun j => ⌊x.1 j⌋, x.2)), some (fun j => ⌊x.1 j⌋, x.2)⟩

noncomputable def bestBoundUpdate (Q : Public) (s : BestBoundState Q) (r : Option (Point Q)) :
    BestBoundState Q :=
  match s.nodes, r with
  | [], _ => s
  | _ :: rest, none => ⟨rest, s.incumbent⟩
  | e :: rest, some x => bestBoundNode Q e.1 rest s.incumbent x

noncomputable def initialNodes (Q : Public) : List (Entry Q) :=
  open Classical in
  if BoundedMixedIntegerLinear.BoxNonempty (publicData Q) (Q.lo, Q.hi) then [((Q.lo, Q.hi), ⊥)]
  else []

noncomputable def bestBoundBranchAndBound (Q : Public) :
    Algorithm (Box Q) (Option (Point Q)) (Option (Solution Q)) where
  State := BestBoundState Q
  initial _ := ⟨initialNodes Q, none⟩
  query s := (0, (s.nodes.headD ((Q.lo, Q.hi), ⊥)).1)
  update := bestBoundUpdate Q
  output s := s.incumbent

end OracleTemplate.HiddenMixedIntegerLinear
