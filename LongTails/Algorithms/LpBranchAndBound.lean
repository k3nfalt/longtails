import LongTails.Setups.BoundedMixedIntegerLinear

namespace OracleTemplate.BoundedMixedIntegerLinear

open LongTails.Setups.BoundedMixedIntegerLinear

structure SearchState (P : Params) where
  stack : List (Box P)
  incumbent : Option (Solution P)

def BoxNonempty (P : Params) (β : Box P) : Prop := ∀ j, β.1 j ≤ β.2 j

noncomputable def initialStack (P : Params) : List (Box P) :=
  open Classical in if BoxNonempty P (P.lo, P.hi) then [(P.lo, P.hi)] else []

def Improves (P : Params) (incumbent : Option (Solution P)) (v : ℝ) : Prop :=
  ∀ x, incumbent = some x → v < objective P (toPoint P x)

def leftChild (P : Params) (β : Box P) (j : Fin P.p) (t : ℤ) : Box P :=
  (β.1, Function.update β.2 j t)

def rightChild (P : Params) (β : Box P) (j : Fin P.p) (t : ℤ) : Box P :=
  (Function.update β.1 j (t + 1), β.2)

noncomputable def processNode (P : Params) (β : Box P) (rest : List (Box P))
    (incumbent : Option (Solution P)) (x : Point P) : SearchState P :=
  open Classical in
  if ¬ Improves P incumbent (objective P x) then ⟨rest, incumbent⟩
  else if h : ∃ j, Int.fract (x.1 j) ≠ 0 then
    ⟨leftChild P β h.choose ⌊x.1 h.choose⌋ :: rightChild P β h.choose ⌊x.1 h.choose⌋ :: rest,
      incumbent⟩
  else ⟨rest, some (fun j => ⌊x.1 j⌋, x.2)⟩

noncomputable def branchUpdate (P : Params) (s : SearchState P) (r : Option (Point P)) :
    SearchState P :=
  match s.stack, r with
  | [], _ => s
  | _ :: rest, none => ⟨rest, s.incumbent⟩
  | β :: rest, some x => processNode P β rest s.incumbent x

noncomputable def lpBranchAndBound (P : Params) :
    Algorithm (Box P) (Option (Point P)) (Option (Solution P)) where
  State := SearchState P
  initial _ := ⟨initialStack P, none⟩
  query s := (0, s.stack.headD (P.lo, P.hi))
  update := branchUpdate P
  output s := s.incumbent

end OracleTemplate.BoundedMixedIntegerLinear
