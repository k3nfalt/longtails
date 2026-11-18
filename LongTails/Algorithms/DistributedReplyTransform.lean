import LongTails.Setups.StarNetwork

namespace LongTails.Algorithms.DistributedReplyTransform

open MeasureTheory DistributedTemplate LongTails.Setups.StarNetwork

variable {X Y Z Output : Type} {n : ℕ}

abbrev Protocol (X Y Output : Type) (n : ℕ) :=
  Algorithm (ComputeQuery X) (ComputeReply X Y) (CommReply n) Output (n + 1)

def event (transform : Fin (n + 1) → ℕ → X → Y → Z) (v : Fin (n + 1)) (k : ℕ) :
    Event (ComputeReply X Y) (CommReply n) → Event (ComputeReply X Z) (CommReply n)
  | .computed (.computed x y) => .computed (.computed x (transform v k x y))
  | .received r => .received r
  | .wake => .wake

def nextCount (k : ℕ) : Event (ComputeReply X Y) (CommReply n) → ℕ
  | .computed _ => k + 1
  | _ => k

noncomputable def algorithm (A : Protocol X Z Output n) (seed : A.Seed)
    (transform : Fin (n + 1) → ℕ → X → Y → Z) : Protocol X Y Output n where
  clock := A.clock
  timer := A.timer
  State := A.State × ℕ
  root := A.root
  initial v _ := (A.initial v seed, 0)
  update v s t e := (A.update v s.1 t (event transform v s.2 e), nextCount s.2 e)
  query v s t := let (act, next) := A.query v s.1 t; (act, (next, s.2))
  output s := A.output s.1

end LongTails.Algorithms.DistributedReplyTransform
