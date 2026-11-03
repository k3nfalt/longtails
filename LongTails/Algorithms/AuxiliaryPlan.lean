import LongTails.Template

namespace LongTails.Algorithms.AuxiliaryPlan

open OracleTemplate

inductive TwoPlan (Q R α : Type) : Type
  | done (value : α) : TwoPlan Q R α
  | ask (i : Fin 2) (query : Q) (next : R → TwoPlan Q R α) : TwoPlan Q R α

namespace TwoPlan

variable {Q R α β : Type}

def andThen : TwoPlan Q R α → (α → TwoPlan Q R β) → TwoPlan Q R β
  | done a, k => k a
  | ask i q next, k => ask i q (fun r => andThen (next r) k)

instance : Monad (TwoPlan Q R) where
  pure := done
  bind := andThen

def call (i : Fin 2) (q : Q) : TwoPlan Q R R := ask i q done

def eval (g : Fin 2 → Q → R) : TwoPlan Q R α → α
  | done a => a
  | ask i q next => eval g (next (g i q))

def calls (g : Fin 2 → Q → R) (j : Fin 2) : TwoPlan Q R α → ℕ
  | done _ => 0
  | ask i q next => (if i = j then 1 else 0) + calls g j (next (g i q))

def step (g : Fin 2 → Q → R) : TwoPlan Q R α → TwoPlan Q R α
  | done a => done a
  | ask i q next => next (g i q)

def index (q0 : Q) : TwoPlan Q R α → Fin 2 × Q
  | done _ => (0, q0)
  | ask i q _ => (i, q)

def advance : TwoPlan Q R α → R → TwoPlan Q R α
  | done a, _ => done a
  | ask _ _ next, r => next r

def result (a0 : α) : TwoPlan Q R α → α
  | done a => a
  | ask _ _ _ => a0

def loop (n : ℕ) (body : β → TwoPlan Q R β) (s : β) : TwoPlan Q R β :=
  match n with
  | 0 => done s
  | n + 1 => andThen (body s) (loop n body)

noncomputable def algorithm (q0 : Q) (a0 : α) (plan : TwoPlan Q R α) : Algorithm Q R α 2 where
  State := TwoPlan Q R α
  initial _ := plan
  query := index q0
  update := advance
  output := result a0

end TwoPlan

end LongTails.Algorithms.AuxiliaryPlan
