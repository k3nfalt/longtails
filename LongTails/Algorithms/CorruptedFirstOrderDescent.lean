import LongTails.Setups.CorruptedFirstOrderNonconvex

open OracleTemplate LongTails.Setups.CorruptedFirstOrderNonconvex

namespace LongTails.Algorithms.CorruptedFirstOrderDescent

inductive State (X : Type)
  | sample (values : List ℝ)
  | walk (anchor : ℝ) (parents : List X) (point : X) (votes : ℕ)
  | done (point : X)

noncomputable def startingBound (values : List ℝ) (k : ℕ) (η : ℝ) : ℝ := by
  classical
  exact sInf {t : ℝ | k < (values.filter (· ≤ t)).length} + 2 * η

def output (p : Params) : State (Space p.d) → Space p.d
  | .sample _ => p.x0
  | .walk _ _ x _ | .done x => x

noncomputable def advance (p : Params) (s : State (Space p.d)) (r : ℝ × Space p.d) :
    State (Space p.d) := by
  classical
  exact match s with
  | .done x => .done x
  | .sample vs =>
    let vs' := r.1 :: vs
    if vs'.length < 2 * p.k + 1 then .sample vs'
    else .walk (startingBound vs' p.k (p.ε ^ 2 / (128 * p.L))) [] p.x0 0
  | .walk a ps x v =>
    if v = 0 ∧ a - (ps.length : ℝ) * (p.ε ^ 2 / (16 * p.L)) < r.1 then
      match ps with
      | [] => .walk a [] x 0
      | y :: ys => .walk a ys y 0
    else if ‖r.2‖ ≤ (3 * p.ε / 4) then
      if p.k ≤ v then .done x else .walk a ps x (v + 1)
    else if 0 < v then .walk a ps x (v - 1)
    else .walk a (x :: ps) (x - (1 / p.L) • r.2) 0

noncomputable def algorithm (p : Params) :
    Algorithm (Space p.d) (ℝ × Space p.d) (Space p.d) where
  State := State (Space p.d)
  initial := fun _ => .sample []
  query := fun s => (0, output p s)
  update := advance p
  output := output p

end LongTails.Algorithms.CorruptedFirstOrderDescent
