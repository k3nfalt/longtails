import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.CoupledMinimaxInner

open OracleTemplate

variable {E Q R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure State (E : Type*) where
  x : E
  z : E
  v : E

noncomputable def accumulated (L : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * (k + 1) / (4 * L)

noncomputable def weight (L : ℝ) (k : ℕ) : ℝ := (k + 1 : ℝ) / (2 * L)

noncomputable def queryPoint (L : ℝ) (k : ℕ) (s : State E) : E :=
  (accumulated L k / accumulated L (k + 1)) • s.x +
    (weight L k / accumulated L (k + 1)) • s.z

noncomputable def update (P : E → E) (L : ℝ) (center : E) (k : ℕ)
    (s : State E) (g : E) : State E :=
  let v := s.v + weight L k • g
  let z := P (center - v)
  ⟨(accumulated L k / accumulated L (k + 1)) • s.x +
    (weight L k / accumulated L (k + 1)) • z, z, v⟩

noncomputable def initial (center : E) : State E := ⟨center, center, 0⟩

noncomputable def phase (query : E → Q) (grad : R → E) (P : E → E) (L : ℝ)
    (center : E) : (N : ℕ) → ℕ → State E → QueryPlan Q R E N
  | 0, _, s => .done s.x
  | N + 1, k, s => .ask (query (queryPoint L k s))
      (fun r => phase query grad P L center N (k + 1) (update P L center k s (grad r)))

noncomputable def restart (query : E → Q) (grad : R → E) (P : E → E) (L : ℝ)
    (N : ℕ) : (S : ℕ) → E → QueryPlan Q R E (N * S)
  | 0, center => .done center
  | S + 1, center => (phase query grad P L center N 0 (initial center)).bind
      (restart query grad P L N S)

end LongTails.Algorithms.CoupledMinimaxInner
