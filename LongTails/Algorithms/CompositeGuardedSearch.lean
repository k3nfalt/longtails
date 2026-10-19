import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.CompositeGuardedSearch

structure Bracket where
  lower : ℝ
  upper : ℝ

noncomputable def Bracket.midpoint (b : Bracket) : ℝ := (b.lower + b.upper) / 2

noncomputable def advance (b : Bracket) (certified : Bool) (residual : ℝ) : Bracket :=
  if certified = true ∧ residual ≤ 0 then ⟨b.midpoint, b.upper⟩
  else ⟨b.lower, b.midpoint⟩

noncomputable def runBracket (evaluate : ℝ → Bool × ℝ) : ℕ → Bracket → Bracket
  | 0, b => b
  | n + 1, b =>
    let trial := evaluate b.midpoint
    runBracket evaluate n (advance b trial.1 trial.2)

structure AccelerationState (E : Type*) where
  point : E
  momentum : E

noncomputable def acceleratedAdvance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (k : ℕ) (state : AccelerationState E) (z r : E) : AccelerationState E :=
  ⟨z, state.momentum - (((k : ℝ) + 1) / 2) • Ring.inverse B r⟩

end LongTails.Algorithms.CompositeGuardedSearch
