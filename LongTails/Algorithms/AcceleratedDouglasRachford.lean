import LongTails.Setups.DouglasRachfordSmoothConvex

namespace OracleTemplate.DouglasRachford

open LongTails.Setups.DouglasRachfordSmoothConvex

structure State (E : Type*) where
  k : ℕ
  u : E
  w : E
  x : Option E
  y : E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def relaxed (lam : ℝ) (w x y : E) : E := w + lam • (y - x)

noncomputable def advanceState (lam : ℝ) (s : State E) (x y : E) : State E :=
  ⟨s.k + 1, relaxed lam s.w x y,
    relaxed lam s.w x y + (((s.k - 2 : ℕ) : ℝ) / ((s.k : ℝ) + 1)) • (relaxed lam s.w x y - s.u), none, y⟩

noncomputable def acceleratedDouglasRachford (p : Public) : Algorithm (Query p) p.E p.E where
  State := State p.E
  initial _ := ⟨1, p.w1, p.w1, none, p.w1⟩
  query s := (0,
    match s.x with
    | none => .proxF s.w
    | some x => .proxG ((2 : ℝ) • x - s.w))
  update s r :=
    match s.x with
    | none => { s with x := some r }
    | some x => advanceState p.lam s x r
  output s := s.y

end OracleTemplate.DouglasRachford
