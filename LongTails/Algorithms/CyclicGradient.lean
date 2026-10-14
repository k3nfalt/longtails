import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.CyclicInterpolation

def component (m : ℕ) [NeZero m] (t : ℕ) : Fin m := ⟨t % m, Nat.mod_lt _ (NeZero.pos m)⟩

noncomputable def cyclicGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (L : ℝ) (x0 : E) : Algorithm (Fin m × E) E E where
  State := E × ℕ
  initial _ := (x0, 0)
  query s := (0, (component m s.2, s.1))
  update s reply := (s.1 - (1 / L) • reply, s.2 + 1)
  output s := s.1

end OracleTemplate.CyclicInterpolation
