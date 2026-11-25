import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate

noncomputable def nonconvexPLSmoothedAgda {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (r τx τy β : ℝ) (n : ℕ)
    (x0 : E) (y0 : F) : Algorithm (E × F) (E × F) E where
  Seed := Fin (n + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (n + 1))).toMeasure, inferInstance⟩
  State := Fin (n + 1) × ℕ × E × F × E × E
  initial j := (j, 0, x0, y0, x0, x0)
  query s := (0, (s.2.2.1, s.2.2.2.1))
  update s reply :=
    if s.2.1 % 2 = 0 then
      (s.1, s.2.1 + 1, s.2.2.1 - τx • (reply.1 + r • (s.2.2.1 - s.2.2.2.2.1)), s.2.2.2.1,
        s.2.2.2.2.1, s.2.2.2.2.2)
    else
      (s.1, s.2.1 + 1, s.2.2.1, s.2.2.2.1 + τy • reply.2,
        s.2.2.2.2.1 + β • (s.2.2.1 - s.2.2.2.2.1),
        if (s.2.1 + 1) / 2 = (s.1 : ℕ) then s.2.2.2.2.1 + β • (s.2.2.1 - s.2.2.2.2.1)
        else s.2.2.2.2.2)
  output s := s.2.2.2.2.2

end OracleTemplate
