import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.AbcSgd

open OracleTemplate MeasureTheory

noncomputable def sampledSgd {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (K : ℕ) (x0 : E) : Algorithm E E E where
  Seed := Fin (K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (K + 1))).toMeasure, inferInstance⟩
  State := Fin (K + 1) × ℕ × E × E
  initial k := (k, 0, x0, x0)
  query s := (0, s.2.2.1)
  update s g := (s.1, s.2.1 + 1, s.2.2.1 - η • g, if s.2.1 = s.1.val then s.2.2.1 else s.2.2.2)
  output s := s.2.2.2

end LongTails.Algorithms.AbcSgd
