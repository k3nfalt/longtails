import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate

noncomputable def stochasticSmoothedAgda {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (r τx τy β : ℝ) (n : ℕ) (x0 : E) (y0 : F) :
    Algorithm ((E × F) ⊕ (E × F)) (E ⊕ F) (E × F) where
  Seed := Fin (n + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (n + 1))).toMeasure, inferInstance⟩
  State := Fin (n + 1) × ℕ × E × F × E × (E × F)
  initial j := (j, 0, x0, y0, x0, (x0, y0))
  query s := (0, if s.2.1 % 2 = 0 then Sum.inl (s.2.2.1, s.2.2.2.1) else Sum.inr (s.2.2.1, s.2.2.2.1))
  update s reply :=
    match reply with
    | Sum.inl g => (s.1, s.2.1 + 1, s.2.2.1 - τx • (g + r • (s.2.2.1 - s.2.2.2.2.1)), s.2.2.2.1,
        s.2.2.2.2.1, s.2.2.2.2.2)
    | Sum.inr g => (s.1, s.2.1 + 1, s.2.2.1, s.2.2.2.1 + τy • g,
        s.2.2.2.2.1 + β • (s.2.2.1 - s.2.2.2.2.1),
        if (s.2.1 + 1) / 2 = n + (s.1 : ℕ) then (s.2.2.1, s.2.2.2.1 + τy • g) else s.2.2.2.2.2)
  output s := s.2.2.2.2.2

end OracleTemplate
