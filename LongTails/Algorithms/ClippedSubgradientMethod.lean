import LongTails.Algorithms.Clipping
import LongTails.Template
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.ClippedSubgradient

inductive Query (E : Type) where
  | subgradient : E → Query E
  | projection : E → Query E

structure State (E : Type) where
  t : ℕ
  x : E
  pending : Bool
  proposal : E
  index : ℕ
  out : E

noncomputable def method {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (η τ : ℝ) (x0 : E) : Algorithm (Query E) E E where
  Seed := Fin (K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (K + 1))).toMeasure, inferInstance⟩
  State := State E
  initial j := ⟨0, x0, false, x0, j.val, x0⟩
  query s := (0, if s.pending then .projection s.proposal else .subgradient s.x)
  update s reply :=
    if s.pending then
      ⟨s.t + 1, reply, false, reply, s.index, if s.t + 1 = s.index then reply else s.out⟩
    else
      ⟨s.t, s.x, true, s.x - η • clip τ reply, s.index, s.out⟩
  output s := s.out

end OracleTemplate.ClippedSubgradient
