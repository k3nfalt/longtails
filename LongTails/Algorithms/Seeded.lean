import LongTails.Template

namespace OracleTemplate

noncomputable def seeded {Q V U S : Type} [MeasurableSpace S]
    (A : Algorithm Q V U) (μ : MeasureTheory.ProbabilityMeasure S) : Algorithm Q V U where
  Seed := A.Seed × S
  law := ⟨(A.law : MeasureTheory.Measure _).prod (μ : MeasureTheory.Measure _), inferInstance⟩
  State := ℕ × S × A.State
  initial seed := (0,seed.2,A.initial seed.1)
  query state := A.query state.2.2
  update state reply := (state.1+1,state.2.1,A.update state.2.2 reply)
  output state := A.output state.2.2

end OracleTemplate
