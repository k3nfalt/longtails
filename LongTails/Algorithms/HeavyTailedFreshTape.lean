import LongTails.Template
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace LongTails.Algorithms.HeavyTailedFreshTape

structure State (S Aux : Type) where
  value : S
  index : ℕ
  tape : ℕ → Aux

noncomputable def algorithm {Query Reply Output S Initial Aux : Type}
    [MeasurableSpace Initial] [MeasurableSpace Aux]
    (initialLaw : ProbabilityMeasure Initial) (auxLaw : ProbabilityMeasure Aux)
    (initial : Initial → S) (query : S → Aux → Query)
    (update : S → Aux → Reply → S) (output : S → Output) :
    OracleTemplate.Algorithm Query Reply Output where
  Seed := Initial × (ℕ → Aux)
  law := ⟨(initialLaw : Measure Initial).prod
    (Measure.infinitePi fun _ : ℕ => (auxLaw : Measure Aux)), inferInstance⟩
  State := State S Aux
  initial seed := ⟨initial seed.1, 0, seed.2⟩
  query state := (0, query state.value (state.tape state.index))
  update state reply := ⟨update state.value (state.tape state.index) reply,
    state.index + 1, state.tape⟩
  output state := output state.value

end LongTails.Algorithms.HeavyTailedFreshTape
