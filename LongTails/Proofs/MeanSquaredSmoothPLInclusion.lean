import LongTails.Setups.HighDimensionalMeanSquaredSmoothPL
import LongTails.Includes

namespace LongTails.Proofs.MeanSquaredSmoothPLInclusion

open OracleTemplate LongTails.Setups

noncomputable def inclusion :
    Inclusion MeanSquaredSmoothPL.spec HighDimensionalMeanSquaredSmoothPL.spec where
  numOracles_eq := rfl
  mapParams q := q.toGeneral
  mapPublic q := q.toGeneral
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid _ hq := hq.1
  admissible _ _ _ _ h := h
  successful := by
    intro p hp I O ha Ω m output P h
    exact h
  allowedAlgorithm _ _ _ := trivial

lemma includes : Includes MeanSquaredSmoothPL.spec HighDimensionalMeanSquaredSmoothPL.spec :=
  ⟨inclusion⟩

end LongTails.Proofs.MeanSquaredSmoothPLInclusion
