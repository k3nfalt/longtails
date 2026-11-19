import LongTails.Setups.HighDimensionalStochasticWeakMinty
import LongTails.Includes

namespace LongTails.Proofs.StochasticWeakMintyInclusion

open OracleTemplate LongTails.Setups

noncomputable def highDimensionalInclusion :
    Inclusion StochasticWeakMinty.spec HighDimensionalStochasticWeakMinty.spec where
  numOracles_eq := rfl
  mapParams q := HighDimensionalStochasticWeakMinty.toGeneral q
  mapPublic q := HighDimensionalStochasticWeakMinty.toGeneral q
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

lemma highDimensional_includes :
    Includes StochasticWeakMinty.spec HighDimensionalStochasticWeakMinty.spec :=
  ⟨highDimensionalInclusion⟩

end LongTails.Proofs.StochasticWeakMintyInclusion
