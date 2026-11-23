import LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex
import LongTails.Proofs.ThirdOrderLowerParameters
import LongTails.Includes

namespace LongTails.Proofs.ThirdOrderSmoothInclusion

open OracleTemplate LongTails.Setups

noncomputable def highDimensionalInclusion :
    Inclusion StochasticThirdOrderSmoothNonconvex.spec
      HighDimensionalStochasticThirdOrderSmoothNonconvex.spec where
  numOracles_eq := rfl
  mapParams q := HighDimensionalStochasticThirdOrderSmoothNonconvex.toGeneral q
  mapPublic q := HighDimensionalStochasticThirdOrderSmoothNonconvex.toGeneral q
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid q hq := by
    have hΔ := (LongTails.Proofs.ThirdOrderLowerParameters.ratio_bounds q hq).2.2
    obtain ⟨hL₁, hL₂, hL₃, hσ, hε, -, -⟩ := hq
    exact ⟨hL₁, hL₂, hL₃, hσ, hΔ, hε⟩
  admissible _ _ _ _ h := h
  successful := by
    intro p hp I O ha Ω m output P h
    exact h
  allowedAlgorithm _ _ _ := trivial

lemma highDimensional_includes :
    Includes StochasticThirdOrderSmoothNonconvex.spec
      HighDimensionalStochasticThirdOrderSmoothNonconvex.spec :=
  ⟨highDimensionalInclusion⟩

end LongTails.Proofs.ThirdOrderSmoothInclusion
