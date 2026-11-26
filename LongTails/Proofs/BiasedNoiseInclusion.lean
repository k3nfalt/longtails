import LongTails.Setups.HighDimensionalBiasedNoiseNonconvex
import LongTails.Includes

namespace LongTails.Proofs.BiasedNoiseInclusion

open OracleTemplate LongTails.Setups

noncomputable def highDimensionalInclusion :
    Inclusion BiasedNoiseNonconvex.spec HighDimensionalBiasedNoiseNonconvex.spec where
  numOracles_eq := rfl
  mapParams q := HighDimensionalBiasedNoiseNonconvex.toGeneral q
  mapPublic q := HighDimensionalBiasedNoiseNonconvex.toGeneral q
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid q hq := by
    obtain ⟨hL, hm0, hm1, hM, hσ, hζ, hε, hfloor, hreg, _⟩ := hq
    have hΔ : 0 ≤ q.Δ := by
      by_contra hneg
      push Not at hneg
      nlinarith [sq_nonneg q.ε, mul_neg_of_pos_of_neg hL hneg]
    exact ⟨hL, hm0, hm1, hM, hσ, hζ, hΔ, hε, hfloor⟩
  admissible _ _ _ _ h := h
  successful := by
    intro p hp I O ha Ω m output P h
    exact h
  allowedAlgorithm _ _ _ := trivial

lemma highDimensional_includes :
    Includes BiasedNoiseNonconvex.spec HighDimensionalBiasedNoiseNonconvex.spec :=
  ⟨highDimensionalInclusion⟩

end LongTails.Proofs.BiasedNoiseInclusion
