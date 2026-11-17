import LongTails.Setups.HighDimensionalAbcNoiseNonconvex
import LongTails.Includes

namespace LongTails.Proofs.AbcNoiseInclusion

open OracleTemplate LongTails.Setups

noncomputable def highDimensionalInclusion :
    Inclusion AbcNoiseNonconvex.spec HighDimensionalAbcNoiseNonconvex.spec where
  numOracles_eq := rfl
  mapParams q := HighDimensionalAbcNoiseNonconvex.toGeneral q
  mapPublic q := HighDimensionalAbcNoiseNonconvex.toGeneral q
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid q hq := by
    obtain ⟨hL, hA, hB, hC, hε, hreg, _⟩ := hq
    have hΔ : 0 ≤ q.Δ := by
      by_contra hneg
      push Not at hneg
      nlinarith [sq_nonneg q.ε, mul_neg_of_pos_of_neg hL hneg]
    exact ⟨hL, hA, hB, hC, hΔ, hε⟩
  admissible _ _ _ _ h := h
  successful := by
    intro p hp I O ha Ω m output P h
    exact h
  allowedAlgorithm _ _ _ := trivial

lemma highDimensional_includes : Includes AbcNoiseNonconvex.spec HighDimensionalAbcNoiseNonconvex.spec :=
  ⟨highDimensionalInclusion⟩

end LongTails.Proofs.AbcNoiseInclusion
