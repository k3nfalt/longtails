import LongTails.Setups.HighDimensionalConstrainedQuasar
import LongTails.Includes

namespace OracleTemplate.HighDimensionalQuasar

open LongTails.Setups

noncomputable def inclusion :
    Inclusion StochasticConstrainedQuasar.spec HighDimensionalConstrainedQuasar.spec where
  numOracles_eq := rfl
  mapParams p := p.toStochastic
  mapPublic p := p.toStochastic
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid p hp := by
    rcases hp with ⟨hL, hD, hγ, hγ1, hσ, hε, hδ, hδ4, _⟩
    exact ⟨hL, hD, hγ, hγ1, hσ, hε, hδ, show p.δ < 1 by linarith⟩
  admissible _ _ _ _ h := h
  successful _ _ _ _ _ _ _ _ _ h := h
  allowedAlgorithm _ _ _ := trivial

lemma includes : Includes StochasticConstrainedQuasar.spec HighDimensionalConstrainedQuasar.spec :=
  ⟨inclusion⟩

lemma valid_nonempty : ∃ p, HighDimensionalConstrainedQuasar.spec.valid p := by
  let p : HighDimensionalConstrainedQuasar.Params :=
    ⟨2 ^ 34 * 3 ^ 5, 0, 1, 1, 1 / 2, 0, 1 / 100000000, 1 / 4⟩
  refine ⟨p, ?_⟩
  have hs : Real.sqrt (1 * 1 ^ 2 / (1 / 100000000)) = 10000 := by
    rw [show (1 : ℝ) * 1 ^ 2 / (1 / 100000000) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hf : ⌊Real.sqrt (1 * 1 ^ 2 / (1 / 100000000)) / (10000 * (1 / 2)) + 0 ^ 2 * 1 ^ 2 *
      Real.log (1 / (1 / 4)) / (8192 * (1 / 2) ^ 2 * (1 / 100000000) ^ 2)⌋₊ = 2 := by
    rw [hs]
    norm_num
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num,
    le_rfl, by norm_num, Or.inl rfl, ?_⟩
  change 2 ^ 34 * (⌊Real.sqrt (1 * 1 ^ 2 / (1 / 100000000)) / (10000 * (1 / 2)) + 0 ^ 2 * 1 ^ 2 *
      Real.log (1 / (1 / 4)) / (8192 * (1 / 2) ^ 2 * (1 / 100000000) ^ 2)⌋₊ + 1) ^ 5 ≤ 2 ^ 34 * 3 ^ 5
  rw [hf]

end OracleTemplate.HighDimensionalQuasar
