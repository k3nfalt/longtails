import LongTails.Proofs.NoisyBatchQuadraticPerceptronRegeneration
open MeasureTheory ProbabilityTheory OracleTemplate
open scoped RealInnerProductSpace
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronRegeneration
open LongTails.Proofs.NoisyBatchQuadraticPerceptronBudget
open LongTails.Algorithms.NoisyBatchQuadraticPerceptron
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronConvergence
lemma output_probability_of_batch (P : Public) (data : Data P) (η ρ : ℝ)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (N L : ℕ) (hL : (P.count : ℕ) * (N + 1) ≤ L)
    (hprob : (P.noise.law : Measure P.noise.Ω).real
      {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point} ≤ ρ) :
    ((P.noise.law : Measure P.noise.Ω).prod (O.law : Measure _))
      {z | ¬Separates data (output P O η L z.1 z.2)} ≤ ENNReal.ofReal ρ := by
  let S := {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point}
  have hsub : {z | ¬Separates data (output P O η L z.1 z.2)} ⊆
      S ×ˢ (Set.univ : Set ((k : ℕ) → O.Seed k)) := by
    intro z hz
    refine ⟨?_, Set.mem_univ _⟩
    intro hs
    exact hz (output_separates_of_batch P data O hO η z.1 N L z.2 hs hL)
  calc
    _ ≤ ((P.noise.law : Measure P.noise.Ω).prod (O.law : Measure _))
        (S ×ˢ (Set.univ : Set ((k : ℕ) → O.Seed k))) := measure_mono hsub
    _ = (P.noise.law : Measure P.noise.Ω) S := by rw [Measure.prod_prod, measure_univ, mul_one]
    _ = ENNReal.ofReal ((P.noise.law : Measure P.noise.Ω).real S) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hprob
lemma execution_failure_bound (P : Public) (data : Data P) (η ρ : ℝ)
    (O : Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (L : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hL : ⌈100000 * (P.count : ℝ) * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2 +
      ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1))) *
      (2 / ρ) ^ (5 * Real.exp (25000 * (P.dimension + 1 : ℝ) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) / ρ⌉₊ ≤ L) :
    ((P.noise.law : Measure P.noise.Ω).prod (O.law : Measure _))
      {z | ¬Separates data (output P O η L z.1 z.2)} ≤ ENNReal.ofReal ρ := by
  let K := ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊
  let B := K + 2
  let A := 25000 * (P.dimension + 1 : ℝ) ^ 2 * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2
  let J := ⌈Real.exp A * Real.log (2 / ρ)⌉₊
  let N := ⌈(2 / ρ) * 128 ^ J * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B)⌉₊
  have hb := tuned_call_budget P η ρ hδ hδR hρ hρ1 htune
  have hp := batch_failure_confidence P data η ρ h u K B hσ hδ hδR hρ hR hu hmargin htune rfl rfl
  apply output_probability_of_batch P data η ρ O hO N L
  · exact hb.trans hL
  · exact hp
end LongTails.Proofs.NoisyBatchQuadraticPerceptronConvergence
