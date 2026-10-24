import LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialPaths
import LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronTrials
open Classical MeasureTheory ProbabilityTheory
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
lemma gaussian_block_ball_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hD : 0 < Module.finrank ℝ E) (B : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (((ε / (2 * Real.sqrt (Module.finrank ℝ E))) ^ Module.finrank ℝ E *
      Real.exp (-ε ^ 2)) ^ B) ≤
    (Measure.pi (fun _ : Fin B => stdGaussian E)) {y | ∀ j : Fin B, ‖y j‖ ≤ ε} := by
  have hb := gaussian_ball_lower (0 : E) ε 0 hD hε (by norm_num) (by simp)
  simp only [neg_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at hb
  have he : {y : Fin B → E | ∀ j, ‖y j‖ ≤ ε} =
      Set.pi Set.univ (fun _ => Metric.closedBall (0 : E) ε) := by ext y; simp
  rw [he, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by positivity)]
  gcongr
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialPaths
open scoped RealInnerProductSpace
lemma block_current_escape_probability (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t B : ℕ) (x : Fin t → Weights P.dimension)
    (hKB : K ≤ B)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η
      (pastPoint P data η t x).ofLp.1
      (pastPoint P data η t x).ofLp.2)
    (hv : P.noiseScale ≤ |(pastPoint P data η t x).ofLp.2|)
    : ENNReal.ofReal (((ε / (2 * Real.sqrt (P.dimension + 1))) ^ (P.dimension + 1) *
      Real.exp (-ε ^ 2)) ^ B) ≤
    (Measure.pi (fun _ : Fin B => stdGaussian (Weights P.dimension)))
      {y | Separates data (pastPoint P data η (t + B) (Fin.append x y))} := by
  have hD : 0 < Module.finrank ℝ (Weights P.dimension) := by rw [weights_finrank]; omega
  have hl := gaussian_block_ball_lower (E := Weights P.dimension) hD B ε hε
  rw [weights_finrank] at hl
  push_cast at hl
  apply hl.trans
  apply measure_mono
  intro y hy
  exact block_current_escape P data u η δ ε K t B x y hKB hη hδ hsmall hε hεtotal hεprogress
    hK hR hu hmargin ht hσ hescape hv hy
lemma block_proposal_escape_probability (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t B : ℕ) (x : Fin t → Weights P.dimension)
    (b : Weights P.dimension) (hKB : K + 1 ≤ B)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hbase : b = WithLp.toLp 2
      ((pastPoint P data η t x).ofLp.1 +
        (η * (pastPoint P data η t x).ofLp.2) •
          LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
            (pastPoint P data η t x).ofLp.1
            (pastPoint P data η t x).ofLp.2,
      (pastPoint P data η t x).ofLp.2 + η *
        ⟪LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
          (pastPoint P data η t x).ofLp.1
          (pastPoint P data η t x).ofLp.2,
        (pastPoint P data η t x).ofLp.1⟫))
    (hwrong : ¬Separates data (pastPoint P data η t x))
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η b.ofLp.1 b.ofLp.2)
    (hv : P.noiseScale ≤ |b.ofLp.2|)
    : ENNReal.ofReal (((ε / (2 * Real.sqrt (P.dimension + 1))) ^ (P.dimension + 1) *
      Real.exp (-ε ^ 2)) ^ B) ≤
    (Measure.pi (fun _ : Fin B => stdGaussian (Weights P.dimension)))
      {y | Separates data (pastPoint P data η (t + B) (Fin.append x y))} := by
  have hD : 0 < Module.finrank ℝ (Weights P.dimension) := by rw [weights_finrank]; omega
  have hl := gaussian_block_ball_lower (E := Weights P.dimension) hD B ε hε
  rw [weights_finrank] at hl
  push_cast at hl
  apply hl.trans
  apply measure_mono
  intro y hy
  exact block_proposal_escape P data u η δ ε K t B x y b hKB hη hδ hsmall hε hεtotal hεprogress
    hK hR hu hmargin ht hσ hbase hwrong hescape hv hy
lemma block_one_step_probability (P : Public) (data : Data P) (η : ℝ) (t B : ℕ)
    (hB : 0 < B) (x : Fin t → Weights P.dimension) (q : ENNReal)
    (hq : q ≤ stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
      ((pastPoint P data η t x).ofLp.1 + (η * (pastPoint P data η t x).ofLp.2) •
        selected data (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2,
      (pastPoint P data η t x).ofLp.2 + η * ⟪selected data (pastPoint P data η t x).ofLp.1
        (pastPoint P data η t x).ofLp.2, (pastPoint P data η t x).ofLp.1⟫) + P.noiseScale • z)}) :
    q ≤ (Measure.pi (fun _ : Fin B => stdGaussian (Weights P.dimension)))
      {y | Separates data (pastPoint P data η (t + B) (Fin.append x y))} := by
  let S : Set (Weights P.dimension) := {z | Separates data (WithLp.toLp 2
      ((pastPoint P data η t x).ofLp.1 + (η * (pastPoint P data η t x).ofLp.2) •
        selected data (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2,
      (pastPoint P data η t x).ofLp.2 + η * ⟪selected data (pastPoint P data η t x).ofLp.1
        (pastPoint P data η t x).ofLp.2, (pastPoint P data η t x).ofLp.1⟫) + P.noiseScale • z)}
  have hS : MeasurableSet S := (measurableSet_separates P data).preimage (by fun_prop)
  have hm := (measurePreserving_eval (μ := fun _ : Fin B => stdGaussian (Weights P.dimension))
    (⟨0, hB⟩ : Fin B)).map_eq
  have he := congrArg (fun ν : Measure (Weights P.dimension) => ν S) hm
  rw [Measure.map_apply (measurable_pi_apply (⟨0, hB⟩ : Fin B)) hS] at he
  calc
    _ ≤ stdGaussian (Weights P.dimension) S := hq
    _ = _ := he.symm
    _ ≤ _ := measure_mono fun y hy => block_first_sample_success P data η t B hB x y hy

end LongTails.Proofs.NoisyBatchQuadraticPerceptronTrials
