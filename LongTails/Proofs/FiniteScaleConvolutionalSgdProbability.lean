import LongTails.Proofs.FiniteScaleConvolutionalSgdTrajectory
import LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdProbability

lemma uniform_integral {ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (f : ι → ℝ) :
    (∫ i, f i ∂(PMF.uniformOfFintype ι).toMeasure) = (∑ i, f i) / Fintype.card ι := by
  simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply, div_eq_mul_inv,
    ← Finset.sum_mul, mul_comm]

lemma integral_prefix_next {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P) (t : ℕ) (H : (Fin t → ι) × ι → ℝ) :
    (∫ ω, H ((fun j : Fin t => ξ j ω), ξ t ω) ∂P) =
      ∫ ω, (∑ i, H ((fun j : Fin t => ξ j ω), i)) / Fintype.card ι ∂P := by
  have hh := NoisyBatchQuadraticPerceptronExecution.integral_past_next P
    (PMF.uniformOfFintype ι).toMeasure ξ hξ.measurable hξ.independent t (hξ.marginal t) H
    (Integrable.of_finite : Integrable H _)
  simp_rw [uniform_integral] at hh
  rw [hh]
  have hm : Measurable (fun ω (j : Fin t) => ξ j ω) :=
    Measurable.of_eval (fun j => hξ.measurable j)
  exact integral_map hm.aemeasurable
    (measurable_of_countable (fun z : Fin t → ι => (∑ i, H (z, i)) / Fintype.card ι)).aestronglyMeasurable

lemma integrable_finite_comp {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → ι) (hY : Measurable Y) (f : ι → ℝ) :
    Integrable (fun ω => f (Y ω)) P := by
  exact Integrable.comp_measurable Integrable.of_finite hY

lemma integral_prefix_next_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P) (t : ℕ)
    (H : (Fin t → ι) × ι → ℝ) (G : (Fin t → ι) → ℝ)
    (hbound : ∀ z, (∑ i, H (z, i)) ≤ (Fintype.card ι : ℝ) * G z) :
    (∫ ω, H ((fun j : Fin t => ξ j ω), ξ t ω) ∂P) ≤
      ∫ ω, G (fun j : Fin t => ξ j ω) ∂P := by
  rw [integral_prefix_next P ξ hξ t H]
  have hm : Measurable (fun ω (j : Fin t) => ξ j ω) :=
    Measurable.of_eval (fun j => hξ.measurable j)
  apply integral_mono
    (integrable_finite_comp P _ hm (fun z => (∑ i, H (z, i)) / Fintype.card ι))
    (integrable_finite_comp P _ hm G)
  intro ω
  apply (div_le_iff₀ (show (0 : ℝ) < Fintype.card ι by exact_mod_cast Fintype.card_pos)).2
  simpa only [mul_comm] using hbound (fun j : Fin t => ξ j ω)

lemma prefix_contraction {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (V : (k : ℕ) → (Fin k → ι) → ℝ) (r C : ℝ) (T : ℕ) (hr : 0 ≤ r)
    (hinit : ∀ z, V 0 z ≤ C)
    (hstep : ∀ k < T, ∀ z, (∑ i, V (k + 1) (Fin.snoc z i)) ≤
      (Fintype.card ι : ℝ) * r * V k z) :
    ∀ k ≤ T, (∫ ω, V k (fun j : Fin k => ξ j ω) ∂P) ≤ r ^ k * C := by
  have hm (k : ℕ) : Measurable (fun ω (j : Fin k) => ξ j ω) :=
    Measurable.of_eval (fun j => hξ.measurable j)
  intro k
  induction k with
  | zero =>
    intro _
    have hh := integral_mono (integrable_finite_comp P _ (hm 0) (V 0))
      (integrable_const C) (fun ω => hinit (fun j : Fin 0 => ξ j ω))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, pow_zero] using hh
  | succ k ih =>
    intro hk
    have hkT : k < T := Nat.lt_of_succ_le hk
    have hh := integral_prefix_next_le P ξ hξ k
      (fun z => V (k + 1) (Fin.snoc z.1 z.2)) (fun z => r * V k z)
      (fun z => by simpa only [mul_assoc] using hstep k hkT z)
    simp only [NoisyBatchQuadraticPerceptronExecution.sample_snoc] at hh
    rw [integral_const_mul] at hh
    calc
      _ ≤ r * (∫ ω, V k (fun j : Fin k => ξ j ω) ∂P) := hh
      _ ≤ r * (r ^ k * C) := mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkT)) hr
      _ = _ := by rw [pow_succ]; ring

lemma independent_blocks_failure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : ∀ k, Measurable (ξ k)) (hi : iIndepFun ξ P)
    (B M : ℕ) (S : Set (Fin B → ι)) (q : ENNReal)
    (hblock : ∀ j, P {ω | (fun i : Fin B => ξ (j * B + i) ω) ∈ S} ≤ q) :
    P {ω | ∀ j < M, (fun i : Fin B => ξ (j * B + i) ω) ∈ S} ≤ q ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    let A : Set (Fin (M * B) → ι) := {z | ∀ j : Fin M,
      (fun i : Fin B => z ⟨j.val * B + i.val, by
        have hh := Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt)
        nlinarith [i.isLt]⟩) ∈ S}
    have hpre : (fun ω (i : Fin (M * B)) => ξ i ω) ⁻¹' A =
        {ω | ∀ j < M, (fun i : Fin B => ξ (j * B + i) ω) ∈ S} := by
      ext ω
      constructor
      · intro h j hj
        exact h ⟨j, hj⟩
      · intro h j
        exact h j j.isLt
    have hind := (NoisyBatchQuadraticPerceptronExecution.independent_past_block P ξ hξ hi
      (M * B) B).measure_inter_preimage_eq_mul A S (Set.toFinite A).measurableSet (Set.toFinite S).measurableSet
    rw [hpre] at hind
    have hsplit : {ω | ∀ j < M + 1, (fun i : Fin B => ξ (j * B + i) ω) ∈ S} =
        {ω | ∀ j < M, (fun i : Fin B => ξ (j * B + i) ω) ∈ S} ∩
          {ω | (fun i : Fin B => ξ (M * B + i) ω) ∈ S} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun j hj => h j (by omega), h M (by omega)⟩
      · rintro ⟨h, hM⟩ j hj
        by_cases he : j = M
        · simpa [he] using hM
        · exact h j (by omega)
    rw [hsplit, pow_succ]
    exact hind.le.trans (mul_le_mul' ih (hblock M))

lemma iid_shift {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    (P : Measure Ω) (ν : Measure ι) (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ν P) (t : ℕ) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k => ξ (t + k)) ν P := by
  refine ⟨fun k => hξ.measurable (t + k), ?_, fun k => hξ.marginal (t + k)⟩
  exact hξ.independent.precomp (fun _ _ h => Nat.add_left_cancel h)

end LongTails.Proofs.FiniteScaleConvolutionalSgdProbability
