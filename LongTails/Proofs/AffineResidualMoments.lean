import LongTails.Proofs.AffineResidualTrajectory

namespace LongTails.Proofs.AffineResidualMoments

open MeasureTheory
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot affine)
open LongTails.Proofs.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSampling
open LongTails.Proofs.AffineResidualTrajectory

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (C : Set E) (s : Snapshot ι E) (τ μ β D : ℝ)
  (f : ι → E → ℝ) (field : ι → E → E) (initial : State ι E)

lemma conditional_moment_bound (k : ℕ) (payoff : State ι E → State ι E → ι × ι → ℝ) {B : ℝ}
    (hbound : ∀ state q, (∀ i, 0 ≤ q.probability i) → (∑ i, q.probability i = 1) →
      (∫ seed, payoff state q (chosenIndices C s τ μ (stepSize β k) state seed)
        ∂((volume : Measure unitInterval).prod volume)) ≤ B) :
    Integrable (fun ω => payoff (runState C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k) (indices C s τ μ β D f field initial ω k))
        (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, payoff (runState C s τ μ β D f field initial ω k)
        (ghost C s τ μ β D f field initial ω k) (indices C s τ μ β D f field initial ω k)
          ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ B := by
  let SimplexState := {q : State ι E // (∀ i, 0 ≤ q.probability i) ∧ ∑ i, q.probability i = 1}
  let observe : (ℕ → StepSeed) → SimplexState := fun ω =>
    ⟨ghost C s τ μ β D f field initial ω k,
      fun i => (ghost_probability_pos C s τ μ β D f field initial ω k i).le,
      ghost_probability_sum C s τ μ β D f field initial ω k⟩
  let select := selection C s τ μ β D f field initial
  obtain ⟨decode, hd⟩ := history_observable_factor select k observe (observe (fun _ => (0, 0)))
    (by
      intro ω other heq
      apply Subtype.ext
      exact ghost_history_congr C s τ μ β D f field initial ω other k heq)
  let state := fun h : Fin k → ι × ι => (historyState (initial, 0)
    (solverHistoryUpdate C (OracleTemplate.SaddlePoint.project C) s τ μ β D
      (fun q => (f q.1 q.2, field q.1 q.2))) k h).1
  let value := fun h ij => payoff (state h) (decode h).val ij
  have hh := adaptive_payoff_bound select (selection_measurable C s τ μ β D f field initial)
    k value ((volume : Measure unitInterval).prod volume)
    (fun h => hbound (state h) (decode h).val (decode h).property.1 (decode h).property.2)
  have he (ω : ℕ → StepSeed) : payoff (runState C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k) (indices C s τ μ β D f field initial ω k) =
      value (adaptiveHistory select ω k) (select k (adaptiveHistory select ω k) (ω k)) := by
    have hg : ghost C s τ μ β D f field initial ω k = (decode (adaptiveHistory select ω k)).val :=
      congrArg Subtype.val (hd ω)
    unfold indices
    rw [runState_of_history, hg]
    rfl
  simpa only [he] using hh

lemma primal_sample_moment (hC : IsCompact C) (hne : C.Nonempty) {M : ℝ}
    (hgrad : ∀ x ∈ C, ∀ i, ‖field i x - s.field i‖ ≤ M) (k : ℕ) :
    Integrable (fun ω => ‖primalSample C s τ μ β D f field initial ω k‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, ‖primalSample C s τ μ β D f field initial ω k‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ M ^ 2 := by
  let value := fun state (_q : State ι E) (ij : ι × ι) =>
    ‖field ij.1 (predictor C s τ μ (stepSize β k) state).point - s.field ij.1‖ ^ 2
  have hh := conditional_moment_bound C s τ μ β D f field initial k value (B := M ^ 2)
    (by
      intro state q _ _
      exact primal_second_moment C s τ μ (stepSize β k) state
        (fun i => field i (predictor C s τ μ (stepSize β k) state).point - s.field i)
        (hgrad _ (predictor_mem_min hC hne s τ μ (stepSize β k) state).1))
  simpa only [value, primalSample, predicted] using hh

lemma dual_sample_moment (hC : IsCompact C) (hne : C.Nonempty)
    (hres : ∀ x ∈ C, ∀ i, 0 ≤ D - (f i x - affine s i x) ∧ D - (f i x - affine s i x) ≤ D)
    (k : ℕ) :
    Integrable (fun ω => ∑ i, (predicted C s τ μ β D f field initial ω k).probability i *
      (dualSample C s τ μ β D f field initial ω k i) ^ 2)
        (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, ∑ i, (predicted C s τ μ β D f field initial ω k).probability i *
        (dualSample C s τ μ β D f field initial ω k i) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤
            (Fintype.card ι : ℝ) * D ^ 2 := by
  let v := fun state => predictor C s τ μ (stepSize β k) state
  let r := fun state i => D - (f i (v state).point - affine s i (v state).point)
  let value := fun state (_q : State ι E) (ij : ι × ι) =>
    ∑ i, (v state).probability i * (coordinateReply ij.2 (r state ij.2) i) ^ 2
  have hh := conditional_moment_bound C s τ μ β D f field initial k value
    (B := (Fintype.card ι : ℝ) * D ^ 2) (by
      intro state q _ _
      exact dual_second_moment C s τ μ (stepSize β k) state (v state).probability (r state)
        (fun i => (predictor_probability_pos C s τ μ (stepSize β k) state i).le)
        (predictor_probability_sum C s τ μ (stepSize β k) state)
        (hres _ (predictor_mem_min hC hne s τ μ (stepSize β k) state).1))
  simpa only [value, v, r, dualSample, dualMean, predicted] using hh

lemma primal_error_moment [CompleteSpace E] (hC : IsCompact C) (hne : C.Nonempty) {M : ℝ}
    (hgrad : ∀ x ∈ C, ∀ i, ‖field i x - s.field i‖ ≤ M) (k : ℕ) :
    Integrable (fun ω => ‖primalError C s τ μ β D f field initial ω k‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, ‖primalError C s τ μ β D f field initial ω k‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ M ^ 2 := by
  let v := fun state => predictor C s τ μ (stepSize β k) state
  let g := fun state i => field i (v state).point - s.field i
  let value := fun state (_q : State ι E) (ij : ι × ι) =>
    ‖(∑ i, (v state).probability i • g state i) - g state ij.1‖ ^ 2
  have hh := conditional_moment_bound C s τ μ β D f field initial k value (B := M ^ 2)
    (by
      intro state q _ _
      have hm := (primal_centered_moment C s τ μ (stepSize β k) state (g state)).trans
        (primal_weighted_square_bound C s τ μ (stepSize β k) state (g state)
          (hgrad _ (predictor_mem_min hC hne s τ μ (stepSize β k) state).1))
      convert hm using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun seed => congrArg (fun a : ℝ => a ^ 2) (norm_sub_rev _ _))
  simpa only [value, v, g, primalError, primalMean, primalSample, predicted] using hh

lemma dual_error_moment (hC : IsCompact C) (hne : C.Nonempty)
    (hres : ∀ x ∈ C, ∀ i, 0 ≤ D - (f i x - affine s i x) ∧ D - (f i x - affine s i x) ≤ D)
    (k : ℕ) :
    Integrable (fun ω => ∑ i, (ghost C s τ μ β D f field initial ω k).probability i *
      (dualError C s τ μ β D f field initial ω k i) ^ 2)
        (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, ∑ i, (ghost C s τ μ β D f field initial ω k).probability i *
        (dualError C s τ μ β D f field initial ω k i) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤
            (Fintype.card ι : ℝ) * D ^ 2 := by
  let v := fun state => predictor C s τ μ (stepSize β k) state
  let r := fun state i => D - (f i (v state).point - affine s i (v state).point)
  let value := fun state (q : State ι E) (ij : ι × ι) =>
    ∑ i, q.probability i * (r state i - coordinateReply ij.2 (r state ij.2) i) ^ 2
  have hh := conditional_moment_bound C s τ μ β D f field initial k value
    (B := (Fintype.card ι : ℝ) * D ^ 2) (by
      intro state q hq hqsum
      have hm := dual_centered_moment C s τ μ (stepSize β k) state q.probability (r state) hq hqsum
        (hres _ (predictor_mem_min hC hne s τ μ (stepSize β k) state).1)
      convert hm using 1
      apply integral_congr_ae
      filter_upwards [] with seed
      apply Finset.sum_congr rfl
      intro i _
      ring)
  simpa only [value, v, r, dualError, dualSample, dualMean, predicted] using hh

noncomputable def remainder (ω : ℕ → StepSeed) (k : ℕ) : ℝ :=
  (4 / μ * ‖primalSample C s τ μ β D f field initial ω k‖ ^ 2 +
    8 / τ * ∑ i, (predicted C s τ μ β D f field initial ω k).probability i *
      (dualSample C s τ μ β D f field initial ω k i) ^ 2) +
    2 / μ * ‖primalError C s τ μ β D f field initial ω k‖ ^ 2 +
    4 / τ * ∑ i, (ghost C s τ μ β D f field initial ω k).probability i *
      (dualError C s τ μ β D f field initial ω k i) ^ 2 +
    iterationWeight β k * pairing (primalError C s τ μ β D f field initial ω k)
      (dualError C s τ μ β D f field initial ω k) (predicted C s τ μ β D f field initial ω k)
      (ghost C s τ μ β D f field initial ω k)

lemma remainder_moment [CompleteSpace E] (hC : IsCompact C) (hne : C.Nonempty)
    (hμ : 0 < μ) (hτ : 0 < τ) {M : ℝ}
    (hgrad : ∀ x ∈ C, ∀ i, ‖field i x - s.field i‖ ≤ M)
    (hres : ∀ x ∈ C, ∀ i, 0 ≤ D - (f i x - affine s i x) ∧ D - (f i x - affine s i x) ≤ D)
    (k : ℕ) :
    Integrable (fun ω => remainder C s τ μ β D f field initial ω k)
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume) ∧
      (∫ ω, remainder C s τ μ β D f field initial ω k
        ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤
          16 * (M ^ 2 / μ + (Fintype.card ι : ℝ) * D ^ 2 / τ) := by
  have a := primal_sample_moment C s τ μ β D f field initial hC hne hgrad k
  have b := dual_sample_moment C s τ μ β D f field initial hC hne hres k
  have c := primal_error_moment C s τ μ β D f field initial hC hne hgrad k
  have d := dual_error_moment C s τ μ β D f field initial hC hne hres k
  have e := ghost_noise_integrable_zero C s τ μ β D f field initial k
  have ha := a.1.const_mul (4 / μ)
  have hb := b.1.const_mul (8 / τ)
  have hc := c.1.const_mul (2 / μ)
  have hd := d.1.const_mul (4 / τ)
  have he := e.1.const_mul (iterationWeight β k)
  refine ⟨(((ha.add hb).add hc).add hd).add he, ?_⟩
  unfold remainder
  have hs1 := integral_add (((ha.add hb).add hc).add hd) he
  have hs2 := integral_add ((ha.add hb).add hc) hd
  have hs3 := integral_add (ha.add hb) hc
  have hs4 := integral_add ha hb
  simp only [Pi.add_apply] at hs1 hs2 hs3 hs4
  rw [hs1, hs2, hs3, hs4]
  simp only [integral_const_mul, e.2, mul_zero, add_zero]
  have ha' := mul_le_mul_of_nonneg_left a.2 (by positivity : 0 ≤ 4 / μ)
  have hb' := mul_le_mul_of_nonneg_left b.2 (by positivity : 0 ≤ 8 / τ)
  have hc' := mul_le_mul_of_nonneg_left c.2 (by positivity : 0 ≤ 2 / μ)
  have hd' := mul_le_mul_of_nonneg_left d.2 (by positivity : 0 ≤ 4 / τ)
  have hm : 0 ≤ M ^ 2 / μ := by positivity
  have hn : 0 ≤ (Fintype.card ι : ℝ) * D ^ 2 / τ := by positivity
  simp only [div_eq_mul_inv] at ha' hb' hc' hd' hm hn ⊢
  nlinarith

end LongTails.Proofs.AffineResidualMoments
