import LongTails.Proofs.HeavyTailedMarkovLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma finite_probability_weights (μ : Measure S) [IsProbabilityMeasure μ] :
    (∀ i, 0 ≤ μ.real {i}) ∧ ∑ i, μ.real {i} = 1 := by
  constructor
  · intro i
    exact ENNReal.toReal_nonneg
  · simp

lemma finite_comp_weights (κ : Kernel S S) [IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] (j : S) :
    (κ ∘ₘ π).real {j} = ∑ i, π.real {i} * (κ i).real {j} := by
  have h : (κ ∘ₘ π) {j} = ∑ i, π {i} * κ i {j} := by
    rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton j)]
    simp only [Measure.smul_apply, smul_eq_mul, tsum_fintype]
  unfold Measure.real
  rw [h, ENNReal.toReal_sum (fun (i : S) (_ : i ∈ Finset.univ) =>
    ENNReal.mul_ne_top (measure_ne_top π {i}) (measure_ne_top (κ i) {j}))]
  simp only [ENNReal.toReal_mul]

lemma finite_stationary_weights (κ : Kernel S S) [IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] (hπ : κ ∘ₘ π = π) (j : S) :
    ∑ i, π.real {i} * (κ i).real {j} = π.real {j} := by
  rw [← finite_comp_weights, hπ]

omit [Fintype S] [MeasurableSingletonClass S] in
lemma finite_refresh_weights (κ : Kernel S S) [IsMarkovKernel κ]
    (π : Measure S) {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ i j, ENNReal.ofReal α * π {j} ≤ κ i {j}) (i j : S) :
    α * π.real {j} ≤ (κ i).real {j} := by
  have hh := ENNReal.toReal_mono (measure_ne_top (κ i) {j}) (h i j)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα, measureReal_def] using hh

lemma finite_integrable {E : Type*} [NormedAddCommGroup E] (μ : Measure S)
    [IsFiniteMeasure μ] (f : S → E) : Integrable f μ :=
  (SimpleFunc.ofFinite f).integrable_of_isFiniteMeasure

lemma finite_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → E) :
    (∫ i, f i ∂μ) = ∑ i, μ.real {i} • f i :=
  integral_fintype (finite_integrable μ f)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma finite_residual_transition (p : S → ℝ) (P : S → S → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hPs : ∀ i, ∑ j, P i j = 1)
    (hstat : ∀ j, ∑ i, p i * P i j = p j)
    {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) (href : ∀ i j, α * p j ≤ P i j) :
    ∃ Q : S → S → ℝ, (∀ i j, 0 ≤ Q i j) ∧ (∀ i, ∑ j, Q i j = 1) ∧
      (∀ j, ∑ i, p i * Q i j = p j) ∧
      ∀ i j, P i j = (1 - α) * Q i j + α * p j := by
  classical
  by_cases he : α = 1
  · subst α
    have hEq (i j : S) : P i j = p j := by
      have hz : ∑ k, (P i k - p k) = 0 := by rw [Finset.sum_sub_distrib, hPs, hs]; ring
      have hn : ∀ k ∈ Finset.univ, 0 ≤ P i k - p k := by
        intro k hk
        have := href i k
        linarith
      have heq := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz j (Finset.mem_univ j)
      linarith
    refine ⟨fun _ j => p j, fun _ j => hp j, fun _ => hs, ?_, ?_⟩
    · intro j
      rw [← Finset.sum_mul, hs, one_mul]
    · intro i j
      simpa using hEq i j
  · have hq : 0 < 1 - α := by have := lt_of_le_of_ne ha1 he; linarith
    refine ⟨fun i j => (P i j - α * p j) / (1 - α), ?_, ?_, ?_, ?_⟩
    · intro i j
      exact div_nonneg (sub_nonneg.mpr (href i j)) hq.le
    · intro i
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hPs, hs, mul_one]
      exact div_self (ne_of_gt hq)
    · intro j
      simp_rw [← mul_div_assoc, mul_sub, mul_left_comm (p _) α (p j)]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hstat, ← Finset.mul_sum,
        ← Finset.sum_mul, hs, one_mul]
      field_simp
    · intro i j
      rw [mul_div_cancel₀ _ (ne_of_gt hq)]
      ring

lemma finite_pathLaw_integral_future (κ : Kernel S S) [IsMarkovKernel κ]
    (μ : ProbabilityMeasure S) (k t : ℕ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : (Finset.Iic k → S) → S → E) :
    (∫ ξ, W (frestrictLe k ξ) (ξ (k + t))
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S))) =
    ∫ h, ∫ y, W h y ∂(κ ^ t) (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
      ∂((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map (frestrictLe k)) := by
  let ρ := (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map (frestrictLe k)
  let K : Kernel (Finset.Iic k → S) S :=
    (κ ^ t).comap (fun h => h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)
  have : IsProbabilityMeasure ρ := inferInstance
  have hi : Integrable (Function.uncurry W) (ρ ⊗ₘ K) := finite_integrable _ _
  have hj := HeavyTailedMarkovGradient.pathLaw_prefix_future κ μ k t
  change ρ ⊗ₘ K = _ at hj
  have hi' := hi
  rw [hj] at hi'
  have he := Measure.integral_compProd hi
  rw [hj, integral_map (by fun_prop) hi'.aestronglyMeasurable] at he
  simpa only [Function.uncurry_apply_pair, K, Kernel.comap_apply, ρ] using he

noncomputable def finiteWeightKernel (Q : S → S → ℝ) : Kernel S S :=
  Kernel.ofFunOfCountable (fun i => Measure.sum (fun j => ENNReal.ofReal (Q i j) • Measure.dirac j))

lemma finiteWeightKernel_markov (Q : S → S → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hs : ∀ i, ∑ j, Q i j = 1) : IsMarkovKernel (finiteWeightKernel Q) := by
  constructor
  intro i
  exact HasSum.isProbabilityMeasure_sum_dirac (hQ i) (by simpa [hs i] using hasSum_fintype (Q i))

lemma finiteWeightKernel_real (Q : S → S → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (i j : S) :
    (finiteWeightKernel Q i).real {j} = Q i j := by
  change (Measure.sum (fun k => ENNReal.ofReal (Q i k) • Measure.dirac k) {j}).toReal = _
  rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hQ i j)]

lemma finiteWeightKernel_stationary (Q : S → S → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hs : ∀ i, ∑ j, Q i j = 1) (π : Measure S) [IsProbabilityMeasure π]
    (hstat : ∀ j, ∑ i, π.real {i} * Q i j = π.real {j}) :
    finiteWeightKernel Q ∘ₘ π = π := by
  have : IsMarkovKernel (finiteWeightKernel Q) := finiteWeightKernel_markov Q hQ hs
  apply Measure.ext_of_measureReal_singleton
  intro j
  rw [finite_comp_weights]
  simpa only [finiteWeightKernel_real Q hQ] using hstat j

end OracleTemplate.MarkovProduct
