import LongTails.Proofs.DashaCompression
import LongTails.Proofs.DashaQuantization

namespace LongTails.Proofs.DashaInitialization

open MeasureTheory
open LongTails.Algorithms.DashaQuantization

lemma fine_error_sq (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : Vector d) (u : Fin d → ℝ) :
    ‖rounded d false ρ x u - x‖ ^ 2 ≤ d * ρ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _ : Fin d, ρ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := (sq_le_sq₀ (abs_nonneg _) hρ.le).mpr
        (DashaQuantization.coordinate_initial_error d ρ hρ x u j)
      simpa only [PiLp.sub_apply, sq_abs] using h
    _ = _ := by simp

lemma fine_scalar_integrable (x : ℝ) :
    Integrable (fun u : ℝ => (scalarIndex false x u : ℝ)) (unitLaw : Measure ℝ) := by
  have hm : Measurable (fun u : ℝ => (scalarIndex false x u : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp ((DashaQuantization.measurable_scalarIndex false).comp
      (measurable_const.prodMk measurable_id))
  apply (integrable_const (|x| + 1)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    rw [Real.norm_eq_abs]
    have he := DashaQuantization.scalar_initial_error x u
    have ht := abs_add_le ((scalarIndex false x u : ℝ) - x) x
    rw [sub_add_cancel] at ht
    linarith)

lemma fine_scalar_error_integrable (x : ℝ) :
    Integrable (fun u : ℝ => ((scalarIndex false x u : ℝ) - x) ^ 2) (unitLaw : Measure ℝ) := by
  have hm : Measurable (fun u : ℝ => ((scalarIndex false x u : ℝ) - x) ^ 2) :=
    (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp ((DashaQuantization.measurable_scalarIndex false).comp
      (measurable_const.prodMk measurable_id))).sub_const x).pow_const 2
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (DashaQuantization.scalar_initial_error x u)
    simpa only [sq_abs, one_pow] using h)

lemma fine_moments {d : ℕ+} (ρ : ℝ) (hρ : 0 < ρ) (x : Vector d) :
    let Q := fun seed : LongTails.Algorithms.DashaCyclic.Seed d => rounded d false ρ x seed.2
    Integrable Q (LongTails.Algorithms.DashaCyclic.law d : Measure _) ∧
    (∫ seed, Q seed ∂(LongTails.Algorithms.DashaCyclic.law d : Measure _)) = x ∧
    Integrable (fun seed => ‖Q seed - x‖ ^ 2) (LongTails.Algorithms.DashaCyclic.law d : Measure _) ∧
    (∫ seed, ‖Q seed - x‖ ^ 2 ∂(LongTails.Algorithms.DashaCyclic.law d : Measure _)) ≤ d * ρ ^ 2 := by
  let Q := fun seed : LongTails.Algorithms.DashaCyclic.Seed d => rounded d false ρ x seed.2
  have hc (j : Fin d) := DashaCompression.coordinate_law_integral j
    (fun _ u => ρ * (scalarIndex false (x j / ρ) u : ℝ))
    (fun _ => measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((DashaQuantization.measurable_scalarIndex false).comp (measurable_const.prodMk measurable_id))))
    (fun _ => (fine_scalar_integrable (x j / ρ)).const_mul ρ)
  have hi : Integrable Q (LongTails.Algorithms.DashaCyclic.law d : Measure _) :=
    Integrable.of_eval_piLp (fun j => (hc j).1)
  have hm : Measurable Q := (DashaQuantization.measurable_reconstruct d ρ).comp
    ((DashaQuantization.measurable_indices d false ρ).comp (measurable_const.prodMk measurable_snd))
  have hI : Integrable (fun seed => ‖Q seed - x‖ ^ 2)
      (LongTails.Algorithms.DashaCyclic.law d : Measure _) :=
    (integrable_const ((d : ℝ) * ρ ^ 2)).mono' ((hm.sub_const x).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun seed => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact fine_error_sq d ρ hρ x seed.2))
  refine ⟨hi, ?_, hI, ?_⟩
  · ext j
    rw [OracleTemplate.ZerothOrder.integral_euclidean_apply hi]
    change (∫ seed : LongTails.Algorithms.DashaCyclic.Seed d, ρ * (scalarIndex false (x j / ρ) (seed.2 j) : ℝ)
      ∂(LongTails.Algorithms.DashaCyclic.law d : Measure _)) = _
    rw [(hc j).2]
    simp_rw [integral_const_mul, DashaQuantization.scalarIndex_mean]
    simp [mul_div_cancel₀ _ hρ.ne', ne_of_gt (show (0 : ℝ) < d by exact_mod_cast d.pos)]
  · calc
      _ ≤ ∫ _ : LongTails.Algorithms.DashaCyclic.Seed d, (d : ℝ) * ρ ^ 2
          ∂(LongTails.Algorithms.DashaCyclic.law d : Measure _) :=
        integral_mono hI (integrable_const _) (fun seed => fine_error_sq d ρ hρ x seed.2)
      _ = _ := by simp

lemma fine_measurable {d : ℕ+} (ρ : ℝ) (x : Vector d) :
    Measurable (fun seed : LongTails.Algorithms.DashaCyclic.Seed d => rounded d false ρ x seed.2) :=
  (DashaQuantization.measurable_reconstruct d ρ).comp
    ((DashaQuantization.measurable_indices d false ρ).comp (measurable_const.prodMk measurable_snd))

lemma independent_fine_errors {d : ℕ+} {n : ℕ} (ρ : ℝ) (v : Fin n → Vector d) :
    ProbabilityTheory.iIndepFun
      (fun i (seed : Fin n → LongTails.Algorithms.DashaCyclic.Seed d) => rounded d false ρ (v i) (seed i).2 - v i)
      (Measure.pi fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)) :=
  ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure (LongTails.Algorithms.DashaCyclic.Seed d)))
    (X := fun i (seed : LongTails.Algorithms.DashaCyclic.Seed d) => rounded d false ρ (v i) seed.2 - v i)
    (fun i => ((fine_measurable ρ (v i)).sub_const (v i)).aemeasurable)

lemma replicated_fine_moments {d : ℕ+} {n : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (v : Fin n → Vector d) (i : Fin n) :
    let P := Measure.pi fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)
    let Z := fun seed : Fin n → LongTails.Algorithms.DashaCyclic.Seed d => rounded d false ρ (v i) (seed i).2 - v i
    Integrable Z P ∧ (∫ seed, Z seed ∂P) = 0 ∧
    Integrable (fun seed => ‖Z seed‖ ^ 2) P ∧ (∫ seed, ‖Z seed‖ ^ 2 ∂P) ≤ d * ρ ^ 2 := by
  have h := fine_moments ρ hρ (v i)
  have hi := h.1.sub (integrable_const (v i))
  change Integrable (fun seed : LongTails.Algorithms.DashaCyclic.Seed d =>
    rounded d false ρ (v i) seed.2 - v i) (LongTails.Algorithms.DashaCyclic.law d : Measure _) at hi
  have hz : (∫ seed : LongTails.Algorithms.DashaCyclic.Seed d, rounded d false ρ (v i) seed.2 - v i
      ∂(LongTails.Algorithms.DashaCyclic.law d : Measure _)) = 0 := by
    rw [integral_sub h.1 (integrable_const _), h.2.1]
    simp
  refine ⟨integrable_comp_eval (X := fun _ : Fin n => LongTails.Algorithms.DashaCyclic.Seed d)
    (μ := fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)) (i := i) hi, ?_,
    integrable_comp_eval (X := fun _ : Fin n => LongTails.Algorithms.DashaCyclic.Seed d)
      (μ := fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)) (i := i)
      (f := fun seed : LongTails.Algorithms.DashaCyclic.Seed d => ‖rounded d false ρ (v i) seed.2 - v i‖ ^ 2)
      h.2.2.1, ?_⟩
  · rw [integral_comp_eval (X := fun _ : Fin n => LongTails.Algorithms.DashaCyclic.Seed d)
      (μ := fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)) hi.aestronglyMeasurable, hz]
  · rw [integral_comp_eval (X := fun _ : Fin n => LongTails.Algorithms.DashaCyclic.Seed d)
      (μ := fun _ : Fin n => (LongTails.Algorithms.DashaCyclic.law d : Measure _)) h.2.2.1.aestronglyMeasurable]
    exact h.2.2.2

end LongTails.Proofs.DashaInitialization
