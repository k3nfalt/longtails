import LongTails.Proofs.DashaCyclic
import LongTails.Proofs.DashaFloat
import LongTails.Proofs.ZerothOrderGridEstimator
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace LongTails.Proofs.DashaCompression

open MeasureTheory
open LongTails.Algorithms.DashaCyclic LongTails.Algorithms.DashaFloat
open LongTails.Algorithms.DashaQuantization (unitLaw)

lemma inclusion_weighted {d : ℕ+} (k j : Fin d) (A : ℝ) :
    (∑ shift : Fin d, if selected k shift j then A else 0) = (k.val + 1) * A := by
  calc
    _ = (∑ shift : Fin d, if selected k shift j then (1 : ℝ) else 0) * A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro shift _
      split_ifs <;> simp
    _ = _ := by rw [DashaCyclic.inclusion_sum]

lemma coordinate_mean {d : ℕ+} (k j : Fin d) (r : ℕ) (ρ x : ℝ) (hρ : ρ ≠ 0) :
    (1 / (d : ℝ)) * (∑ shift : Fin d, ∫ u : ℝ,
      (if selected k shift j then rounded r ρ (multiplier k * x) u else 0)
      ∂(unitLaw : Measure ℝ)) = x := by
  convert DashaCyclic.scaled_mean k j x using 2
  apply Finset.sum_congr rfl
  intro shift _
  by_cases h : selected k shift j
  · simp only [h, ↓reduceIte]
    exact DashaFloat.rounded_mean r ρ _ hρ
  · simp [h]

lemma coordinate_variance {d : ℕ+} (k j : Fin d) (r : ℕ) (ρ x : ℝ) (hρ : ρ ≠ 0) :
    (1 / (d : ℝ)) * (∑ shift : Fin d, ∫ u : ℝ,
      ((if selected k shift j then rounded r ρ (multiplier k * x) u else 0) - x) ^ 2
      ∂(unitLaw : Measure ℝ)) ≤
      ((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * x ^ 2 +
        2 * (k.val + 1) / (d : ℝ) * ρ ^ 2 := by
  let A := 2 / (4 : ℝ) ^ r * (multiplier k * x) ^ 2 + 2 * ρ ^ 2
  have hi (shift : Fin d) : (∫ u : ℝ,
      ((if selected k shift j then rounded r ρ (multiplier k * x) u else 0) - x) ^ 2
      ∂(unitLaw : Measure ℝ)) ≤
      ((if selected k shift j then multiplier k * x else 0) - x) ^ 2 +
        (if selected k shift j then A else 0) := by
    by_cases h : selected k shift j
    · simp only [h, ↓reduceIte]
      have hb := (DashaFloat.rounded_shifted_variance r ρ (multiplier k * x) x hρ).2
      dsimp [A]
      linarith
    · simp [h]
  calc
    _ ≤ (1 / (d : ℝ)) * (∑ shift : Fin d,
        (((if selected k shift j then multiplier k * x else 0) - x) ^ 2 +
          (if selected k shift j then A else 0))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun shift _ => hi shift)) (by positivity)
    _ = _ := by
      rw [Finset.sum_add_distrib, mul_add, DashaCyclic.scaled_variance, inclusion_weighted]
      dsimp [A, multiplier]
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
      have hk : (k.val : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

lemma coordinate_integrable {d : ℕ+} (k shift j : Fin d) (r : ℕ) (ρ x : ℝ) :
    Integrable (fun u : ℝ => if selected k shift j then rounded r ρ (multiplier k * x) u else 0)
      (unitLaw : Measure ℝ) := by
  by_cases h : selected k shift j
  · simpa only [h, ↓reduceIte] using DashaFloat.rounded_integrable r ρ (multiplier k * x)
  · simp only [h, ↓reduceIte]
    exact integrable_const 0

lemma coordinate_error_integrable {d : ℕ+} (k shift j : Fin d) (r : ℕ) (ρ x : ℝ)
    (hρ : ρ ≠ 0) :
    Integrable (fun u : ℝ =>
      ((if selected k shift j then rounded r ρ (multiplier k * x) u else 0) - x) ^ 2)
      (unitLaw : Measure ℝ) := by
  by_cases h : selected k shift j
  · simpa only [h, ↓reduceIte] using
      (DashaFloat.rounded_shifted_variance r ρ (multiplier k * x) x hρ).1
  · simp only [h, ↓reduceIte]
    exact integrable_const _

lemma summed_coordinate_variance {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hρ : ρ ≠ 0) :
    (∑ j : Fin d, (1 / (d : ℝ)) * (∑ shift : Fin d, ∫ u : ℝ,
      ((if selected k shift j then rounded r ρ (multiplier k * x j) u else 0) - x j) ^ 2
      ∂(unitLaw : Measure ℝ))) ≤
      ((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * ‖x‖ ^ 2 + 2 * (k.val + 1) * ρ ^ 2 := by
  calc
    _ ≤ ∑ j : Fin d, (((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * (x j) ^ 2 +
        2 * (k.val + 1) / (d : ℝ) * ρ ^ 2) :=
      Finset.sum_le_sum (fun j _ => coordinate_variance k j r ρ (x j) hρ)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
      field_simp

lemma compress_apply {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) (j : Fin d) :
    compress k r ρ x seed j =
      if selected k seed.1 j then rounded r ρ (multiplier k * x j) (seed.2 j) else 0 := by
  change ρ * (compressedIndex k seed.1 r ρ x seed.2 j : ℝ) = _
  by_cases h : selected k seed.1 j
  · simp [compressedIndex, h, rounded]
  · simp [compressedIndex, h]

lemma measurable_compressedIndex_joint {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × Seed d => compressedIndex k z.2.1 r ρ z.1 z.2.2) := by
  apply Measurable.of_eval
  intro j
  have hx : Measurable (fun z : EuclideanSpace ℝ (Fin d) × Seed d =>
      multiplier k * z.1 j / ρ) :=
    (measurable_const.mul ((measurable_pi_apply j).comp
      ((WithLp.measurable_ofLp 2 (Fin d → ℝ)).comp measurable_fst))).div_const ρ
  have hu : Measurable (fun z : EuclideanSpace ℝ (Fin d) × Seed d => z.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin d) × Seed d | selected k z.2.1 j} :=
    (Set.to_countable {shift : Fin d | selected k shift j}).measurableSet.preimage
      (measurable_fst.comp measurable_snd)
  exact Measurable.ite hset ((DashaFloat.measurable_scalarIndex r).comp (hx.prodMk hu)) measurable_const

lemma measurable_compress_joint {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × Seed d => compress k r ρ z.1 z.2) :=
  (DashaQuantization.measurable_reconstruct (d : ℕ) ρ).comp (measurable_compressedIndex_joint k r ρ)

lemma measurable_compress {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Measurable (compress k r ρ x) := by
  exact Measurable.comp
    (g := fun z : EuclideanSpace ℝ (Fin d) × Seed d => compress k r ρ z.1 z.2)
    (f := fun seed : Seed d => (x, seed))
    (measurable_compress_joint k r ρ) (measurable_const.prodMk measurable_id)

lemma coordinate_law_integral {d : ℕ+} (j : Fin d) (g : Fin d → ℝ → ℝ)
    (hm : ∀ shift, Measurable (g shift)) (hi : ∀ shift, Integrable (g shift) (unitLaw : Measure ℝ)) :
    Integrable (fun seed : Seed d => g seed.1 (seed.2 j)) (law d : Measure _) ∧
      (∫ seed : Seed d, g seed.1 (seed.2 j) ∂(law d : Measure _)) =
        (1 / (d : ℝ)) * ∑ shift : Fin d, ∫ u : ℝ, g shift u ∂(unitLaw : Measure ℝ) := by
  have hmeas : Measurable (fun seed : Seed d => g seed.1 (seed.2 j)) :=
    measurable_from_prod_countable_right (fun shift => (hm shift).comp (measurable_pi_apply j))
  have hprod : Integrable (fun seed : Seed d => g seed.1 (seed.2 j))
      ((PMF.uniformOfFintype (Fin d)).toMeasure.prod
        (Measure.pi fun _ : Fin d => (unitLaw : Measure ℝ))) :=
    OracleTemplate.ZerothOrder.finite_prod_integrable hmeas.aestronglyMeasurable
      (fun shift => by
        change Integrable (fun ω : Fin d → ℝ => g shift (ω j))
          (Measure.pi fun _ : Fin d => (unitLaw : Measure ℝ))
        exact integrable_comp_eval (μ := fun _ : Fin d => (unitLaw : Measure ℝ)) (i := j) (hi shift))
  refine ⟨hprod, ?_⟩
  change (∫ seed : Seed d, g seed.1 (seed.2 j)
    ∂((PMF.uniformOfFintype (Fin d)).toMeasure.prod
      (Measure.pi fun _ : Fin d => (unitLaw : Measure ℝ)))) = _
  rw [integral_prod _ hprod, OracleTemplate.ZerothOrder.uniform_integral_explicit]
  simp only [Fintype.card_fin, smul_eq_mul, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro shift _
  exact integral_comp_eval (hi shift).aestronglyMeasurable

lemma coordinate_measurable {d : ℕ+} (k shift j : Fin d) (r : ℕ) (ρ x : ℝ) :
    Measurable (fun u : ℝ => if selected k shift j then rounded r ρ (multiplier k * x) u else 0) := by
  by_cases h : selected k shift j
  · simp only [h, ↓reduceIte]
    exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((DashaFloat.measurable_scalarIndex r).comp (measurable_const.prodMk measurable_id)))
  · simp only [h, ↓reduceIte]
    exact measurable_const

lemma compress_coordinate_moments {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hρ : ρ ≠ 0) (j : Fin d) :
    Integrable (fun seed => compress k r ρ x seed j) (law d : Measure _) ∧
      (∫ seed, compress k r ρ x seed j ∂(law d : Measure _)) = x j ∧
      Integrable (fun seed => (compress k r ρ x seed j - x j) ^ 2) (law d : Measure _) ∧
      (∫ seed, (compress k r ρ x seed j - x j) ^ 2 ∂(law d : Measure _)) ≤
        ((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * (x j) ^ 2 +
          2 * (k.val + 1) / (d : ℝ) * ρ ^ 2 := by
  have h1 := coordinate_law_integral j
    (fun shift u => if selected k shift j then rounded r ρ (multiplier k * x j) u else 0)
    (fun shift => coordinate_measurable k shift j r ρ (x j))
    (fun shift => coordinate_integrable k shift j r ρ (x j))
  have h2 := coordinate_law_integral j
    (fun shift u => ((if selected k shift j then rounded r ρ (multiplier k * x j) u else 0) - x j) ^ 2)
    (fun shift => ((coordinate_measurable k shift j r ρ (x j)).sub_const (x j)).pow_const 2)
    (fun shift => coordinate_error_integrable k shift j r ρ (x j) hρ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [compress_apply] using h1.1
  · simpa only [compress_apply] using h1.2.trans (coordinate_mean k j r ρ (x j) hρ)
  · simpa only [compress_apply] using h2.1
  · simpa only [compress_apply] using h2.2.trans_le (coordinate_variance k j r ρ (x j) hρ)

lemma compress_moments {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hρ : ρ ≠ 0) :
    Integrable (compress k r ρ x) (law d : Measure _) ∧
      (∫ seed, compress k r ρ x seed ∂(law d : Measure _)) = x ∧
      Integrable (fun seed => ‖compress k r ρ x seed - x‖ ^ 2) (law d : Measure _) ∧
      (∫ seed, ‖compress k r ρ x seed - x‖ ^ 2 ∂(law d : Measure _)) ≤
        ((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * ‖x‖ ^ 2 + 2 * (k.val + 1) * ρ ^ 2 := by
  have hc := compress_coordinate_moments k r ρ x hρ
  have hi : Integrable (compress k r ρ x) (law d : Measure _) :=
    Integrable.of_eval_piLp (fun j => (hc j).1)
  have he (seed : Seed d) : ‖compress k r ρ x seed - x‖ ^ 2 =
      ∑ j : Fin d, (compress k r ρ x seed j - x j) ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  refine ⟨hi, ?_, ?_, ?_⟩
  · ext j
    rw [OracleTemplate.ZerothOrder.integral_euclidean_apply hi]
    exact (hc j).2.1
  · simp_rw [he]
    exact integrable_finsetSum _ (fun j _ => (hc j).2.2.1)
  · simp_rw [he]
    rw [integral_finsetSum _ (fun j _ => (hc j).2.2.1)]
    calc
      _ ≤ ∑ j : Fin d, (((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * (x j) ^ 2 +
          2 * (k.val + 1) / (d : ℝ) * ρ ^ 2) :=
        Finset.sum_le_sum (fun j _ => (hc j).2.2.2)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hd : (d : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
        field_simp

lemma independent_compression_errors {d : ℕ+} {n : ℕ} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    ProbabilityTheory.iIndepFun (fun i (seed : Fin n → Seed d) => compress k r ρ (v i) (seed i) - v i)
      (Measure.pi fun _ : Fin n => (law d : Measure _)) :=
  ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => (law d : Measure (Seed d)))
    (X := fun i (seed : Seed d) => compress k r ρ (v i) seed - v i)
    (fun i => ((measurable_compress k r ρ (v i)).sub_const (v i)).aemeasurable)

lemma replicated_error_moments {d : ℕ+} {n : ℕ} (k : Fin d) (r : ℕ) (ρ : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hρ : ρ ≠ 0) (i : Fin n) :
    Integrable (fun seed : Fin n → Seed d => compress k r ρ (v i) (seed i) - v i)
        (Measure.pi fun _ : Fin n => (law d : Measure _)) ∧
      (∫ seed : Fin n → Seed d, compress k r ρ (v i) (seed i) - v i
        ∂Measure.pi (fun _ : Fin n => (law d : Measure _))) = 0 ∧
      Integrable (fun seed : Fin n → Seed d => ‖compress k r ρ (v i) (seed i) - v i‖ ^ 2)
        (Measure.pi fun _ : Fin n => (law d : Measure _)) ∧
      (∫ seed : Fin n → Seed d, ‖compress k r ρ (v i) (seed i) - v i‖ ^ 2
        ∂Measure.pi (fun _ : Fin n => (law d : Measure _))) ≤
        ((1 + 2 / (4 : ℝ) ^ r) * multiplier k - 1) * ‖v i‖ ^ 2 + 2 * (k.val + 1) * ρ ^ 2 := by
  have h := compress_moments k r ρ (v i) hρ
  have hi := h.1.sub (integrable_const (v i))
  change Integrable (fun seed => compress k r ρ (v i) seed - v i) (law d : Measure _) at hi
  have hz : (∫ seed, compress k r ρ (v i) seed - v i ∂(law d : Measure _)) = 0 := by
    rw [integral_sub h.1 (integrable_const _), h.2.1]
    simp
  refine ⟨integrable_comp_eval (X := fun _ : Fin n => Seed d) (μ := fun _ : Fin n => (law d : Measure (Seed d))) (i := i) hi, ?_,
    integrable_comp_eval (X := fun _ : Fin n => Seed d) (μ := fun _ : Fin n => (law d : Measure (Seed d))) (i := i)
      (f := fun seed : Seed d => ‖compress k r ρ (v i) seed - v i‖ ^ 2) h.2.2.1, ?_⟩
  · rw [integral_comp_eval (X := fun _ : Fin n => Seed d) (μ := fun _ : Fin n => (law d : Measure (Seed d))) hi.aestronglyMeasurable, hz]
  · rw [integral_comp_eval (X := fun _ : Fin n => Seed d) (μ := fun _ : Fin n => (law d : Measure (Seed d))) h.2.2.1.aestronglyMeasurable]
    exact h.2.2.2

lemma compress_norm_bound {d : ℕ+} (k : Fin d) (r : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) :
    ‖compress k r ρ x seed‖ ≤ 2 * multiplier k * ‖x‖ + ρ * Real.sqrt (d : ℝ) := by
  let ax : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => |x j|)
  let ones : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun _ => ρ)
  have hq : 0 ≤ multiplier k := by unfold multiplier; positivity
  have hax : ‖ax‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq, ax, sq_abs]
  have hones : ‖ones‖ = ρ * Real.sqrt (d : ℝ) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (by positivity)]
    simp [ones, mul_comm]
  have hc : ‖compress k r ρ x seed‖ ≤ ‖(2 * multiplier k) • ax + ones‖ := by
    apply DashaQuantization.norm_le_of_coordinates
    intro j
    have hj : |((2 * multiplier k) • ax + ones) j| = 2 * multiplier k * |x j| + ρ := by
      change |2 * multiplier k * |x j| + ρ| = _
      rw [abs_of_nonneg (by positivity)]
    rw [hj, compress_apply]
    split_ifs
    · have hb := DashaFloat.rounded_abs_bound r ρ (multiplier k * x j) (seed.2 j) hρ
      rw [abs_mul, abs_of_nonneg hq] at hb
      linarith
    · simp only [abs_zero]
      positivity
  calc
    _ ≤ ‖(2 * multiplier k) • ax + ones‖ := hc
    _ ≤ ‖(2 * multiplier k) • ax‖ + ‖ones‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hax, hones]

end LongTails.Proofs.DashaCompression
