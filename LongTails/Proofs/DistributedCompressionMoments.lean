import LongTails.Proofs.DistributedRandomRounding
import LongTails.Algorithms.DistributedNormalizedCompression
import LongTails.Proofs.CharacteristicGradientBounds

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.DistributedCompressionMoments

open LongTails.Algorithms.DistributedRandomRounding
open LongTails.Algorithms.DistributedQuantization
open LongTails.Proofs.DistributedRandomRounding

lemma uniform_integral_transport {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {u : Ω → ℝ} (hu : MeasurePreserving u P (uniform : Measure ℝ))
    {f : ℝ → ℝ} (hf : Integrable f (uniform : Measure ℝ)) :
    Integrable (fun ω => f (u ω)) P ∧
      (∫ ω, f (u ω) ∂P) = ∫ z, f z ∂(uniform : Measure ℝ) := by
  refine ⟨hu.integrable_comp_of_integrable hf, ?_⟩
  have hm : AEStronglyMeasurable f (P.map u) := hu.map_eq.symm ▸ hf.aestronglyMeasurable
  rw [← integral_map hu.measurable.aemeasurable hm, hu.map_eq]

lemma full_grid_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (d width : ℕ) {spacing : ℝ} (hs : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d)) (u : Ω → Fin d → ℝ)
    (hu : ∀ i, MeasurePreserving (fun ω => u ω i) P (uniform : Measure ℝ))
    (hx : ∀ i, |x i| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let X := fun ω => reconstruct spacing (grid d width spacing x (u ω))
    Integrable X P ∧ (∫ ω, X ω ∂P) = x ∧
      Integrable (fun ω => ‖X ω - x‖ ^ 2) P ∧
      (∫ ω, ‖X ω - x‖ ^ 2 ∂P) ≤ d * spacing ^ 2 / 4 := by
  intro X
  have hc (i : Fin d) : Integrable (fun ω => X ω i) P ∧
      (∫ ω, X ω i ∂P) = x i := by
    obtain ⟨hi, hm⟩ := encoded_scalar_integral width hs (x i) (hx i)
    obtain ⟨hci, hcm⟩ := uniform_integral_transport (hu i) hi
    exact ⟨hci, hcm.trans hm⟩
  have hv (i : Fin d) : Integrable (fun ω => (X ω i - x i) ^ 2) P ∧
      (∫ ω, (X ω i - x i) ^ 2 ∂P) ≤ spacing ^ 2 / 4 := by
    obtain ⟨hi, hm⟩ := encoded_scalar_variance width hs (x i) (hx i)
    obtain ⟨hci, hcm⟩ := uniform_integral_transport (hu i) hi
    exact ⟨hci, hcm.trans_le hm⟩
  have hi : Integrable X P :=
    CharacteristicGradientBounds.integrable_euclidean_of_coordinates fun i => (hc i).1
  have hm : (∫ ω, X ω ∂P) = x := by
    ext i
    rw [OracleTemplate.ZerothOrder.integral_euclidean_apply hi]
    exact (hc i).2
  obtain ⟨hei, he⟩ := CharacteristicGradientBounds.vector_error_second_bound
    (fun i => (hv i).1) (fun i => (hv i).2)
  refine ⟨hi, hm, hei, ?_⟩
  convert he using 1
  ring

lemma coordinate_sum {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    (∑ j : Fin d, EuclideanSpace.single j ((d : ℝ) * x j)) = (d : ℝ) • x := by
  ext i
  simp

lemma coordinate_energy {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    (∑ j : Fin d, ‖EuclideanSpace.single j ((d : ℝ) * x j)‖ ^ 2) =
      (d : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]

lemma coordinate_variance {d : ℕ} (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) :
    (d : ℝ)⁻¹ * ∑ j : Fin d, ‖EuclideanSpace.single j ((d : ℝ) * x j) - x‖ ^ 2 =
      ((d : ℝ) - 1) * ‖x‖ ^ 2 := by
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, coordinate_energy,
    ← Finset.mul_sum, ← sum_inner, coordinate_sum, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  field_simp
  ring

set_option maxHeartbeats 800000 in
lemma measurable_grid (d width : ℕ) (spacing : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
      grid d width spacing z.1 z.2) := by
  change Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
    fun i : Fin d => gridIndex width spacing (z.1 i) (z.2 i))
  apply measurable_pi_iff.mpr
  intro i
  have hx : Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => z.1 i) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).comp measurable_fst
  have hu : Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  change Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
    gridIndex width spacing (z.1 i) (z.2 i))
  exact (measurable_gridIndex width spacing).comp (hx.prodMk hu)

lemma measurable_message [MeasurableSpace (List Bool)] (d width : ℕ) (spacing : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
      LongTails.Algorithms.DistributedRandomRounding.message d width spacing z.1 z.2) := by
  exact (measurable_of_countable encode).comp (measurable_grid d width spacing)

lemma encoded_scalar_error (width : ℕ) {spacing : ℝ} (hs : 0 < spacing) (x u : ℝ)
    (hx : |x| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    |spacing * (((gridIndex width spacing x u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2) - x| ≤ spacing := by
  obtain ⟨h0, hcap⟩ := grid_capacity_of_abs width hs x hx
  rw [gridIndex_reconstruction width hs.ne' x u h0 hcap]
  have he : scalar spacing (x + spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2)) u -
      spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2) - x =
      scalar spacing (x + spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2)) u -
        (x + spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2)) := by ring
  rw [he]
  exact scalar_error hs _ u

lemma single_scalar_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} (j : Fin d) (x : EuclideanSpace ℝ (Fin d))
    (q : Ω → ℝ) (a v : ℝ) (hi : Integrable q P)
    (hm : (∫ ω, q ω ∂P) = a)
    (h2 : Integrable (fun ω => (q ω - a) ^ 2) P)
    (hv : (∫ ω, (q ω - a) ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖EuclideanSpace.single j (q ω) - x‖ ^ 2) P ∧
      (∫ ω, ‖EuclideanSpace.single j (q ω) - x‖ ^ 2 ∂P) ≤
        v + ‖EuclideanSpace.single j a - x‖ ^ 2 := by
  have he (ω : Ω) : ‖EuclideanSpace.single j (q ω) - x‖ ^ 2 =
      (q ω - a) ^ 2 + 2 * (a - x j) * (q ω - a) +
        ‖EuclideanSpace.single j a - x‖ ^ 2 := by
    simp only [norm_sub_sq_real, PiLp.norm_single, Real.norm_eq_abs, sq_abs,
      EuclideanSpace.inner_single_left, conj_trivial]
    ring
  have hz : Integrable (fun ω => q ω - a) P := hi.sub (integrable_const a)
  have hzm : (∫ ω, q ω - a ∂P) = 0 := by
    rw [integral_sub hi (integrable_const a), hm]
    simp
  have hl : Integrable (fun ω => 2 * (a - x j) * (q ω - a)) P := hz.const_mul _
  have hsum : Integrable (fun ω => (q ω - a) ^ 2 + 2 * (a - x j) * (q ω - a)) P :=
    h2.add hl
  have hc : Integrable (fun _ : Ω => ‖EuclideanSpace.single j a - x‖ ^ 2) P := integrable_const _
  simp_rw [he]
  refine ⟨hsum.add hc, ?_⟩
  rw [integral_add hsum hc, integral_add h2 hl, integral_const_mul, hzm]
  simpa using add_le_add_right hv (‖EuclideanSpace.single j a - x‖ ^ 2)

lemma single_scalar_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} (j : Fin d) (q : Ω → ℝ) (a : ℝ) (hi : Integrable q P)
    (hm : (∫ ω, q ω ∂P) = a) :
    Integrable (fun ω => EuclideanSpace.single j (q ω)) P ∧
      (∫ ω, EuclideanSpace.single j (q ω) ∂P) = EuclideanSpace.single j a := by
  have he (z : ℝ) : EuclideanSpace.single j z = z • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp
  have hf : (fun ω => EuclideanSpace.single j (q ω)) =
      (fun ω => q ω • EuclideanSpace.single j (1 : ℝ)) := funext fun ω => he (q ω)
  simp only [hf]
  refine ⟨hi.smul_const _, ?_⟩
  rw [integral_smul_const, hm, ← he a]

lemma sparse_fixed_coordinate_moments {d : ℕ} (width : ℕ) {spacing : ℝ}
    (hs : 0 < spacing) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hx : |(d : ℝ) * x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let X := LongTails.Algorithms.DistributedNormalizedCompression.sparseSample width spacing x j
    Integrable X (uniform : Measure ℝ) ∧
      (∫ u, X u ∂(uniform : Measure ℝ)) = EuclideanSpace.single j ((d : ℝ) * x j) ∧
      Integrable (fun u => ‖X u - x‖ ^ 2) (uniform : Measure ℝ) ∧
      (∫ u, ‖X u - x‖ ^ 2 ∂(uniform : Measure ℝ)) ≤
        spacing ^ 2 / 4 + ‖EuclideanSpace.single j ((d : ℝ) * x j) - x‖ ^ 2 := by
  intro X
  obtain ⟨hi, hm⟩ := encoded_scalar_integral width hs ((d : ℝ) * x j) hx
  obtain ⟨h2, hv⟩ := encoded_scalar_variance width hs ((d : ℝ) * x j) hx
  obtain ⟨hXi, hXm⟩ := single_scalar_integral j _ _ hi hm
  obtain ⟨hEi, hEv⟩ := single_scalar_error j x _ _ _ hi hm h2 hv
  exact ⟨hXi, hXm, hEi, hEv⟩

end LongTails.Proofs.DistributedCompressionMoments
