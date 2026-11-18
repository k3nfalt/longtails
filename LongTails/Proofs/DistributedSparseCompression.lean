import LongTails.Proofs.DistributedCompressionMoments
import LongTails.Proofs.DistributedNormalizedCompression
import LongTails.Proofs.ZerothOrderGridEstimator
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory

namespace LongTails.Proofs.DistributedSparseCompression

open LongTails.Algorithms.DistributedNormalizedCompression
open LongTails.Algorithms.DistributedRandomRounding
open DistributedCompressionMoments
open DistributedRandomRounding

lemma measurable_single {d : ℕ} (j : Fin d) :
    Measurable (fun z : ℝ => EuclideanSpace.single j z) := by
  have he : (fun z : ℝ => EuclideanSpace.single j z) =
      (fun z : ℝ => z • EuclideanSpace.single j (1 : ℝ)) := by
    funext z
    ext i
    simp
  rw [he]
  exact measurable_id.smul_const _

set_option maxHeartbeats 800000 in
lemma measurable_sparse_sample {d : ℕ} (width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun z : Fin d × ℝ => sparseSample width spacing x z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro j
  have hq : Measurable (fun u : ℝ =>
      spacing * (((gridIndex width spacing (d * x j) u).val : ℝ) -
        ((2 ^ width - 1 : ℕ) : ℝ) / 2)) :=
    (measurable_of_countable (fun v : Fin (2 ^ width) =>
      spacing * ((v.val : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2))).comp
      ((measurable_gridIndex width spacing).comp (measurable_const.prodMk measurable_id))
  exact (measurable_single j).comp hq

lemma sparse_sample_moments {d : ℕ} [Nonempty (Fin d)] (width : ℕ) {spacing : ℝ}
    (hs : 0 < spacing) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j, |(d : ℝ) * x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (PMF.uniformOfFintype (Fin d)).toMeasure.prod (uniform : Measure ℝ)
    let X := fun z : Fin d × ℝ => sparseSample width spacing x z.1 z.2
    Integrable X P ∧ (∫ z, X z ∂P) = x ∧
      Integrable (fun z => ‖X z - x‖ ^ 2) P ∧
      (∫ z, ‖X z - x‖ ^ 2 ∂P) ≤ ((d : ℝ) - 1) * ‖x‖ ^ 2 + spacing ^ 2 / 4 := by
  intro P X
  have hd : 0 < d := Fintype.card_pos_iff.mpr inferInstance |>.trans_eq (Fintype.card_fin d)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hc (j : Fin d) := sparse_fixed_coordinate_moments width hs x j (hx j)
  have hXm : Measurable X := measurable_sparse_sample width spacing x
  have hi : Integrable X P := OracleTemplate.ZerothOrder.finite_prod_integrable
    hXm.aestronglyMeasurable (fun j => (hc j).1)
  have hei : Integrable (fun z => ‖X z - x‖ ^ 2) P :=
    OracleTemplate.ZerothOrder.finite_prod_integrable
      ((hXm.sub_const x).norm.pow_const 2).aestronglyMeasurable (fun j => (hc j).2.2.1)
  have hm : (∫ z, X z ∂P) = x := by
    rw [integral_prod _ hi]
    simp_rw [show ∀ j : Fin d, (∫ u, X (j, u) ∂(uniform : Measure ℝ)) =
      EuclideanSpace.single j ((d : ℝ) * x j) from fun j => (hc j).2.1]
    rw [OracleTemplate.ZerothOrder.uniform_integral_explicit, Fintype.card_fin,
      coordinate_sum, smul_smul, inv_mul_cancel₀ hd', one_smul]
  refine ⟨hi, hm, hei, ?_⟩
  rw [integral_prod _ hei]
  calc
    _ ≤ ∫ j, (spacing ^ 2 / 4 + ‖EuclideanSpace.single j ((d : ℝ) * x j) - x‖ ^ 2)
        ∂(PMF.uniformOfFintype (Fin d)).toMeasure :=
      integral_mono Integrable.of_finite Integrable.of_finite (fun j => (hc j).2.2.2)
    _ = _ := by
      rw [OracleTemplate.ZerothOrder.uniform_integral_explicit]
      simp only [Fintype.card_fin, smul_eq_mul, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add]
      rw [coordinate_variance hd x]
      field_simp
      ring

lemma sparse_message_moments {d : ℕ} [Nonempty (Fin d)] (width m : ℕ) (hm : 0 < m)
    {spacing : ℝ} (hs : 0 < spacing) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j, |(d : ℝ) * x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (PMF.uniformOfFintype (Fin d)).toMeasure.prod (uniform : Measure ℝ)
    let Y := fun ξ : Fin m → Fin d × ℝ => sparseReceive width m spacing
      (fun q => (ξ q).1) (sparseMessage width m spacing x (fun q => (ξ q).1) (fun q => (ξ q).2))
    Integrable Y (Measure.pi fun _ : Fin m => P) ∧
      (∫ ξ, Y ξ ∂Measure.pi (fun _ : Fin m => P)) = x ∧
      Integrable (fun ξ => ‖Y ξ - x‖ ^ 2) (Measure.pi fun _ : Fin m => P) ∧
      (∫ ξ, ‖Y ξ - x‖ ^ 2 ∂Measure.pi (fun _ : Fin m => P)) ≤
        (((d : ℝ) - 1) * ‖x‖ ^ 2 + spacing ^ 2 / 4) / m := by
  intro P Y
  let X := fun z : Fin d × ℝ => sparseSample width spacing x z.1 z.2
  have hY : Y = (fun ξ : Fin m → Fin d × ℝ => (1 / (m : ℝ)) • ∑ q, X (ξ q)) := by
    funext ξ
    simpa only [Y, X, List.append_nil, one_div] using
      DistributedNormalizedCompression.sparse_receive_message width m spacing x
        (fun q => (ξ q).1) (fun q => (ξ q).2) []
  obtain ⟨hi, hmean, h2, hv⟩ := sparse_sample_moments width hs x hx
  obtain ⟨hYi, hYm⟩ := OracleTemplate.LightTail.finite_mean_integral hi m hm
  obtain ⟨hY2, hYv⟩ := OracleTemplate.RobustGradient.finite_mean_variance
    (measurable_sparse_sample width spacing x) hi x h2 hmean m hm
  rw [hY]
  exact ⟨hYi, hYm.trans hmean, hY2,
    hYv.trans_le (div_le_div_of_nonneg_right hv (Nat.cast_nonneg m))⟩

set_option maxHeartbeats 800000 in
lemma measurable_sparse_sample_joint {d : ℕ} (width : ℕ) (spacing : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d × ℝ) =>
      sparseSample width spacing z.1 z.2.1 z.2.2) := by
  have hc : Measurable (fun z : Fin d × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      sparseSample width spacing z.2.1 z.1 z.2.2) := by
    apply measurable_from_prod_countable_right
    intro j
    have hx : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ => (d : ℝ) * z.1 j) :=
      (((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).comp
        measurable_fst).const_mul _
    have hq : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ =>
        spacing * (((gridIndex width spacing ((d : ℝ) * z.1 j) z.2).val : ℝ) -
          ((2 ^ width - 1 : ℕ) : ℝ) / 2)) :=
      (measurable_of_countable (fun v : Fin (2 ^ width) =>
        spacing * ((v.val : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2))).comp
        ((measurable_gridIndex width spacing).comp (hx.prodMk measurable_snd))
    exact (measurable_single j).comp hq
  exact hc.comp ((measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

set_option maxHeartbeats 800000 in
lemma measurable_sparse_message_joint {d : ℕ} (width m : ℕ) (spacing : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin m → Fin d × ℝ) =>
      sparseReceive width m spacing (fun q => (z.2 q).1)
        (sparseMessage width m spacing z.1 (fun q => (z.2 q).1) (fun q => (z.2 q).2))) := by
  have he : (fun z : EuclideanSpace ℝ (Fin d) × (Fin m → Fin d × ℝ) =>
      sparseReceive width m spacing (fun q => (z.2 q).1)
        (sparseMessage width m spacing z.1 (fun q => (z.2 q).1) (fun q => (z.2 q).2))) =
      (fun z => (m : ℝ)⁻¹ • ∑ q, sparseSample width spacing z.1 (z.2 q).1 (z.2 q).2) := by
    funext z
    simpa only [List.append_nil] using DistributedNormalizedCompression.sparse_receive_message
      width m spacing z.1 (fun q => (z.2 q).1) (fun q => (z.2 q).2) []
  rw [he]
  have ht (q : Fin m) : Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin m → Fin d × ℝ) =>
      sparseSample width spacing z.1 (z.2 q).1 (z.2 q).2) :=
    (measurable_sparse_sample_joint width spacing).comp
      (measurable_fst.prodMk ((measurable_pi_apply q).comp measurable_snd))
  exact (Finset.measurable_sum Finset.univ (fun q _ => ht q)).fun_const_smul _

set_option maxHeartbeats 800000 in
lemma measurable_full_message_joint (d width : ℕ) (spacing : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
      fullReceive d width spacing
        (LongTails.Algorithms.DistributedRandomRounding.message d width spacing z.1 z.2)) := by
  have he : (fun z : EuclideanSpace ℝ (Fin d) × (Fin d → ℝ) =>
      fullReceive d width spacing
        (LongTails.Algorithms.DistributedRandomRounding.message d width spacing z.1 z.2)) =
      (fun z => LongTails.Algorithms.DistributedQuantization.reconstruct spacing
        (grid d width spacing z.1 z.2)) := by
    funext z
    simpa only [List.append_nil] using DistributedNormalizedCompression.full_receive_message
      d width spacing z.1 z.2 []
  rw [he]
  exact (measurable_of_countable (LongTails.Algorithms.DistributedQuantization.reconstruct spacing)).comp
    (measurable_grid d width spacing)

end LongTails.Proofs.DistributedSparseCompression
