import LongTails.Algorithms.DistributedNormalizedCompression
import LongTails.Proofs.DistributedQuantization
import LongTails.Proofs.DistributedCompressionMoments

namespace LongTails.Proofs.DistributedNormalizedCompression

open LongTails.Algorithms.DistributedNormalizedCompression
open LongTails.Algorithms.DistributedQuantization

lemma sparse_message_length {d : ℕ} (width m : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin m → Fin d) (u : Fin m → ℝ) :
    (sparseMessage width m spacing x j u).length = m * width :=
  DistributedQuantization.encode_length _

lemma sparse_receive_message {d : ℕ} (width m : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin m → Fin d) (u : Fin m → ℝ)
    (padding : List Bool) :
    sparseReceive width m spacing j (sparseMessage width m spacing x j u ++ padding) =
      (m : ℝ)⁻¹ • ∑ q, sparseSample width spacing x (j q) (u q) := by
  unfold sparseReceive sparseMessage
  rw [← DistributedQuantization.encode_length (sparseGrid width m spacing x j u),
    List.take_left, DistributedQuantization.decode_encode]
  rfl

lemma full_receive_message (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) (padding : List Bool) :
    fullReceive d width spacing
      (LongTails.Algorithms.DistributedRandomRounding.message d width spacing x u ++ padding) =
      reconstruct spacing (LongTails.Algorithms.DistributedRandomRounding.grid d width spacing x u) := by
  unfold fullReceive receive LongTails.Algorithms.DistributedRandomRounding.message
  rw [← DistributedQuantization.encode_length
      (LongTails.Algorithms.DistributedRandomRounding.grid d width spacing x u),
    List.take_left, DistributedQuantization.decode_encode]

lemma sparse_sample_norm {d : ℕ} (width : ℕ) {spacing : ℝ} (hs : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) (u : ℝ)
    (hx : |(d : ℝ) * x j| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖sparseSample width spacing x j u‖ ≤ (d : ℝ) * ‖x‖ + spacing := by
  let q := spacing *
    (((LongTails.Algorithms.DistributedRandomRounding.gridIndex width spacing (d * x j) u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2)
  have he : |q - (d : ℝ) * x j| ≤ spacing :=
    DistributedCompressionMoments.encoded_scalar_error width hs _ u hx
  have ht : |q| ≤ |q - (d : ℝ) * x j| + |(d : ℝ) * x j| := by
    simpa using abs_add_le (q - (d : ℝ) * x j) ((d : ℝ) * x j)
  have hc : |(d : ℝ) * x j| ≤ (d : ℝ) * ‖x‖ := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
      (Nat.cast_nonneg d)
  change ‖EuclideanSpace.single j q‖ ≤ _
  rw [PiLp.norm_single, Real.norm_eq_abs]
  linarith

lemma sparse_message_norm {d : ℕ} (width m : ℕ) (hm : 0 < m) {spacing : ℝ}
    (hs : 0 < spacing) (x : EuclideanSpace ℝ (Fin d)) (j : Fin m → Fin d) (u : Fin m → ℝ)
    (padding : List Bool)
    (hx : ∀ i, |(d : ℝ) * x i| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖sparseReceive width m spacing j (sparseMessage width m spacing x j u ++ padding)‖ ≤
      (d : ℝ) * ‖x‖ + spacing := by
  rw [sparse_receive_message, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ q, ‖sparseSample width spacing x (j q) (u q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ ≤ (m : ℝ)⁻¹ * ∑ _q : Fin m, ((d : ℝ) * ‖x‖ + spacing) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun q _ => sparse_sample_norm width hs x (j q) (u q) (hx (j q)))
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      rw [← mul_assoc, inv_mul_cancel₀ hm', one_mul]

lemma full_message_error_sq (d width : ℕ) {spacing : ℝ} (hs : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) (padding : List Bool)
    (hx : ∀ i, |x i| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖fullReceive d width spacing
      (LongTails.Algorithms.DistributedRandomRounding.message d width spacing x u ++ padding) - x‖ ^ 2 ≤
      d * spacing ^ 2 := by
  rw [full_receive_message, EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, spacing ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have he := DistributedCompressionMoments.encoded_scalar_error width hs (x i) (u i) (hx i)
      have hh := pow_le_pow_left₀ (abs_nonneg _) he 2
      change (spacing *
        (((LongTails.Algorithms.DistributedRandomRounding.gridIndex width spacing (x i) (u i)).val : ℝ) -
          ((2 ^ width - 1 : ℕ) : ℝ) / 2) - x i) ^ 2 ≤ spacing ^ 2
      simpa only [sq_abs] using hh
    _ = _ := by simp

end LongTails.Proofs.DistributedNormalizedCompression
