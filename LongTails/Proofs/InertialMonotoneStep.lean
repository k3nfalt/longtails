import LongTails.Proofs.ClippedExtragradientStability

open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma extragradient_contract {η μ K : ℝ} (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * K ^ 2 ≤ 1) (z p g q ξ ζ : E)
    (hm : μ * ‖z - η • g - p‖ ^ 2 ≤ ⟪q, z - η • g - p⟫)
    (he : ‖q - g‖ ^ 2 ≤ 2 * K ^ 2 * ‖η • g‖ ^ 2 + 2 * ‖ξ‖ ^ 2) :
    ‖z - η • (q + ζ) - p‖ ^ 2 ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 2 * η ^ 2 * ‖ξ‖ ^ 2 +
        η ^ 2 * ‖ζ‖ ^ 2 - 2 * η * ⟪ζ, z - η • q - p⟫ := by
  rw [ClippedExtragradient.extragradient_identity]
  have h1 := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * η by positivity)
  have h2 := mul_le_mul_of_nonneg_left he (sq_nonneg η)
  have h3 := mul_le_mul_of_nonneg_left
    (ClippedExtragradient.distance_split z p (η • g)) (mul_nonneg hη hμ)
  have h4 := mul_nonneg (sq_nonneg ‖η • g‖)
    (show 0 ≤ 1 - 2 * η * μ - 2 * η ^ 2 * K ^ 2 by linarith)
  nlinarith

lemma extragradient_local_error {K : ℝ}
    (η : ℝ) (hz hy ξ : E)
    (hlip : ‖hy - hz‖ ≤ K * ‖η • (hz + ξ)‖) :
    ‖hy - (hz + ξ)‖ ^ 2 ≤
      2 * K ^ 2 * ‖η • (hz + ξ)‖ ^ 2 + 2 * ‖ξ‖ ^ 2 := by
  have he : hy - (hz + ξ) = (hy - hz) - ξ := by abel
  have ht := norm_sub_le (hy - hz) ξ
  rw [← he] at ht
  have hbound : ‖hy - (hz + ξ)‖ ≤ K * ‖η • (hz + ξ)‖ + ‖ξ‖ := by linarith
  have hs := sq_nonneg (K * ‖η • (hz + ξ)‖ - ‖ξ‖)
  have hn := norm_nonneg (hy - (hz + ξ))
  have hh := mul_self_le_mul_self hn hbound
  nlinarith

lemma corrected_contraction {r μ v a b : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ 1 / 16)
    (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hstep : μ ^ 2 * b ≤ (1 - 2 * r) * μ ^ 2 * a + 12 * r ^ 2 * v) :
    μ ^ 2 * (1 + r) ^ 2 * b ≤ μ ^ 2 * a + 14 * r ^ 2 * v := by
  have hh := mul_le_mul_of_nonneg_left hstep (sq_nonneg (1 + r))
  have hc : (1 + r) ^ 2 * (1 - 2 * r) ≤ 1 := by
    nlinarith [mul_nonneg hr (sq_nonneg r)]
  have hn : 12 * (1 + r) ^ 2 ≤ 14 := by nlinarith
  have hca := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg μ) ha)
  have hnv := mul_le_mul_of_nonneg_right hn (mul_nonneg (sq_nonneg r) hv)
  nlinarith only [hh, hca, hnv]

end OracleTemplate.InertialMonotone
