import LongTails.Proofs.PLHessianStep

namespace OracleTemplate.RobustPLPotential

lemma fourth_cost {η lam L Q V t : ℝ} (ht : 0 < t)
    (hQ : 4 * lam * L ^ 2 * η ^ 2 * Q ≤ t * V) :
    4 * lam * L ^ 2 * η ^ 4 * Q / t ≤ η ^ 2 * V := by
  rw [div_le_iff₀ ht]
  have := mul_le_mul_of_nonneg_left hQ (sq_nonneg η)
  nlinarith

lemma distance_bias {η Φ μ B d g : ℝ} (hη : 0 ≤ η) (hμ : 0 < μ)
    (hbound : μ * (d + η * g) ^ 2 ≤ 36 * Φ) :
    2 * η * (d + η * g) * B ≤ η * Φ / 8 + 288 * η * B ^ 2 / μ := by
  have h := sq_nonneg (μ * (d + η * g) - 288 * B)
  have hscaled := mul_le_mul_of_nonneg_left hbound hμ.le
  have hbase : 2 * (d + η * g) * B ≤ Φ / 8 + 288 * B ^ 2 / μ := by
    rw [add_comm (Φ / 8), ← sub_le_iff_le_add, le_div_iff₀ hμ]
    nlinarith
  convert mul_le_mul_of_nonneg_left hbase hη using 1 <;> ring

set_option maxHeartbeats 1000000 in
lemma deterministic_drift {η μ L Φ D s lam c H I G r : ℝ}
    (hη : 0 < η) (hμ : 0 < μ) (hΦ : 0 ≤ Φ)
    (hs : 1 ≤ s) (hlam : lam * μ = 32 * s) (hlam0 : 0 ≤ lam)
    (hD : μ * D ≤ 16 * Φ) (hc : 0 ≤ c)
    (hG : 2 * μ * Φ ≤ G) (hG' : G ≤ 2 * L * Φ)
    (hstep : 8 * L * η ≤ 1) (hsmall : 32 * s * η ^ 2 * L ^ 2 ≤ 1)
    (hH : H ≤ c * Φ + r)
    (hcase : (Φ ≤ I ∧ r ≤ 4 * η ^ 2 * L ^ 2 * Φ) ∨
      (-6 * s * Φ ≤ I ∧ c = 1 ∧ H ≤ Φ)) :
    -2 * η * I + η ^ 2 * G - 3 / 8 * lam * c * η * G + 3 / 8 * η * Φ ≤
      -(μ * η / 64) * (D + lam * H) - η * Φ / 2 := by
  have hηG : η ^ 2 * G ≤ η * Φ / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hG' (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_right hstep (mul_nonneg hη.le hΦ)
    nlinarith
  have hcontractD : μ * η / 64 * D ≤ η * Φ / 4 := by
    have := mul_le_mul_of_nonneg_left hD (show 0 ≤ η / 64 by positivity)
    nlinarith
  have hgain : 3 / 4 * lam * c * μ * η * Φ ≤ 3 / 8 * lam * c * η * G := by
    have := mul_le_mul_of_nonneg_left hG (show 0 ≤ 3 / 8 * lam * c * η by positivity)
    nlinarith
  rcases hcase with ⟨hI, hr⟩ | ⟨hI, hc1, hHF⟩
  · have hR : μ * η / 64 * lam * r ≤ η * Φ / 16 := by
      have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ μ * η / 64 * lam by positivity)
      have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ η * Φ by positivity)
      have he : μ * η / 64 * lam * (4 * η ^ 2 * L ^ 2 * Φ) =
          2 * s * η ^ 3 * L ^ 2 * Φ := by
        calc
          _ = (lam * μ) * (η ^ 3 * L ^ 2 * Φ / 16) := by ring
          _ = _ := by rw [hlam]; ring
      nlinarith
    have hcontractH : μ * η / 64 * lam * H ≤ μ * η / 64 * lam * c * Φ + η * Φ / 16 := by
      have := mul_le_mul_of_nonneg_left hH (show 0 ≤ μ * η / 64 * lam by positivity)
      nlinarith
    have hIη := mul_le_mul_of_nonneg_left hI hη.le
    have hcn : 0 ≤ lam * c * μ * η * Φ := by positivity
    nlinarith [hgain]
  · have hcontractH : μ * η / 64 * lam * H ≤ s * η * Φ / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hHF (show 0 ≤ μ * η / 64 * lam by positivity)
      have he : μ * η / 64 * lam * Φ = s * η * Φ / 2 := by
        calc
          _ = (lam * μ) * (η * Φ / 64) := by ring
          _ = _ := by rw [hlam]; ring
      linarith
    have hgain' : 24 * s * η * Φ ≤ 3 / 8 * lam * c * η * G := by
      have he : 3 / 4 * lam * c * μ * η * Φ = 24 * s * η * Φ := by
        rw [hc1]
        calc
          _ = (lam * μ) * (3 * η * Φ / 4) := by ring
          _ = _ := by rw [hlam]; ring
      linarith
    have hIη := mul_le_mul_of_nonneg_left hI hη.le
    have hsΦ := mul_le_mul_of_nonneg_right hs (show 0 ≤ η * Φ by positivity)
    nlinarith

lemma variance_cost {η lam L V t c Φ G : ℝ} (hη : 0 ≤ η) (hlam : 0 ≤ lam)
    (hL : 0 ≤ L) (hV : 0 ≤ V) (ht : 0 < t) (hΦ : 0 ≤ Φ)
    (hc : c * t ≤ 4 * Φ) (hG : G ≤ 2 * L * Φ)
    (hsmall : 96 * lam * L * η * V ≤ t) :
    lam * c * L * η ^ 2 * V + 4 * lam * η ^ 2 * G * V / t ≤ η * Φ / 8 := by
  have h1 := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ lam * L * η ^ 2 * V by positivity)
  have h2 := mul_le_mul_of_nonneg_left hG
    (show 0 ≤ 4 * lam * η ^ 2 * V by positivity)
  have h3 := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ η * Φ by positivity)
  rw [add_comm (lam * c * L * η ^ 2 * V), ← le_sub_iff_add_le, div_le_iff₀ ht]
  nlinarith

lemma gradient_bias {η lam B t c Φ g : ℝ} (hη : 0 ≤ η) (hlam : 0 ≤ lam)
    (hc0 : 0 ≤ c) (ht : 0 < t) (hΦ : 0 ≤ Φ)
    (hc : c * t ≤ 4 * Φ) (hsmall : 64 * lam * B ^ 2 ≤ t) :
    lam * c * η * g * B ≤ lam * c * η * g ^ 2 / 8 + η * Φ / 8 := by
  have hy : g * B ≤ g ^ 2 / 8 + 2 * B ^ 2 := by nlinarith [sq_nonneg (g - 4 * B)]
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ lam * c * η by positivity)
  have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * lam * η * B ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ η * Φ by positivity)
  have hb : 2 * lam * c * η * B ^ 2 ≤ η * Φ / 8 := by
    nlinarith
  nlinarith

lemma assembled_step {η μ L Φ D s lam c H I G r V Q B t Wnext : ℝ}
    (hη : 0 < η) (hμ : 0 < μ) (hL : 0 ≤ L) (hΦ : 0 ≤ Φ)
    (hs : 1 ≤ s) (hlam : lam * μ = 32 * s) (hlam0 : 0 ≤ lam)
    (hD : μ * D ≤ 16 * Φ) (hc : 0 ≤ c)
    (hG : 2 * μ * Φ ≤ G) (hG' : G ≤ 2 * L * Φ)
    (hstep : 8 * L * η ≤ 1) (hsmall : 32 * s * η ^ 2 * L ^ 2 ≤ 1)
    (hH : H ≤ c * Φ + r)
    (hcase : (Φ ≤ I ∧ r ≤ 4 * η ^ 2 * L ^ 2 * Φ) ∨
      (-6 * s * Φ ≤ I ∧ c = 1 ∧ H ≤ Φ))
    (ht : 0 < t) (hV : 0 ≤ V) (hct : c * t ≤ 4 * Φ)
    (hVsmall : 96 * lam * L * η * V ≤ t)
    (hQ : 4 * lam * L ^ 2 * η ^ 2 * Q ≤ t * V)
    (hB : B ^ 2 ≤ μ * η * V)
    (hraw : Wnext ≤ D + lam * H - 2 * η * I + η ^ 2 * G -
      3 / 8 * lam * c * η * G + η * Φ / 4 + 288 * η * B ^ 2 / μ +
      η ^ 2 * V + lam * c * L * η ^ 2 * V + 4 * lam * η ^ 2 * G * V / t +
      4 * lam * L ^ 2 * η ^ 4 * Q / t) :
    Wnext ≤ (1 - μ * η / 64) * (D + lam * H) - η * Φ / 2 + 290 * η ^ 2 * V := by
  have hd := deterministic_drift hη hμ hΦ hs hlam hlam0 hD hc hG hG' hstep hsmall hH hcase
  have hv := variance_cost hη.le hlam0 hL hV ht hΦ hct hG' hVsmall
  have hq := fourth_cost ht hQ
  have hb : 288 * η * B ^ 2 / μ ≤ 288 * η ^ 2 * V := by
    rw [div_le_iff₀ hμ]
    have := mul_le_mul_of_nonneg_left hB (show 0 ≤ 288 * η by positivity)
    nlinarith
  linarith

end OracleTemplate.RobustPLPotential
