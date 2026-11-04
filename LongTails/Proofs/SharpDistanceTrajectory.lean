import LongTails.Proofs.SharpDistanceEnergy

namespace LongTails.Proofs.SharpDistanceTrajectory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma filter_radius (x z : ℕ → E) {A c B C ρ : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) (hAρ : A ≤ ρ ^ 2)
    (hinit : x 0 = z 0) (hz : ∀ k, ‖z k‖ ≤ B + C * ρ ^ k)
    (hrec : ∀ k, x (k + 1) - c • z (k + 1) =
      A • (x k - c • z k) + ((1 - A) * (1 - c)) • z k) :
    ∀ n, ‖x n‖ ≤ B + 3 * C * ρ ^ n := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hA1 : A ≤ 1 := by nlinarith
  have hcoef : 3 * A + (1 - A) ≤ 3 * ρ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) (show 0 ≤ 2 * ρ - 1 by linarith)]
  have hw : ∀ n, ‖x n - c • z n‖ ≤ (1 - c) * (B + 3 * C * ρ ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [hinit]
      have he : z 0 - c • z 0 = (1 - c) • z 0 := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1)]
      have hh := mul_le_mul_of_nonneg_left (hz 0) (sub_nonneg.mpr hc1)
      simp only [pow_zero, mul_one] at hh ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hC]
    | succ n ih =>
      rw [hrec]
      have ht := norm_add_le (A • (x n - c • z n)) (((1 - A) * (1 - c)) • z n)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hA,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hc1))] at ht
      have hi := mul_le_mul_of_nonneg_left ih hA
      have hj := mul_le_mul_of_nonneg_left (hz n)
        (mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hc1))
      have hk := mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ (1 - c) * C * ρ ^ n by positivity)
      rw [pow_succ]
      nlinarith only [ht, hi, hj, hk]
  intro n
  have he : x n = c • z n + (x n - c • z n) := by abel
  have ht := norm_add_le (c • z n) (x n - c • z n)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at ht
  have hj := mul_le_mul_of_nonneg_left (hz n) hc
  have hi := hw n
  have hp : 0 ≤ c * C * ρ ^ n := by positivity
  nlinarith only [ht, hj, hi, hp]

lemma geometric_energy (V : ℕ → ℝ) {θ F : ℝ}
    (hθ1 : θ ≤ 1) (hF : 0 ≤ F)
    (hstep : ∀ n, V (n + 1) ≤ (1 - θ) * V n + θ * F) :
    ∀ n, V n ≤ (1 - θ) ^ n * V 0 + F := by
  intro n
  induction n with
  | zero => simpa using hF
  | succ n ih =>
      have hi := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hθ1)
      have hs := hstep n
      rw [pow_succ]
      nlinarith only [hi, hs]

omit [NormedSpace ℝ E] in
lemma energy_radius {μ V B C : ℝ} {z : E} (hμ : 0 < μ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hz : μ / 2 * ‖z‖ ^ 2 ≤ V) (hV : V ≤ μ / 2 * (B ^ 2 + C ^ 2)) :
    ‖z‖ ≤ B + C := by
  have hs : ‖z‖ ^ 2 ≤ B ^ 2 + C ^ 2 := by nlinarith
  nlinarith [norm_nonneg z, mul_nonneg hB hC]

end LongTails.Proofs.SharpDistanceTrajectory
