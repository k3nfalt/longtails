import LongTails.Proofs.SpectralGradient
import LongTails.Proofs.SpectralGradientModel

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma nonlinear_sweep_error (g : E → E) (H : E →ₗ[ℝ] E) {K b c : ℝ}
    (hK : 0 ≤ K) (hb : 1 ≤ b) (hKb : K ≤ b) (hc : 0 ≤ c) (rs : List ℝ)
    (hgrowth : ∀ η ∈ rs, ∀ x, ‖g (x - η • g x)‖ ≤ b * ‖g x‖)
    (hlin : ∀ η ∈ rs, ∀ x, ‖x - η • H x‖ ≤ K * ‖x‖)
    (hrem : ∀ η ∈ rs, ∀ x,
      ‖g (x - η • g x) - (g x - η • H (g x))‖ ≤ c * b * ‖g x‖ ^ 2) (x : E) :
    ‖g (gradientSteps g rs x) - sweep (LinearMap.id - H) rs (g x)‖ ≤
      (rs.length : ℝ) * c * b ^ (2 * rs.length) * ‖g x‖ ^ 2 := by
  have hb0 : 0 ≤ b := by linarith
  induction rs generalizing x with
  | nil => simp [gradientSteps, sweep]
  | cons η rs ih =>
    have ht (r : ℝ) (hr : r ∈ rs) : r ∈ η :: rs := by simp [hr]
    have hη : η ∈ η :: rs := by simp
    let y := x - η • g x
    have he : g (gradientSteps g (η :: rs) x) -
        sweep (LinearMap.id - H) (η :: rs) (g x) =
        (g (gradientSteps g rs y) - sweep (LinearMap.id - H) rs (g y)) +
        sweep (LinearMap.id - H) rs (g y - (g x - η • H (g x))) := by
      rw [sweep_descent_cons]
      simp only [map_sub]
      change g (gradientSteps g rs y) - _ = _
      abel
    have htail := ih (fun r hr => hgrowth r (ht r hr))
      (fun r hr => hlin r (ht r hr)) (fun r hr => hrem r (ht r hr)) y
    have hn := sweep_descent_norm H hK rs (fun r hr => hlin r (ht r hr))
      (g y - (g x - η • H (g x)))
    have hfirst : ‖g (gradientSteps g rs y) - sweep (LinearMap.id - H) rs (g y)‖ ≤
        (rs.length : ℝ) * c * b ^ (2 * rs.length) * (b * ‖g x‖) ^ 2 := by
      apply htail.trans
      gcongr
      exact hgrowth η hη x
    have hsecond : ‖sweep (LinearMap.id - H) rs (g y - (g x - η • H (g x)))‖ ≤
        K ^ rs.length * (c * b * ‖g x‖ ^ 2) :=
      hn.trans (mul_le_mul_of_nonneg_left (hrem η hη x) (pow_nonneg hK _))
    have hp : K ^ rs.length * b ≤ b ^ (2 * (rs.length + 1)) := by
      calc
        _ ≤ b ^ rs.length * b := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hK hKb _) hb0
        _ = b ^ (rs.length + 1) := (pow_succ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ hb (by omega)
    have hs : K ^ rs.length * (c * b * ‖g x‖ ^ 2) ≤
        c * b ^ (2 * (rs.length + 1)) * ‖g x‖ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg hc (sq_nonneg ‖g x‖))
      nlinarith only [hh]
    rw [he]
    calc
      _ ≤ ‖g (gradientSteps g rs y) - sweep (LinearMap.id - H) rs (g y)‖ +
          ‖sweep (LinearMap.id - H) rs (g y - (g x - η • H (g x)))‖ := norm_add_le _ _
      _ ≤ (rs.length : ℝ) * c * b ^ (2 * rs.length) * (b * ‖g x‖) ^ 2 +
          c * b ^ (2 * (rs.length + 1)) * ‖g x‖ ^ 2 :=
        add_le_add hfirst (hsecond.trans hs)
      _ = _ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
          Nat.mul_add, Nat.mul_one, pow_add, mul_pow]
        ring

end OracleTemplate.SpectralGradient
