import LongTails.Algorithms.TemporalAccelerated
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace OracleTemplate.TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma squared_mix (a b : E) (θ : ℝ) :
    ‖(1 - θ) • a + θ • b‖ ^ 2 =
      (1 - θ) * ‖a‖ ^ 2 + θ * ‖b‖ ^ 2 - θ * (1 - θ) * ‖a - b‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right]
  ring

lemma accelerated_energy_step {f : E → ℝ} {μ θ : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (x z u g : E)
    (hx : f (acceleratedQuery θ (x, z)) +
      ⟪g, x - acceleratedQuery θ (x, z)⟫ +
        μ / 2 * ‖x - acceleratedQuery θ (x, z)‖ ^ 2 ≤ f x)
    (hu : f (acceleratedQuery θ (x, z)) +
      ⟪g, u - acceleratedQuery θ (x, z)⟫ +
        μ / 2 * ‖u - acceleratedQuery θ (x, z)‖ ^ 2 ≤ f u)
    (hd : f (acceleratedUpdate θ μ (x, z) g).1 ≤
      f (acceleratedQuery θ (x, z)) - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2) :
    f (acceleratedUpdate θ μ (x, z) g).1 - f u +
        μ / 2 * ‖(acceleratedUpdate θ μ (x, z) g).2 - u‖ ^ 2 ≤
      (1 - θ) * (f x - f u + μ / 2 * ‖z - u‖ ^ 2) := by
  let y := acceleratedQuery θ (x, z)
  let v := (1 - θ) • (z - u) + θ • (y - u)
  have hden : 1 + θ ≠ 0 := by positivity
  have hi : (1 - θ) • (x - y) + θ • (u - y) = -θ • v := by
    dsimp [v, y, acceleratedQuery]
    match_scalars
    all_goals field_simp; ring
  have hip := congrArg (fun w => ⟪g, w⟫) hi
  simp only [inner_add_right, inner_smul_right] at hip
  have hm := squared_mix (z - u) (y - u) θ
  have hz : (acceleratedUpdate θ μ (x, z) g).2 - u = v - (θ / μ) • g := by
    dsimp [acceleratedUpdate, v, y]
    module
  rw [hz, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm v g]
  have hcancel : μ / 2 * (‖v‖ ^ 2 - 2 * ((θ / μ) * ⟪g, v⟫) +
      (θ / μ) ^ 2 * ‖g‖ ^ 2) =
      μ / 2 * ‖v‖ ^ 2 + θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 - θ * ⟪g, v⟫ := by
    field_simp
    ring
  rw [hcancel]
  have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hθ1)
  have hu' := mul_le_mul_of_nonneg_left hu hθ
  have hm' := congrArg (fun t : ℝ => μ / 2 * t) hm
  have hn1 : 0 ≤ μ / 2 * (1 - θ) * ‖x - y‖ ^ 2 := by positivity
  have hn2 : 0 ≤ μ / 2 * θ * (1 - θ) * ‖z - u - (y - u)‖ ^ 2 := by positivity
  change μ / 2 * ‖v‖ ^ 2 = _ at hm'
  change f y + ⟪g, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ f x at hx
  change f y + ⟪g, u - y⟫ + μ / 2 * ‖u - y‖ ^ 2 ≤ f u at hu
  rw [norm_sub_rev y u] at hm'
  change (1 - θ) * (f y + ⟪g, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2) ≤ _ at hx'
  change θ * (f y + ⟪g, u - y⟫ + μ / 2 * ‖u - y‖ ^ 2) ≤ _ at hu'
  change f _ ≤ f y - _ at hd
  nlinarith

end OracleTemplate.TemporalDiscrepancy
