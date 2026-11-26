import LongTails.Proofs.MarkovQuadraticRisk

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovQuadraticWeightedAverage

open MarkovQuadratic MarkovProduct LongTails.Setups.MarkovQuadraticInterpolation
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)

variable {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
  {κ : Kernel (Fin m) (Fin m)} [IsMarkovKernel κ] {H : Fin m → q.E →L[ℝ] q.E}
  {f : q.E → ℝ} {u : q.E}

noncomputable abbrev point (q : Params) (H : Fin m → q.E →L[ℝ] q.E) (u : q.E) :=
  iterate (fun x i => H i (x - u)) q.L⁻¹ q.x0

private lemma row_energy (h : Model q m π κ H f u) (hL : 0 < q.L) (hα : 0 ≤ q.α)
    (i : Fin m) (x : q.E) :
    (∫ j, q.α * (f x - f u) + q.L / 2 * ‖x - q.L⁻¹ • H j (x-u) - u‖^2 ∂κ i) ≤
      q.L / 2 * ‖x-u‖^2 := by
  let loss := fun j => ⟪x-u, H j (x-u)⟫ / 2
  have hr : q.α * (f x - f u) ≤ ∫ j, loss j ∂κ i := by
    rw [h.population, finite_integral, finite_integral, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp only [smul_eq_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (finite_refresh_weights κ _ hα h.refresh i j)
      (div_nonneg (h.positive j _) (by norm_num))
  have hs (j : Fin m) : loss j + q.L / 2 * ‖x - q.L⁻¹ • H j (x-u) - u‖^2 ≤
      q.L / 2 * ‖x-u‖^2 := by
    rw [show x - q.L⁻¹ • H j (x-u) - u = (x-u) - q.L⁻¹ • H j (x-u) by abel]
    have he := quadratic_step_objective (H j) hL (h.symmetric j) (h.positive j)
      (h.smooth j) (inv_nonneg.mpr hL.le) (by simp [hL.ne']) (x-u)
    have hh := mul_le_mul_of_nonneg_left he hL.le
    dsimp [loss]
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at hh
    linarith
  rw [integral_add (integrable_const _) (finite_integrable _ _), integral_const]
  simp only [probReal_univ, one_smul]
  apply (add_le_add_left hr _).trans
  rw [← integral_add (finite_integrable _ _) (finite_integrable _ _)]
  simpa using integral_mono (μ := κ i) (finite_integrable _ _) (integrable_const _) hs

lemma expected_step (h : Model q m π κ H f u) (μ : ProbabilityMeasure (Fin m))
    (hL : 0 < q.L) (hα : 0 ≤ q.α) (k : ℕ) :
    let P := (pathLaw κ μ : Measure (ℕ → Fin m))
    let x := point q H u
    (∫ ξ, q.α * (f (x ξ (k+1)) - f u) + q.L / 2 * ‖x ξ (k+2) - u‖^2 ∂P) ≤
      ∫ ξ, q.L / 2 * ‖x ξ (k+1)-u‖^2 ∂P := by
  let z := fun b : Finset.Iic k → Fin m => point q H u (extendHistory b) (k+1)
  have hz (ξ : ℕ → Fin m) : z (frestrictLe k ξ) = point q H u ξ (k+1) := by
    apply iterate_congr_samples
    intro j hj
    rw [extendHistory_eq _ (by omega : j ≤ k)]
    rfl
  let W := fun b (j : Fin m) => q.α * (f (z b)-f u) +
    q.L / 2 * ‖z b - q.L⁻¹ • H j (z b-u) - u‖^2
  let V := fun (b : Finset.Iic k → Fin m) (_ : Fin m) => q.L / 2 * ‖z b-u‖^2
  have he := finite_pathLaw_integral_future κ μ k 1 W
  have hv := finite_pathLaw_integral_future κ μ k 1 V
  simp only [W, V, hz, pow_one, integral_const, probReal_univ, one_smul] at he hv
  dsimp only
  change (∫ ξ, q.α * _ + q.L / 2 * ‖point q H u ξ (k+1) -
    q.L⁻¹ • H (ξ (k+1)) (point q H u ξ (k+1)-u) - u‖^2 ∂_) ≤ _
  rw [he, hv]
  exact integral_mono (finite_integrable _ _) (finite_integrable _ _)
    (fun b => row_energy h hL hα _ (z b))

end OracleTemplate.MarkovQuadraticWeightedAverage
