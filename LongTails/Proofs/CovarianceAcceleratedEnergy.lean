import LongTails.Proofs.CovarianceAcceleratedSelection
import LongTails.Proofs.CovarianceAcceleratedEntropy

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedVariational
open LongTails.Proofs.CovarianceAcceleratedSelection

namespace LongTails.Proofs.CovarianceAcceleratedEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))

omit [BorelSpace E] in
lemma weighted_integrable (F : E → ℝ)
    (hF : ∀ i, Integrable (fun u => density (z i) u * F u) (stdGaussian E)) :
    Integrable (fun u => mixture z w u * F u) (stdGaussian E) := by
  unfold mixture
  simp_rw [Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum _ (fun i _ => (hF i).const_mul (w.weights i))

omit [BorelSpace E] in
lemma weighted_integral (F : E → ℝ)
    (hF : ∀ i, Integrable (fun u => density (z i) u * F u) (stdGaussian E)) :
    (∫ u, mixture z w u * F u ∂stdGaussian E) =
      ∑ i, w.weights i * ∫ u, density (z i) u * F u ∂stdGaussian E := by
  unfold mixture
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hF i).const_mul (w.weights i))]
  simp only [integral_const_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_physical_mean (x0 b : E) (a : ℝ) :
    (∑ i, w.weights i • (x0 + a • z i - b)) = x0 + a • mean z w - b := by
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, w.total_of_fintype, one_smul]
  congr 1
  congr 1
  simp only [mean, Finset.smul_sum, smul_comm (w.weights _) a]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_linear (x0 b h : E) (a α : ℝ) :
    (∑ i, w.weights i * (α * ⟪h, x0 + a • z i - b⟫)) =
      α * ⟪h, x0 + a • mean z w - b⟫ := by
  rw [← weighted_physical_mean z w x0 b a, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right]
  ring

lemma coefficients_loss (x0 : E) (a α : ℝ) (b h g : E) :
    linearLoss (coefficients z x0 a α b h g) w =
      α * ⟪h, x0 + a • mean z w - b⟫ +
      ∫ u, mixture z w u * max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))
        ∂stdGaussian E := by
  unfold linearLoss coefficients
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [weighted_linear]
  rw [weighted_integral z w _ (fun i => clipped_integrand_integrable z x0 a α b h g i)]

lemma step_three_point (x0 : E) (a α β γ : ℝ) (p : StdSimplex ℝ (Fin n)) (h g : E)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    linearLoss (coefficients z x0 a α (x0 + a • mean z p) h g) (step z x0 a α β γ p h g) -
      linearLoss (coefficients z x0 a α (x0 + a • mean z p) h g) w ≤
      potential z a β γ w p - potential z a β γ w (step z x0 a α β γ p h g) -
        potential z a β γ (step z x0 a α β γ p h g) p := by
  exact minimizer_three_point z w _ p _ a β γ hM hz
    (update_minimizes z a β γ _ p hM hz)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linear_form (x0 b r u : E) (a α : ℝ) :
    α * ⟪r, x0 + a • u - b⟫ = ⟪(α * a) • r, u⟫ + α * ⟪r, x0 - b⟫ := by
  simp only [inner_sub_right, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

lemma component_linear_integrable (x0 b r : E) (a α : ℝ) (i : Fin n) :
    Integrable (fun u => density (z i) u * (α * ⟪r, x0 + a • u - b⟫)) (stdGaussian E) := by
  simp_rw [linear_form]
  exact CovarianceAcceleratedTilt.gaussian_density_affine_integrable _ _ _

lemma mixture_linear_integral (x0 b r : E) (a α : ℝ) :
    (∫ u, mixture z w u * (α * ⟪r, x0 + a • u - b⟫) ∂stdGaussian E) =
      α * ⟪r, x0 + a • mean z w - b⟫ := by
  rw [weighted_integral z w _ (component_linear_integrable z x0 b r a α)]
  have he (i : Fin n) : (∫ u, density (z i) u * (α * ⟪r, x0 + a • u - b⟫) ∂stdGaussian E) =
      α * ⟪r, x0 + a • z i - b⟫ := by
    simp_rw [linear_form]
    exact CovarianceAcceleratedTilt.gaussian_density_affine_integral _ _ _
  simp_rw [he]
  exact weighted_linear z w x0 b r a α

lemma component_exp_linear_integrable (x0 b r : E) (a α : ℝ) (i : Fin n) :
    Integrable (fun u => density (z i) u * Real.exp (α * ⟪r, x0 + a • u - b⟫))
      (stdGaussian E) := by
  have hi := (CovarianceAcceleratedTilt.integrable_exp_inner (z i + (α * a) • r)).const_mul
    (Real.exp (α * ⟪r, x0 - b⟫ - ‖z i‖ ^ 2 / 2))
  apply hi.congr
  filter_upwards [] with u
  simp only [density, ← Real.exp_add]
  congr 1
  rw [linear_form, inner_add_left]
  ring

lemma mixture_error_integrable (x0 b h g v : E) (a α : ℝ) :
    Integrable (fun u => mixture z w u *
      (max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)) -
        α * ⟪v - h, x0 + a • u - b⟫)) (stdGaussian E) := by
  have h1 := weighted_integrable z w _ (clipped_integrand_integrable z x0 a α b h g)
  have h2 := weighted_integrable z w _ (component_linear_integrable z x0 b (v - h) a α)
  apply (h1.sub h2).congr
  filter_upwards [] with u
  dsimp only [Pi.sub_apply]
  ring

lemma mixture_exp_error_integrable (x0 b h g v : E) (a α : ℝ) :
    Integrable (fun u => mixture z w u * Real.exp
      (α * ⟪v - h, x0 + a • u - b⟫ - max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))))
      (stdGaussian E) := by
  have hi := (weighted_integrable z w _
    (component_exp_linear_integrable z x0 b (v - h) a α)).const_mul (Real.exp 1)
  apply hi.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · have hm : Measurable (fun u => mixture z w u * Real.exp
        (α * ⟪v - h, x0 + a • u - b⟫ - max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)))) := by
      unfold mixture density
      fun_prop
    exact hm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (mul_pos (mixture_pos z w u) (Real.exp_pos _))]
    have hc := (abs_le.mp (CovarianceAcceleratedClipping.clip_abs_le
      (α * ⟪g - h, x0 + a • u - b⟫))).1
    have he := Real.exp_le_exp.mpr (show
      α * ⟪v - h, x0 + a • u - b⟫ - max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)) ≤
        1 + α * ⟪v - h, x0 + a • u - b⟫ by linarith)
    have hh := mul_le_mul_of_nonneg_left he (mixture_pos z w u).le
    rw [Real.exp_add] at hh
    nlinarith

lemma mixture_exp_error_pos (x0 b h g v : E) (a α : ℝ) :
    0 < ∫ u, mixture z w u * Real.exp
      (α * ⟪v - h, x0 + a • u - b⟫ - max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)))
      ∂stdGaussian E := by
  rw [integral_pos_iff_support_of_nonneg
    (fun u => (mul_pos (mixture_pos z w u) (Real.exp_pos _)).le)
    (mixture_exp_error_integrable z w x0 b h g v a α)]
  have he : Function.support (fun u => mixture z w u * Real.exp
      (α * ⟪v - h, x0 + a • u - b⟫ - max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)))) =
      Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (mul_pos (mixture_pos z w u) (Real.exp_pos _)).ne'
  rw [he]
  simp

lemma coefficients_loss_error (x0 b h g v : E) (a α : ℝ) :
    linearLoss (coefficients z x0 a α b h g) w +
      (∫ u, mixture z w u * (α * ⟪v - h, x0 + a • u - b⟫ -
        max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))) ∂stdGaussian E) =
      α * ⟪v, x0 + a • mean z w - b⟫ := by
  rw [coefficients_loss]
  simp_rw [mul_sub]
  rw [integral_sub
    (weighted_integrable z w _ (component_linear_integrable z x0 b (v - h) a α))
    (weighted_integrable z w _ (clipped_integrand_integrable z x0 a α b h g)),
    mixture_linear_integral, inner_sub_left]
  ring

lemma step_energy (x0 : E) (a α β γ : ℝ) (p : StdSimplex ℝ (Fin n)) (h g v : E)
    (hγ : 0 ≤ γ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    let b := x0 + a • mean z p
    let q := step z x0 a α β γ p h g
    let F := fun u => α * ⟪v - h, x0 + a • u - b⟫ -
      max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))
    let W := ∫ u, mixture z p u * Real.exp (F u) ∂stdGaussian E
    α * ⟪v, a • (mean z q - mean z w)⟫ +
      β * a ^ 2 / 2 * ‖mean z q - mean z p‖ ^ 2 ≤
      potential z a β γ w p - potential z a β γ w q + Real.log W -
        ∫ u, mixture z w u * F u ∂stdGaussian E := by
  let b := x0 + a • mean z p
  let q := step z x0 a α β γ p h g
  let F := fun u => α * ⟪v - h, x0 + a • u - b⟫ -
    max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))
  let W := ∫ u, mixture z p u * Real.exp (F u) ∂stdGaussian E
  change α * ⟪v, a • (mean z q - mean z w)⟫ +
    β * a ^ 2 / 2 * ‖mean z q - mean z p‖ ^ 2 ≤
    potential z a β γ w p - potential z a β γ w q + Real.log W -
      ∫ u, mixture z w u * F u ∂stdGaussian E
  have hF : Integrable (fun u => mixture z q u * F u) (stdGaussian E) := by
    have hi := (mixture_error_integrable z q x0 b h g v a α).neg
    apply hi.congr
    filter_upwards [] with u
    dsimp [F]
    ring
  have he := CovarianceAcceleratedEntropy.integral_entropy_bound (stdGaussian E)
    (mixture z p) (mixture z q) F (mixture_pos z p) (mixture_pos z q)
    (mixture_integrable z q) (mixture_integral z q) hF
    (mixture_divergence_integrable z q p hM hz)
    (mixture_exp_error_integrable z p x0 b h g v a α)
    (mixture_exp_error_pos z p x0 b h g v a α)
  change (∫ u, mixture z q u * F u ∂stdGaussian E) - divergence z q p ≤ Real.log W at he
  have hq := coefficients_loss_error z q x0 b h g v a α
  have hw := coefficients_loss_error z w x0 b h g v a α
  have hs := step_three_point z w x0 a α β γ p h g hM hz
  change linearLoss (coefficients z x0 a α b h g) q -
    linearLoss (coefficients z x0 a α b h g) w ≤
    potential z a β γ w p - potential z a β γ w q -
      (divergence z q p + β * a ^ 2 / 2 * ‖mean z q - mean z p‖ ^ 2 +
        γ / 2 * ∑ i, (q.weights i - p.weights i) ^ 2) at hs
  have hi : α * ⟪v, x0 + a • mean z q - b⟫ - α * ⟪v, x0 + a • mean z w - b⟫ =
      α * ⟪v, a • (mean z q - mean z w)⟫ := by
    rw [← mul_sub, ← inner_sub_right]
    congr 2
    module
  have hn : 0 ≤ γ / 2 * ∑ i, (q.weights i - p.weights i) ^ 2 := by positivity
  change linearLoss (coefficients z x0 a α b h g) q +
    (∫ u, mixture z q u * F u ∂stdGaussian E) = α * ⟪v, x0 + a • mean z q - b⟫ at hq
  change linearLoss (coefficients z x0 a α b h g) w +
    (∫ u, mixture z w u * F u ∂stdGaussian E) = α * ⟪v, x0 + a • mean z w - b⟫ at hw
  linarith

end LongTails.Proofs.CovarianceAcceleratedEnergy
