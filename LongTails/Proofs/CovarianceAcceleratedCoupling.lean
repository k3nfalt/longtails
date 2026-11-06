import LongTails.Proofs.CovarianceAcceleratedEnergy
import LongTails.Proofs.GdConvex

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedMixture

namespace LongTails.Proofs.CovarianceAcceleratedCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_coupling {f : E → ℝ} {v : E → E} {L A α : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hB : 0 < A + α)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (v x) x)
    (hL : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖) (y z z' u : E) :
    (A + α) * (f (couple A α y z') - f u) ≤
      A * (f y - f u) + α * ⟪v (couple A α y z), z' - u⟫ +
        L * α ^ 2 / (2 * (A + α)) * ‖z' - z‖ ^ 2 := by
  let x := couple A α y z
  let out := couple A α y z'
  have hy := OracleTemplate.Gradient.convex_support hc hg x y
  have hu := OracleTemplate.Gradient.convex_support hc hg x u
  have hid : A • (y - x) + α • (u - x) = α • (u - z) := by
    dsimp [x, couple]
    match_scalars
    all_goals field_simp [hB.ne'] <;> ring
  have hi := congrArg (fun t => ⟪v x, t⟫) hid
  simp only [inner_add_right, real_inner_smul_right] at hi
  rw [show u - z = -(z - u) by abel, inner_neg_right] at hi
  have hconv : (A + α) * (f x - f u) ≤ A * (f y - f u) + α * ⟪v x, z - u⟫ := by
    have hy' := mul_le_mul_of_nonneg_left hy hA
    have hu' := mul_le_mul_of_nonneg_left hu hα
    nlinarith only [hy', hu', hi]
  have hd : out - x = (α / (A + α)) • (z' - z) := by dsimp [out, x, couple]; module
  have hs := OracleTemplate.Gradient.smooth_upper_bound hg hL x out
  rw [hd, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hs' := mul_le_mul_of_nonneg_left hs hB.le
  have he : (A + α) * (f x + α / (A + α) * ⟪v x, z' - z⟫ +
      L / 2 * ((α / (A + α)) ^ 2 * ‖z' - z‖ ^ 2)) =
      (A + α) * f x + α * ⟪v x, z' - z⟫ +
        L * α ^ 2 / (2 * (A + α)) * ‖z' - z‖ ^ 2 := by
    field_simp [hB.ne']
  rw [he] at hs'
  have hin : α * ⟪v x, z - u⟫ + α * ⟪v x, z' - z⟫ = α * ⟪v x, z' - u⟫ := by
    rw [← mul_add, ← inner_add_right]
    congr 2
    abel
  change (A + α) * (f out - f u) ≤ _
  nlinarith only [hconv, hs', hin]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma accelerated_step {n : ℕ} (z : Fin n → E) (x0 y : E)
    (p w : StdSimplex ℝ (Fin n)) (h g : E) {f : E → ℝ} {v : E → E}
    {L A a α β γ : ℝ} (hA : 0 ≤ A) (hα : 0 ≤ α) (hB : 0 < A + α)
    (hβ : L * α ^ 2 / (A + α) ≤ β) (hγ : 0 ≤ γ)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (v x) x)
    (hL : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    let b := x0 + a • mean z p
    let q := step z x0 a α β γ p h g
    let x := couple A α y b
    let out := couple A α y (x0 + a • mean z q)
    let u := x0 + a • mean z w
    let F := fun t => α * ⟪v x - h, x0 + a • t - b⟫ -
      max (-1) (min 1 (α * ⟪g - h, x0 + a • t - b⟫))
    let W := ∫ t, mixture z p t * Real.exp (F t) ∂stdGaussian E
    (A + α) * (f out - f u) + potential z a β γ w q ≤
      A * (f y - f u) + potential z a β γ w p + Real.log W -
        ∫ t, mixture z w t * F t ∂stdGaussian E := by
  let b := x0 + a • mean z p
  let q := step z x0 a α β γ p h g
  let x := couple A α y b
  let out := couple A α y (x0 + a • mean z q)
  let u := x0 + a • mean z w
  let F := fun t => α * ⟪v x - h, x0 + a • t - b⟫ -
    max (-1) (min 1 (α * ⟪g - h, x0 + a • t - b⟫))
  let W := ∫ t, mixture z p t * Real.exp (F t) ∂stdGaussian E
  change (A + α) * (f out - f u) + potential z a β γ w q ≤
    A * (f y - f u) + potential z a β γ w p + Real.log W -
      ∫ t, mixture z w t * F t ∂stdGaussian E
  have he := CovarianceAcceleratedEnergy.step_energy z w x0 a α β γ p h g (v x) hγ hM hz
  change α * ⟪v x, a • (mean z q - mean z w)⟫ +
    β * a ^ 2 / 2 * ‖mean z q - mean z p‖ ^ 2 ≤
    potential z a β γ w p - potential z a β γ w q + Real.log W -
      ∫ t, mixture z w t * F t ∂stdGaussian E at he
  have hs := smooth_coupling hA hα hB hc hg hL y b (x0 + a • mean z q) u
  have hdiff : x0 + a • mean z q - u = a • (mean z q - mean z w) := by dsimp [u]; module
  have hmove : x0 + a • mean z q - b = a • (mean z q - mean z p) := by dsimp [b]; module
  rw [hdiff, hmove, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hcoef : L * α ^ 2 / (2 * (A + α)) ≤ β / 2 := by
    have hh := div_le_div_of_nonneg_right hβ (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1
    field_simp [hB.ne']
  have hterm := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg a) (sq_nonneg ‖mean z q - mean z p‖))
  change (A + α) * (f out - f u) ≤ A * (f y - f u) +
    α * ⟪v x, a • (mean z q - mean z w)⟫ +
      L * α ^ 2 / (2 * (A + α)) * (a ^ 2 * ‖mean z q - mean z p‖ ^ 2) at hs
  nlinarith only [he, hs, hterm]

end LongTails.Proofs.CovarianceAcceleratedCoupling
