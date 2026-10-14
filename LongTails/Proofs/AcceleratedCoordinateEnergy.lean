import LongTails.Proofs.AcceleratedCoordinateStep
import LongTails.Proofs.AcceleratedCoordinateSampling

open InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

lemma convex_coupling {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {μ τ η : ℝ}
    (hμ : 0 ≤ μ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η)
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (y z u : E) :
    let x := τ • z + (1 - τ) • y
    η / τ * (f x - f u) ≤ η * (1 - τ) / τ * (f y - f u) +
      η * ⟪g x, z - u⟫ - η * μ / 2 * ‖x - u‖ ^ 2 := by
  let x := τ • z + (1 - τ) • y
  have hy := hs x y
  have hu := hs x u
  have hn := mul_nonneg (show 0 ≤ μ / 2 by positivity) (sq_nonneg ‖x - y‖)
  have hy' : f x - f y ≤ ⟪g x, x - y⟫ := by
    rw [show y - x = -(x - y) by module, inner_neg_right, norm_neg] at hy
    linarith
  rw [show u - x = -(x - u) by module, inner_neg_right, norm_neg] at hu
  have hid : τ • (z - u) = τ • (x - u) + (1 - τ) • (x - y) := by
    dsimp [x]
    module
  have hi := congrArg (fun w => ⟪g x, w⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hy'' := mul_le_mul_of_nonneg_left hy' (show 0 ≤ η * (1 - τ) by positivity)
  have hu' := mul_le_mul_of_nonneg_left hu (mul_nonneg hη hτ.le)
  have hi' := congrArg (fun t => η * t) hi
  dsimp only
  change η / τ * (f x - f u) ≤ _
  apply (mul_le_mul_iff_right₀ hτ).mp
  field_simp
  nlinarith only [hy'', hu', hi']

lemma potential_algebra {η τ μ A fx fy fu ef dz ez dx inner : ℝ}
    (hη : 0 < η) (hτ : 0 < τ)
    (htune : η * μ * (1 - τ) = τ)
    (hA : A ≤ η / τ) (hdescent : ef ≤ fx)
    (hmirror : η * inner - η * μ / 2 * dx ≤
      A * (fx - ef) + dz / 2 - (1 + η * μ) / 2 * ez)
    (hsupport : η / τ * (fx - fu) ≤
      η * (1 - τ) / τ * (fy - fu) + η * inner - η * μ / 2 * dx) :
    ef - fu + μ / 2 * ez ≤ (1 - τ) * (fy - fu + μ / 2 * dz) := by
  have hcoef := mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hdescent)
  have h : η / τ * (ef - fu) + (1 + η * μ) / 2 * ez ≤
      η * (1 - τ) / τ * (fy - fu) + dz / 2 := by
    nlinarith only [hmirror, hsupport, hcoef]
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * τ by positivity)
  have heq : τ * (1 + η * μ) = η * μ := by nlinarith only [htune]
  field_simp at hh
  have heq' := congrArg (fun t => t * ez) heq
  have htune' := congrArg (fun t => t * dz) htune
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * η by positivity)).mp
  nlinarith only [hh, heq', htune']

lemma coordinate_mirror (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i)
    {f : EuclideanSpace ℝ (Fin p.d) → ℝ}
    (hmodel : ∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * gradient f x i + p.L i / 2 * t ^ 2)
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
    (u : EuclideanSpace ℝ (Fin p.d)) (i : Fin p.d) :
    let x := extrapolate p s
    let next := step p s i (gradient f x i)
    eta p * ((totalWeight p : ℝ) / (weight p i : ℝ) *
      (gradient f x i * (s.2 - u) i)) - eta p * p.μ / 2 * ‖x - u‖ ^ 2 ≤
      (eta p) ^ 2 * p.μ * (totalWeight p : ℝ) ^ 2 * (f x - f next.1) +
        ‖s.2 - u‖ ^ 2 / 2 - (1 + eta p * p.μ) / 2 * ‖next.2 - u‖ ^ 2 := by
  let x := extrapolate p s
  let a := EuclideanSpace.single i (eta p * (totalWeight p : ℝ) / (weight p i : ℝ) * gradient f x i)
  have hη := (tuning p hμ).2.2.1
  have hLi : 0 < p.L i := hμ.trans_le (hL i)
  have hwi : (0 : ℝ) < weight p i := by exact_mod_cast weight_pos p i
  have hd := coordinate_descent hmodel x i hLi
  have hδ : 0 ≤ f x - f (x - EuclideanSpace.single i (gradient f x i / p.L i)) := by
    have hn := div_nonneg (sq_nonneg (gradient f x i)) (show 0 ≤ 2 * p.L i by positivity)
    linarith
  have hg : (gradient f x i) ^ 2 ≤
      2 * p.μ * (weight p i : ℝ) ^ 2 *
        (f x - f (x - EuclideanSpace.single i (gradient f x i / p.L i))) := by
    have h := (div_le_iff₀ (show 0 < 2 * p.L i by positivity)).mp
      (show (gradient f x i) ^ 2 / (2 * p.L i) ≤
        f x - f (x - EuclideanSpace.single i (gradient f x i / p.L i)) by linarith)
    have hh := mul_le_mul_of_nonneg_right (weight_smoothness p hμ hL i) hδ
    nlinarith only [h, hh]
  have hnoise : ‖a‖ ^ 2 / 2 ≤
      (eta p) ^ 2 * p.μ * (totalWeight p : ℝ) ^ 2 *
        (f x - f (x - EuclideanSpace.single i (gradient f x i / p.L i))) := by
    have hn : ‖a‖ ^ 2 / 2 = ((eta p) ^ 2 * (totalWeight p : ℝ) ^ 2 * (gradient f x i) ^ 2) /
        (2 * (weight p i : ℝ) ^ 2) := by
      simp only [a, PiLp.norm_single, Real.norm_eq_abs, sq_abs]
      field_simp
    rw [hn]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (weight p i : ℝ) ^ 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ (eta p) ^ 2 * (totalWeight p : ℝ) ^ 2 by positivity)
    nlinarith only [hh]
  have hm := mirror_bound (mul_nonneg hη.le hμ.le) s.2 x a u
  simp only [a, EuclideanSpace.inner_single_left, conj_trivial] at hm
  dsimp only
  change _ ≤ _
  dsimp only [step]
  change eta p * ((totalWeight p : ℝ) / (weight p i : ℝ) *
      (gradient f x i * (s.2 - u) i)) - eta p * p.μ / 2 * ‖x - u‖ ^ 2 ≤ _
  dsimp only [x, a] at hm hnoise ⊢
  simp only [div_eq_mul_inv] at hm hnoise ⊢
  nlinarith only [hm, hnoise]

end OracleTemplate.AcceleratedCoordinate
