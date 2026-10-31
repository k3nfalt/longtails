import LongTails.Proofs.UntiedReverseFisherLoss
import LongTails.Proofs.SymmetricReverseFisherGradient
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherGradient

open LongTails.Setups.UntiedGaussianReverseFisher
open LongTails.Proofs.UntiedReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherLoss

def tiedParams (p : Params) : LongTails.Setups.SymmetricGaussianReverseFisher.Params :=
  ⟨p.dimension, 0, 0, 1, 1⟩

noncomputable def component {p : Params} (μ θ : Means p) (i : Fin 2) : Space p :=
  (centre θ - centre μ) + ((if i = 0 then (1 : ℝ) else -1) * alpha ‖half θ‖ / 2) • half θ -
    (ridgeForce ‖half μ‖ ⟪θ i - centre μ, half μ⟫ / 2) • half μ

noncomputable def lossGradient {p : Params} (μ θ : Means p) : Means p :=
  toLp 2 (component μ θ)

noncomputable def projection {p : Params} (i : Fin 2) : Means p →L[ℝ] Space p :=
  PiLp.proj 2 (fun _ : Fin 2 => Space p) i

lemma projection_apply {p : Params} (i : Fin 2) (θ : Means p) : projection i θ = θ i := rfl

noncomputable def centreMap {p : Params} : Means p →L[ℝ] Space p :=
  (1 / 2 : ℝ) • (projection 0 + projection 1)

noncomputable def halfMap {p : Params} : Means p →L[ℝ] Space p :=
  (1 / 2 : ℝ) • (projection 0 - projection 1)

lemma centreMap_apply {p : Params} (θ : Means p) : centreMap θ = centre θ := rfl

lemma halfMap_apply {p : Params} (θ : Means p) : halfMap θ = half θ := rfl

lemma loss_eq_scalar {p : Params} (μ : Means p) :
    loss μ = fun θ => ‖centreMap θ - centre μ‖ ^ 2 + radialSelf ‖halfMap θ‖ +
      1 / 2 * (scalarPotential ‖half μ‖ ⟪half μ, projection 0 θ - centre μ⟫ +
        scalarPotential ‖half μ‖ ⟪half μ, projection 1 θ - centre μ⟫) := by
  funext θ
  rw [loss_decomposition, real_inner_comm (half μ), real_inner_comm (half μ)]
  simp only [projection_apply, centreMap_apply, halfMap_apply]
  ring

lemma hasGradientAt_radial_space {p : Params} (x : Space p) :
    HasGradientAt (fun y : Space p => radialSelf ‖y‖) (alpha ‖x‖ • x) x :=
  LongTails.Proofs.SymmetricReverseFisherGradient.hasGradientAt_radial (p := tiedParams p) x

lemma inner_centre {p : Params} (x : Space p) (h : Means p) :
    ⟪x, centre h⟫ = (⟪x, h 0⟫ + ⟪x, h 1⟫) / 2 := by
  unfold centre; rw [inner_smul_right, inner_add_right]; ring

lemma inner_half {p : Params} (x : Space p) (h : Means p) :
    ⟪x, half h⟫ = (⟪x, h 0⟫ - ⟪x, h 1⟫) / 2 := by
  unfold half; rw [inner_smul_right, inner_sub_right]; ring

theorem hasGradientAt_loss {p : Params} (μ θ : Means p) :
    HasGradientAt (loss μ) (lossGradient μ θ) θ := by
  have d1 := ((centreMap (p := p)).hasFDerivAt.sub_const (centre μ)).norm_sq (x := θ)
  have d2 := (hasGradientAt_radial_space (half θ)).hasFDerivAt.comp θ (halfMap (p := p)).hasFDerivAt
  have l0 := (innerSL ℝ (half μ)).hasFDerivAt.comp θ
    ((projection (p := p) 0).hasFDerivAt.sub_const (centre μ))
  have l1 := (innerSL ℝ (half μ)).hasFDerivAt.comp θ
    ((projection (p := p) 1).hasFDerivAt.sub_const (centre μ))
  have d3 := (hasDerivAt_scalarPotential ‖half μ‖ _).comp_hasFDerivAt θ l0
  have d4 := (hasDerivAt_scalarPotential ‖half μ‖ _).comp_hasFDerivAt θ l1
  have h := (d1.add d2).add ((d3.add d4).const_mul (1 / 2))
  rw [loss_eq_scalar, hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · ext x; rfl
  · ext h'
    simp only [InnerProductSpace.toDual_apply_apply, add_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, centreMap_apply,
      halfMap_apply, projection_apply]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [lossGradient, component, PiLp.toLp_apply,
      show ((1 : Fin 2) = 0) = False by decide, ite_false]
    simp only [ite_true]
    rw [real_inner_comm (θ 0 - centre μ) (half μ), real_inner_comm (θ 1 - centre μ) (half μ)]
    set R0 := ridgeForce ‖half μ‖ ⟪θ 0 - centre μ, half μ⟫
    set R1 := ridgeForce ‖half μ‖ ⟪θ 1 - centre μ, half μ⟫
    set A := alpha ‖half θ‖
    set w := centre θ - centre μ
    set v := half θ
    set b := half μ
    rw [inner_smul_left, inner_centre w h', inner_half v h']
    simp only [inner_add_left, inner_sub_left, inner_smul_left, conj_trivial]
    push_cast
    ring

lemma gradient_loss {p : Params} (μ θ : Means p) : gradient (loss μ) θ = lossGradient μ θ :=
  (hasGradientAt_loss μ θ).gradient

lemma step_centre {p : Params} (μ θ : Means p) (γ : ℝ) :
    centre (θ - γ • lossGradient μ θ) - centre μ =
      (1 - γ) • (centre θ - centre μ) +
        (γ / 4 * (ridgeForce ‖half μ‖ ⟪θ 0 - centre μ, half μ⟫ +
          ridgeForce ‖half μ‖ ⟪θ 1 - centre μ, half μ⟫)) • half μ := by
  unfold centre
  simp only [PiLp.sub_apply, PiLp.smul_apply, lossGradient, component,
    show ((1 : Fin 2) = 0) = False by decide, ite_false, ite_true, one_mul]
  unfold centre
  module

lemma step_half {p : Params} (μ θ : Means p) (γ : ℝ) :
    half (θ - γ • lossGradient μ θ) =
      (1 - γ / 2 * alpha ‖half θ‖) • half θ +
        (γ / 4 * (ridgeForce ‖half μ‖ ⟪θ 0 - centre μ, half μ⟫ -
          ridgeForce ‖half μ‖ ⟪θ 1 - centre μ, half μ⟫)) • half μ := by
  unfold half
  simp only [PiLp.sub_apply, PiLp.smul_apply, lossGradient, component,
    show ((1 : Fin 2) = 0) = False by decide, ite_false, ite_true, one_mul]
  unfold half
  module

lemma input_zero {p : Params} (μ θ : Means p) :
    θ 0 - centre μ = (centre θ - centre μ) + half θ := by
  rw [point_zero]; abel

lemma input_one {p : Params} (μ θ : Means p) :
    θ 1 - centre μ = (centre θ - centre μ) - half θ := by
  rw [point_one]; abel

lemma matchingError_le {p : Params} (μ θ : Means p) :
    matchingError μ θ ≤ 2 * ‖centre θ - centre μ‖ ^ 2 + 2 * ‖half θ - half μ‖ ^ 2 := by
  unfold matchingError
  apply min_le_of_left_le
  have h0 : θ 0 - μ 0 = (centre θ - centre μ) + (half θ - half μ) := by
    rw [point_zero θ, point_zero μ]; abel
  have h1 : θ 1 - μ 1 = (centre θ - centre μ) - (half θ - half μ) := by
    rw [point_one θ, point_one μ]; abel
  rw [h0, h1]
  have := parallelogram_law_with_norm ℝ (centre θ - centre μ) (half θ - half μ)
  nlinarith [sq_nonneg ‖centre θ - centre μ‖]

lemma matchingError_le_swap {p : Params} (μ θ : Means p) :
    matchingError μ θ ≤ 2 * ‖centre θ - centre μ‖ ^ 2 + 2 * ‖half θ + half μ‖ ^ 2 := by
  unfold matchingError
  apply min_le_of_right_le
  have h0 : θ 0 - μ 1 = (centre θ - centre μ) + (half θ + half μ) := by
    rw [point_zero θ, point_one μ]; abel
  have h1 : θ 1 - μ 0 = (centre θ - centre μ) - (half θ + half μ) := by
    rw [point_one θ, point_zero μ]; abel
  rw [h0, h1]
  have := parallelogram_law_with_norm ℝ (centre θ - centre μ) (half θ + half μ)
  nlinarith [sq_nonneg ‖centre θ - centre μ‖]

end LongTails.Proofs.UntiedReverseFisherGradient
