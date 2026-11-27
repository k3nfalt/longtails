import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SlidingLowerMoreau

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma moreau_lower {F : E → ℝ} {g : E → E} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hF : ∀ x, HasGradientAt F (g x) x)
    (hwc : ∀ x y, F x + ⟪g x, y - x⟫ - ℓ / 2 * ‖y - x‖ ^ 2 ≤ F y) (w : E) :
    ∃ y, g y = (2 * ℓ) • (w - y) ∧
      ℓ / 2 * ‖w - y‖ ^ 2 ≤ F w - ⨅ v, (F v + ℓ * ‖v - w‖ ^ 2) := by
  let φ : E → ℝ := fun v => F v + ℓ * ‖v - w‖ ^ 2
  have hcont : Continuous φ := by
    have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hF x).continuousAt)
    dsimp [φ]
    fun_prop
  have hb : ∀ v, ℓ / 4 * ‖v - w‖ ^ 2 + (F w - ‖g w‖ ^ 2 / ℓ) ≤ φ v := by
    intro v
    have h1 := hwc w v
    have h3 : -(‖g w‖ * ‖v - w‖) ≤ ⟪g w, v - w⟫ := by
      have := abs_real_inner_le_norm (g w) (v - w)
      have := neg_abs_le ⟪g w, v - w⟫
      linarith
    have h4 : ‖g w‖ * ‖v - w‖ ≤ ℓ / 4 * ‖v - w‖ ^ 2 + ‖g w‖ ^ 2 / ℓ := by
      have h5 : 0 ≤ (ℓ / 2 * ‖v - w‖ - ‖g w‖) ^ 2 / ℓ := by positivity
      have h6 : (ℓ / 2 * ‖v - w‖ - ‖g w‖) ^ 2 / ℓ =
          ℓ / 4 * ‖v - w‖ ^ 2 - ‖g w‖ * ‖v - w‖ + ‖g w‖ ^ 2 / ℓ := by
        field_simp
        ring
      linarith
    dsimp [φ]
    nlinarith
  have hn : Tendsto (fun x : E => ‖x - w‖) (Filter.cocompact E) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖w‖)
      (tendsto_norm_cocompact_atTop (E := E)))
    have := norm_sub_norm_le x w
    linarith
  have hlim : Tendsto (fun x : E => ℓ / 4 * ‖x - w‖ ^ 2 + (F w - ‖g w‖ ^ 2 / ℓ))
      (Filter.cocompact E) atTop :=
    tendsto_atTop_add_const_right _ _
      (((tendsto_pow_atTop two_ne_zero).comp hn).const_mul_atTop (by positivity))
  obtain ⟨y, hy⟩ := hcont.exists_forall_le (tendsto_atTop_mono hb hlim)
  have hgφ : HasGradientAt φ (g y + (2 * ℓ) • (y - w)) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF y)
    have h2 := ((hasStrictFDerivAt_norm_sq (y - w)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const w)).const_mul ℓ
    refine (h1.add h2).congr_fderiv ?_
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
    ring
  have hmin : IsLocalMin φ y := Filter.Eventually.of_forall (fun v => hy v)
  have hz := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.mp hgφ)
  have hz' : g y + (2 * ℓ) • (y - w) = 0 := by
    have := congrArg (InnerProductSpace.toDual ℝ E).symm hz
    simpa using this
  have hgy : g y = (2 * ℓ) • (w - y) := by
    rw [show w - y = -(y - w) by abel, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  refine ⟨y, hgy, ?_⟩
  have hinf : (⨅ v, φ v) = φ y := by
    apply le_antisymm
    · exact ciInf_le ⟨φ y, by rintro _ ⟨v, rfl⟩; exact hy v⟩ y
    · exact le_ciInf hy
  change ℓ / 2 * ‖w - y‖ ^ 2 ≤ F w - ⨅ v, φ v
  rw [hinf]
  have hw := hwc y w
  rw [hgy, inner_smul_left] at hw
  simp only [conj_trivial] at hw
  have hi : ⟪w - y, w - y⟫ = ‖w - y‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hn2 : ‖y - w‖ = ‖w - y‖ := norm_sub_rev y w
  dsimp [φ]
  rw [hn2]
  nlinarith

end LongTails.Proofs.SlidingLowerMoreau
