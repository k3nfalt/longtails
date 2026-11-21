import LongTails.Proofs.PLMinimaxCubicDescent
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.SpectralGradientModel

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CubicNewtonPLDescent

open OracleTemplate.PLMinimax LongTails.Proofs.CubicRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma step_bounds {f : E → ℝ} {H : ℝ} (hH : 0 < H)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ H * ‖x - y‖)
    (x : E) :
    f (x + envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H) ≤
        f x - H / 3 * ‖envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H‖ ^ 3 ∧
      ‖gradient f (x + envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H)‖ ≤
        3 * H / 2 * ‖envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H‖ ^ 2 := by
  have hcomplete : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hproper : ProperSpace E := FiniteDimensional.proper_real E
  have hfd : ∀ y, HasFDerivAt f (innerSL ℝ (gradient f y)) y := by
    intro y
    have h := (hf y).hasFDerivAt
    have he : (InnerProductSpace.toDual ℝ E) (gradient f y) = innerSL ℝ (gradient f y) := by
      ext z
      simp
    rwa [he] at h
  have hgd : ∀ y, HasFDerivAt (gradient f) (fderiv ℝ (gradient f) y) y :=
    fun y => (hg y).hasFDerivAt
  have hsym : ∀ u v, ⟪u, fderiv ℝ (gradient f) x v⟫ = ⟪fderiv ℝ (gradient f) x u, v⟫ :=
    fun u v => (OracleTemplate.SpectralGradient.hessian_symmetric
      (fun a => (hf a).differentiableAt) hg x u v).symm
  obtain ⟨s, hs⟩ : ∃ s : E, s = envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H :=
    ⟨_, rfl⟩
  have ht := objective_taylor hfd hgd hLip x s
  have hgt := gradient_taylor hgd hLip x s
  have hd := envelopeCubicStep_inexact_descent (gradient f x) (gradient f x)
    (fderiv ℝ (gradient f) x) (fderiv ℝ (gradient f) x) (M := H) (a := 0) (b := 0)
    (before := f x) (after := f (x + s)) hH hsym (by simp) (by simp) (by
      rw [← hs]
      have h := (abs_le.mp ht).2
      linarith)
  have hb := envelopeCubicStep_gradient_bound (gradient f x) (gradient f x)
    (gradient f (x + s)) (fderiv ℝ (gradient f) x) (fderiv ℝ (gradient f) x) (M := H)
    (a := 0) (b := 0) hH hsym (by simp) (by simp) (by
      rw [← hs]
      calc
        _ ≤ H * ‖s‖ ^ 2 / 2 := hgt
        _ = H / 2 * ‖s‖ ^ 2 := by ring)
  rw [← hs] at hd hb ⊢
  simp only [zero_mul, zero_div, add_zero, zero_add] at hd hb
  exact ⟨by linarith, hb⟩

end LongTails.Proofs.CubicNewtonPLDescent
