import LongTails.Setups.HigherSmoothBilevel
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace LongTails.Proofs.BilevelMinimizers

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_minimum_of_quadratic_support [ProperSpace E] {f : E → ℝ}
    (hf : Continuous f) (A : E →L[ℝ] ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hbound : ∀ y, f 0 + A y + μ / 2 * ‖y‖ ^ 2 ≤ f y) :
    ∃ y, ∀ z, f y ≤ f z := by
  let R := 2 * ‖A‖ / μ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨y, _, hy⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    (nonempty_closedBall.mpr hR) hf.continuousOn
  refine ⟨y, fun z => ?_⟩
  by_cases hz : z ∈ closedBall (0 : E) R
  · exact hy hz
  · have hn : R < ‖z‖ := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hmul : 2 * ‖A‖ < μ * ‖z‖ := by
      have he : μ * R = 2 * ‖A‖ + μ := by dsimp [R]; field_simp
      have hm := mul_lt_mul_of_pos_left hn hμ
      nlinarith
    have ha : -(‖A‖ * ‖z‖) ≤ A z := by
      have h := A.le_opNorm z
      rw [Real.norm_eq_abs] at h
      exact (abs_le.mp h).1
    have hq : 0 ≤ A z + μ / 2 * ‖z‖ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hmul.le (norm_nonneg z)
      nlinarith
    have hzero := hy (show (0 : E) ∈ closedBall 0 R by simpa using hR)
    exact hzero.trans (by linarith [hbound z])

lemma quadratic_support_unique {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hd : ∀ y, HasFDerivAt f (D y) y) {μ : ℝ} (hμ : 0 < μ)
    (hsc : ∀ y z, f y + D y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    {y z : E} (hy : ∀ w, f y ≤ f w) (hz : ∀ w, f z ≤ f w) : y = z := by
  have hlocal : IsLocalMin f y := Filter.Eventually.of_forall hy
  have hD := hlocal.hasFDerivAt_eq_zero (hd y)
  have h := hsc y z
  simp only [hD, zero_apply, add_zero] at h
  have hn : ‖z - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z - y‖, hz y]
  have he : z - y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact (sub_eq_zero.mp he).symm


open LongTails.Setups.HigherSmoothBilevel

lemma lower_minimum_exists {p : Params} {I : Instance p}
    (hg : Continuous I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    ∃ y, ∀ z, I.g (x, y) ≤ I.g (x, z) := by
  apply exists_minimum_of_quadratic_support
    (hg.comp (continuous_const.prodMk continuous_id))
    ((fderiv ℝ I.g (x, 0)).comp (.inr ℝ p.X p.Y)) hμ
  intro z
  simpa using hsc x 0 z

lemma lowerSolution_minimum {p : Params} {I : Instance p}
    (hg : Continuous I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y : p.Y) :
    I.g (x, lowerSolution I x) ≤ I.g (x, y) := by
  have he := lower_minimum_exists hg hμ hsc x
  simp only [lowerSolution, dite_eq_left he]
  exact Classical.choose_spec he y

lemma lowerSolution_unique {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y : p.Y)
    (hy : ∀ z, I.g (x, y) ≤ I.g (x, z)) : y = lowerSolution I x := by
  apply quadratic_support_unique (D := fun y =>
    (fderiv ℝ I.g (x, y)).comp (.inr ℝ p.X p.Y))
    (fun y => (hg (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y))
    hμ (fun y z => hsc x y z) hy
  exact lowerSolution_minimum hg.continuous hμ hsc x


lemma lowerSolution_stationary {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    (fderiv ℝ I.g (x, lowerSolution I x)).comp (.inr ℝ p.X p.Y) = 0 := by
  have hm : IsLocalMin (fun y => I.g (x, y)) (lowerSolution I x) :=
    Filter.Eventually.of_forall (lowerSolution_minimum hg.continuous hμ hsc x)
  exact hm.hasFDerivAt_eq_zero ((hg _).hasFDerivAt.comp _
    (hasFDerivAt_prodMk_right x (lowerSolution I x)))

lemma stationary_eq_lowerSolution {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y : p.Y)
    (hy : (fderiv ℝ I.g (x, y)).comp (.inr ℝ p.X p.Y) = 0) :
    y = lowerSolution I x := by
  apply lowerSolution_unique hg hμ hsc x y
  intro z
  have hd : fderiv ℝ I.g (x, y) (0, z - y) = 0 :=
    DFunLike.congr_fun hy (z - y)
  have h := hsc x y z
  rw [hd, add_zero] at h
  have hn : 0 ≤ p.μ / 2 * ‖z - y‖ ^ 2 := by positivity
  linarith

end LongTails.Proofs.BilevelMinimizers
