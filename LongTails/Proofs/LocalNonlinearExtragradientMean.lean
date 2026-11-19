import LongTails.Proofs.LocalNonlinearExtragradientIteration
import LongTails.Proofs.LocalNonlinearExtragradientBlock

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalNonlinearExtragradientMean

variable {E Ω Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma run_mean_bound (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p x : E) (F : E → E) (J : E → E →L[ℝ] E) (g : E → Ω → E)
    (ξ : ℕ → Ξ → Ω) {L μ ρ M : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hρ : 1 ≤ ρ) (hM : 0 ≤ M)
    (hd : ∀ z, HasFDerivAt F (J z) z)
    (hJ : ∀ u v, ‖J u - J v‖ ≤ M * ‖u - v‖) (hp : F p = 0)
    (hlip : ∀ u v, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hmono : ∀ y, μ * ‖y - p‖ ^ 2 ≤ ⟪F y, y - p⟫)
    (hg : Measurable (Function.uncurry g))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    (hgi : ∀ y, Integrable (g y) Q)
    (hg2 : ∀ y, Integrable (fun ω => ‖g y ω‖ ^ 2) Q)
    (hmean : ∀ y, (∫ ω, g y ω ∂Q) = F y)
    (hsgc : ∀ y, (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ ρ * ‖F y‖ ^ 2) (k : ℕ) :
    ‖∫ ω, LongTails.Algorithms.LocalNonlinearExtragradient.run
      (1 / (4 * L)) g x (fun j => ξ j ω) k - p ∂P‖ ≤
      (1 - μ / (8 * L)) ^ k * ‖x - p‖ +
        (ρ * M / (4 * L) * ‖x - p‖ ^ 2) * (k : ℝ) *
          (2 + ρ / 8 + ρ ^ 2 / 128) ^ k := by
  classical
  let η : ℝ := 1 / (4 * L)
  let G : ℝ := 2 + ρ / 8 + ρ ^ 2 / 128
  let X : ℕ → Ξ → E := fun j ω => LongTails.Algorithms.LocalNonlinearExtragradient.run
    η g x (fun i => ξ i ω) j
  let Y : ℕ → Ξ → E := fun j ω => X j ω - η • g (X j ω) (ξ (2 * j) ω)
  let z : ℕ → E := fun j => ∫ ω, X j ω - p ∂P
  let e : ℕ → E := fun j =>
    η ^ 2 • J p (∫ ω, F (X j ω) - J p (X j ω - p) ∂P) -
      η • (∫ ω, F (Y j ω) - J p (Y j ω - p) ∂P)
  have hρ0 : 0 ≤ ρ := by linarith
  have hG : 1 ≤ G := by dsimp [G]; nlinarith [sq_nonneg ρ]
  have hm (y : E) : 0 ≤ ⟪y - p, F y⟫ := by
    rw [real_inner_comm]
    exact (mul_nonneg hμ (sq_nonneg _)).trans (hmono y)
  have hl (y : E) : ‖F y‖ ^ 2 ≤ L ^ 2 * ‖y - p‖ ^ 2 := by
    have hh := hlip y p
    rw [hp, sub_zero] at hh
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (F y)) hh 2
  have hs (j : ℕ) := LocalNonlinearExtragradientIteration.run_second_moment
    P Q p x F g ξ hL hρ0 hg hIID hgi hg2 hmean hsgc hm hl j
  let default : Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  have hstream : Measurable (fun ω j => ξ j ω) := Measurable.of_eval hIID.measurable
  have hX (j : ℕ) : Measurable (X j) :=
    (LocalNonlinearExtragradientSampling.measurable_run η g x hg j).comp hstream
  have hY (j : ℕ) : Measurable (Y j) :=
    (hX j).sub ((hg.comp ((hX j).prodMk (hIID.measurable (2 * j)))).const_smul η)
  have hindX (j : ℕ) : IndepFun (X j) (ξ (2 * j)) P :=
    LocalNonlinearExtragradientSampling.run_independent_fresh
      η g x default hg ξ P hIID.independent hIID.measurable j (2 * j) le_rfl
  have hindY (j : ℕ) : IndepFun (Y j) (ξ (2 * j + 1)) P :=
    LocalNonlinearExtragradientSampling.half_independent_fresh
      η g x default hg ξ P hIID.independent hIID.measurable j (2 * j + 1) le_rfl
  have hy (j : ℕ) := LocalNonlinearExtragradientIteration.random_half_growth
    P Q p F g (X j) (ξ (2 * j)) hL hρ0 (hX j) (hIID.measurable (2 * j))
    hg (hindX j) (hIID.marginal (2 * j)) (hs j).1 hgi hg2 hmean hsgc hm hl
  have hA : ‖J p‖ ≤ L :=
    LocalNonlinearExtragradientGeometry.derivative_norm_bound F (J p) p hL.le (hd p) hlip
  have hrec (j : ℕ) : z (j + 1) = z j - η • J p (z j) +
      η ^ 2 • J p (J p (z j)) + e j := by
    have hh := LocalNonlinearExtragradientIteration.random_mean_recursion
      P Q p F J g (X j) (ξ (2 * j)) (ξ (2 * j + 1)) hL hρ0 hd hJ hp
      (hX j) (hIID.measurable (2 * j)) (hIID.measurable (2 * j + 1)) hg
      (hindX j) (hindY j) (hIID.marginal (2 * j)) (hIID.marginal (2 * j + 1))
      (hs j).1 hgi hg2 hmean hsgc hm hl
    change z (j + 1) = _ at hh
    rw [hh]
    dsimp [z, e, η, Y]
    abel
  have he (j : ℕ) : ‖e j‖ ≤ ρ * M / (4 * L) * ‖x - p‖ ^ 2 * G ^ j := by
    have hrX := LocalNonlinearExtragradientMoments.integral_root_remainder F J p hd hJ hp
      (hX j).aestronglyMeasurable (hs j).1
    have hrY := LocalNonlinearExtragradientMoments.integral_root_remainder F J p hd hJ hp
      (hY j).aestronglyMeasurable (hy j).1
    have hb := LocalNonlinearExtragradientGeometry.mean_perturbation_bound (J p)
      (∫ ω, F (X j ω) - J p (X j ω - p) ∂P)
      (∫ ω, F (Y j ω) - J p (Y j ω - p) ∂P)
      hL hM hρ (integral_nonneg fun _ => sq_nonneg _) hA hrX.2
      (hrY.2.trans (mul_le_mul_of_nonneg_left (hy j).2 (by positivity)))
    change ‖e j‖ ≤ ρ * M / (4 * L) * (∫ ω, ‖X j ω - p‖ ^ 2 ∂P) at hb
    calc
      _ ≤ ρ * M / (4 * L) * (∫ ω, ‖X j ω - p‖ ^ 2 ∂P) := hb
      _ ≤ ρ * M / (4 * L) * (G ^ j * ‖x - p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hs j).2 (by positivity)
      _ = _ := by ring
  exact LocalNonlinearExtragradientBlock.mean_run_bound (J p) z e hL hμ hμL hρ0 hM hG hA
    (fun v => LocalNonlinearExtragradientGeometry.root_derivative_coercivity
      F (J p) p v μ (hd p) hp hmono)
    (by simp [z, X, LongTails.Algorithms.LocalNonlinearExtragradient.run]) hrec he k

end LongTails.Proofs.LocalNonlinearExtragradientMean
