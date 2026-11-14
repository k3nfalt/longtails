import LongTails.Setups.HighDimensionalConstrainedQuasar
import LongTails.Proofs.QuasarCoinLaw
import LongTails.Proofs.HiddenConvexGeometry
import LongTails.Proofs.HiddenConvexExpectation

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.QuasarHardAdmissible

open LongTails.Setups HighDimensionalConstrainedQuasar OracleTemplate.LocalHiddenConvex QuasarCoinLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ballProj_obtuse (x0 z w : E) {r : ℝ} (hr : 0 ≤ r) (hw : w ∈ closedBall x0 r) :
    ⟪z - ballProj x0 r z, w - ballProj x0 r z⟫ ≤ 0 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  unfold ballProj
  split_ifs with h
  · simp
  · rw [not_le] at h
    set s := ‖z - x0‖ with hs
    have hpos : 0 < s := hr.trans_lt h
    have hn : z - (x0 + (r / s) • (z - x0)) = ((s - r) / s) • (z - x0) := by
      rw [sub_div, div_self hpos.ne', sub_smul, one_smul]
      abel
    have hp : w - (x0 + (r / s) • (z - x0)) = (w - x0) - (r / s) • (z - x0) := by abel
    rw [hn, hp, inner_smul_left, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    have hcs : ⟪z - x0, w - x0⟫ ≤ s * r :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hw hpos.le)
    have hc : 0 ≤ (s - r) / s := div_nonneg (sub_nonneg.mpr h.le) hpos.le
    have he : r / s * s ^ 2 = s * r := by field_simp
    have hin : ⟪z - x0, w - x0⟫ - r / s * s ^ 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hc hin

lemma coin_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (φ : Bool → F) :
    ∫ ω, φ ω ∂((coinLaw ν h0 h1 : ProbabilityMeasure Bool) : Measure Bool) =
      ν • φ true + (1 - ν) • φ false := by
  have := coinMeasure_isProb h0 h1
  change ∫ ω, φ ω ∂(coinMeasure ν) = _
  rw [integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, Measure.real, coinMeasure_true, coinMeasure_false,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (show 0 ≤ 1 - ν by linarith)]

lemma coin_integrable {F : Type*} [NormedAddCommGroup F] {ν : ℝ}
    (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (φ : Bool → F) :
    Integrable φ ((coinLaw ν h0 h1 : ProbabilityMeasure Bool) : Measure Bool) :=
  Integrable.of_finite

noncomputable def ballOracle (p : Params) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1)
    (g : EuclideanSpace ℝ (Fin p.d) → Bool → EuclideanSpace ℝ (Fin p.d)) :
    OracleTemplate.Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 2 where
  Seed := fun _ => Bool
  law := coinPath ν h0 h1
  answer := fun _ (i, x) seed => if i = 0 then g x seed else ballProj p.x0 (p.D / 2) x

noncomputable def ballInstance (p : Params) (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin p.d)) : StochasticConstrainedQuasar.Instance p.toStochastic :=
  ⟨f, closedBall p.x0 (p.D / 2), xstar⟩

lemma ball_admissible (p : Params) (hD : 0 < p.D) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1)
    (f : EuclideanSpace ℝ (Fin p.d) → ℝ) (G : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (g : EuclideanSpace ℝ (Fin p.d) → Bool → EuclideanSpace ℝ (Fin p.d))
    (xstar : EuclideanSpace ℝ (Fin p.d)) (hxs : ‖xstar - p.x0‖ ≤ p.D / 2)
    (hgrad : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    (hmin : ∀ x, f xstar ≤ f x)
    (hquasar : ∀ x, p.γ * (f x - f xstar) ≤ ⟪G x, x - xstar⟫)
    (hg : Measurable (Function.uncurry g))
    (hmean : ∀ x ∈ closedBall p.x0 (p.D / 2), ν • g x true + (1 - ν) • g x false = G x)
    (hvar : ∀ x ∈ closedBall p.x0 (p.D / 2),
      ν * ‖g x true - G x‖ ^ 2 + (1 - ν) * ‖g x false - G x‖ ^ 2 ≤ p.σ ^ 2) :
    spec.admissible p (ballInstance p f xstar) (ballOracle p h0 h1 g) := by
  have hr : 0 ≤ p.D / 2 := by linarith
  have hgf (x : EuclideanSpace ℝ (Fin p.d)) : gradient f x = G x := (hgrad x).gradient
  refine ⟨g, coinLaw ν h0 h1, coinPath ν h0 h1, ballProj p.x0 (p.D / 2), coinPath_iid h0 h1, rfl,
    ?_, ?_, convex_closedBall _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hg, ?_, ?_, ?_, ?_⟩
  · intro z
    exact ⟨ballProj_mem p.x0 z hr, fun w hw => ballProj_obtuse p.x0 z w hr hw⟩
  · exact isCompact_closedBall _ _
  · exact mem_closedBall_self hr
  · show xstar ∈ closedBall p.x0 (p.D / 2)
    rw [mem_closedBall, dist_eq_norm]; exact hxs
  · intro x' hx y' hy
    let x : EuclideanSpace ℝ (Fin p.d) := x'
    let y : EuclideanSpace ℝ (Fin p.d) := y'
    have hx' : dist x p.x0 ≤ p.D / 2 := mem_closedBall.mp hx
    have hy' : dist y p.x0 ≤ p.D / 2 := mem_closedBall.mp hy
    rw [dist_eq_norm] at hx' hy'
    have key : ‖(x : EuclideanSpace ℝ (Fin p.d)) - y‖ ≤ p.D := by
      calc ‖(x : EuclideanSpace ℝ (Fin p.d)) - y‖ = ‖(x - p.x0) - (y - p.x0)‖ := by
            congr 1; abel
        _ ≤ ‖(x : EuclideanSpace ℝ (Fin p.d)) - p.x0‖ + ‖(y : EuclideanSpace ℝ (Fin p.d)) - p.x0‖ :=
            norm_sub_le _ _
        _ ≤ p.D := by linarith
    exact key
  · intro x _
    have h := hgrad x
    rw [← hgf x] at h
    exact h
  · intro x _ y _
    have h := hlip x y
    rw [← hgf x, ← hgf y] at h
    exact h
  · intro x _
    exact hmin x
  · intro x _
    have h := hquasar x
    rw [← hgf x] at h
    exact h
  · intro x _
    exact coin_integrable h0 h1 _
  · intro x hx
    have key : ∫ ω, g x ω ∂((coinLaw ν h0 h1 : ProbabilityMeasure Bool) : Measure Bool) = G x := by
      rw [coin_integral h0 h1]
      exact hmean x hx
    rw [← hgf x] at key
    exact key
  · intro x _
    exact coin_integrable h0 h1 _
  · intro x hx
    have key : ∫ ω, ‖g x ω - G x‖ ^ 2 ∂((coinLaw ν h0 h1 : ProbabilityMeasure Bool) :
        Measure Bool) ≤ p.σ ^ 2 := by
      rw [coin_integral h0 h1]
      simpa [smul_eq_mul] using hvar x hx
    rw [← hgf x] at key
    exact key

end LongTails.Proofs.QuasarHardAdmissible
