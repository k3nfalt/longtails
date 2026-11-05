import LongTails.Algorithms.QuarticAcceleration
import LongTails.Proofs.CompositeCubicAcceleration

namespace LongTails.Proofs.QuarticAcceleration

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.CompositeCubicAcceleration hiding advance_certificate
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_certificate {F : E → ℝ} {C : Set E} (hF : ConvexOn ℝ C F)
    (state : State E) {z s xstar : E} {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hA : 0 ≤ state.weight)
    (hx : state.point ∈ C) (hz : z ∈ C) (hstar : xstar ∈ C)
    (hne : z ≠ center E μ state)
    (hsub : ∀ u ∈ C, F z + ⟪s, u - z⟫ ≤ F u)
    (hr : ‖s + (γ * ‖z - center E μ state‖ ^ 2) • (z - center E μ state)‖ ≤
      γ * ‖z - center E μ state‖ ^ 3 / 32) :
    let next := advance E μ γ state z s
    next.point ∈ C ∧ state.weight < next.weight ∧
      next.weight * (F next.point - F xstar) + ‖next.momentum - xstar‖ ^ 2 / 2 +
        (1 - (1 / 32 : ℝ) ^ 2) * (state.weight + trialWeight μ state.weight) *
          min μ (γ * ‖z - center E μ state‖ ^ 2) * ‖z - center E μ state‖ ^ 2 / 2 ≤
      state.weight * (F state.point - F xstar) + ‖state.momentum - xstar‖ ^ 2 / 2 := by
  let a := trialWeight μ state.weight
  let T := state.weight + a
  let lam := γ * ‖z - center E μ state‖ ^ 2
  let β := min 1 (μ / lam)
  have ha : 0 < a := trialWeight_pos hμ hA
  have hT : 0 < T := add_pos_of_nonneg_of_pos hA ha
  have hlam : 0 < lam := mul_pos hγ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  have hb := damping_properties hμ hlam
  have hweight : (1 - β) * state.weight + β * T = state.weight + β * a := by dsimp only [T]; ring
  have hnext : 0 < state.weight + β * a := add_pos_of_nonneg_of_pos hA (mul_pos hb.1 ha)
  have hmix := convex_mixture hF hx hz (mul_nonneg (sub_nonneg.mpr hb.2.1) hA)
    (mul_nonneg hb.1.le hT.le) (by rwa [hweight])
  rw [hweight] at hmix
  have hsx : F z - F state.point ≤ ⟪s, z - state.point⟫ := by
    have h := hsub state.point hx
    rw [show state.point - z = -(z - state.point) by abel, inner_neg_right] at h
    linarith
  have hss : F z - F xstar ≤ ⟪s, z - xstar⟫ := by
    have h := hsub xstar hstar
    rw [show xstar - z = -(z - xstar) by abel, inner_neg_right] at h
    linarith
  have hrsq : ‖s + lam • (z - center E μ state)‖ ^ 2 ≤
      (1 / 32 : ℝ) ^ 2 * lam ^ 2 * ‖z - center E μ state‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hr 2
    convert h using 1
    dsimp only [lam]
    ring
  have hpot := damped_potential hA ha.le hb.1.le rfl hweight.symm
    (center_identity state hμ hA) hmix.2 hsx hss hlam (damped_step_bound hμ hlam hA) hrsq
  change (advance E μ γ state z s).point ∈ C ∧ _
  refine ⟨hmix.1, ?_, ?_⟩
  · change state.weight < state.weight + β * a
    exact lt_add_of_pos_right _ (mul_pos hb.1 ha)
  · have he : β * lam = min μ lam := hb.2.2
    convert hpot using 1
    dsimp only [advance, damping, parameter, a, T, β, lam] at *
    rw [← he]
    ring


lemma nextGuess_pos {μ lam : ℝ} (hμ : 0 < μ) : 0 < nextGuess μ lam := by
  unfold nextGuess
  split_ifs <;> positivity

omit [InnerProductSpace ℝ E] in
lemma parameter_zero {γ : ℝ} (hγ : 0 < γ) (c y : E)
    (hz : parameter E γ c y = 0) : y = c := by
  unfold parameter at hz
  have hn : ‖y - c‖ = 0 := (sq_eq_zero_iff).mp ((mul_eq_zero.mp hz).resolve_left hγ.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma zero_residual_min {F : E → ℝ} {γ : ℝ} (hγ : 0 < γ) (c y g : E)
    (hsub : ∀ x, F y + ⟪g, x - y⟫ ≤ F x)
    (hz : parameter E γ c y = 0)
    (hr : ‖g + (parameter E γ c y) • (y - c)‖ ≤ γ * ‖y - c‖ ^ 3 / 32) :
    ∀ x, F y ≤ F x := by
  have hy := parameter_zero hγ c y hz
  have hg : g = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa [hz, hy] using hr
  simpa only [hg, inner_zero_left, add_zero] using hsub

lemma advance_down_weight (state : State E) {μ γ : ℝ} (hμ : 0 < μ) (hA : 0 ≤ state.weight)
    {y g : E} (hlam : 0 < parameter E γ (center E μ state) y)
    (hdown : parameter E γ (center E μ state) y ≤ μ) :
    (advance E μ γ state y g).weight = state.weight + trialWeight μ state.weight ∧
    1 / (2 * Real.sqrt μ) ≤ Real.sqrt (advance E μ γ state y g).weight - Real.sqrt state.weight := by
  have hb : damping E μ γ state y = 1 := by
    unfold damping
    exact min_eq_left ((le_div_iff₀ hlam).mpr (by simpa using hdown))
  have hw : (advance E μ γ state y g).weight = state.weight + trialWeight μ state.weight := by
    simp only [advance, hb, one_mul]
  exact ⟨hw, by rw [hw]; exact success_sqrt_progress hμ hA⟩

end LongTails.Proofs.QuarticAcceleration
