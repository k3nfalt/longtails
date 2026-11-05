import LongTails.Proofs.QuarticFiniteSumStage
import LongTails.Proofs.TensorFreeProximal
import LongTails.Proofs.GradientOnlyExecution

namespace LongTails.Proofs.QuarticProximalBounds

open LongTails.Algorithms.QuarticProximal
open scoped RealInnerProductSpace

lemma growth_gradient_bounds {γ d a gap : ℝ} (hγ : 0 ≤ γ) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hg : 0 ≤ gap) (hlow : γ * d ^ 4 ≤ 12 * gap) (hu : gap ≤ a * d) :
    γ * d ^ 3 ≤ 12 * a ∧ γ * gap ^ 3 ≤ 12 * a ^ 4 := by
  by_cases hz : d = 0
  · subst d
    have hgap : gap = 0 := by nlinarith
    rw [hgap]
    constructor <;> nlinarith [sq_nonneg (a ^ 2)]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    have hdg : γ * d ^ 3 ≤ 12 * a := by
      apply (mul_le_mul_iff_left₀ hdpos).mp
      nlinarith
    refine ⟨hdg, ?_⟩
    calc
      γ * gap ^ 3 ≤ γ * (a * d) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg hu 3) hγ
      _ = (γ * d ^ 3) * a ^ 3 := by ring
      _ ≤ (12 * a) * a ^ 3 := mul_le_mul_of_nonneg_right hdg (by positivity)
      _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma quartic_gradient_bounds {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {γ : ℝ} (hγ : 0 ≤ γ) (c u y : E)
    (hmin : ∀ x, f u + penalty γ 0 c c u ≤ f x + penalty γ 0 c c x) :
    let F := fun x => f x + penalty γ 0 c c x
    γ * ‖y - u‖ ^ 3 ≤ 12 * ‖gradient F y‖ ∧
      γ * (F y - F u) ^ 3 ≤ 12 * ‖gradient F y‖ ^ 4 := by
  let F := fun x => f x + penalty γ 0 c c x
  have hmin' : ∀ x, f u + γ * value (u - c) ≤ f x + γ * value (x - c) := by
    intro x
    simpa [penalty] using hmin x
  have hlower := QuarticFiniteSumStage.quartic_min_growth hf hc hγ c u y hmin'
  have hlower' : γ * ‖y - u‖ ^ 4 ≤ 12 * (F y - F u) := by
    simp only [F, penalty, zero_div, zero_mul, add_zero]
    linarith
  have hsupp := QuarticProximalGeometry.add_penalty_support
    (fun x => (hf x).hasGradientAt) hc hγ c c y u (μ := 0)
  have he : gradient F y = gradient f y + penaltyGrad γ 0 c c y :=
    (QuarticProximalGeometry.add_penalty_hasGradientAt (fun x => (hf x).hasGradientAt) γ 0 c c y).gradient
  rw [← he] at hsupp
  have hi : ⟪gradient F y, u - y⟫ = -⟪gradient F y, y - u⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [hi] at hsupp
  have hupper : F y - F u ≤ ‖gradient F y‖ * ‖y - u‖ := by
    have hin := real_inner_le_norm (gradient F y) (y - u)
    change F y - ⟪gradient F y, y - u⟫ + γ * ‖u - y‖ ^ 4 / 12 + 0 * ‖u - y‖ ^ 2 / 2 ≤ F u at hsupp
    nlinarith [show 0 ≤ γ * ‖u - y‖ ^ 4 by positivity]
  exact growth_gradient_bounds hγ (norm_nonneg _) (norm_nonneg _)
    (sub_nonneg.mpr (hmin y)) hlower' hupper


lemma computed_gap_bound {γ a gap : ℝ} (hγ : 0 < γ)
    (hgap : γ * gap ^ 3 ≤ 12 * a ^ 4) :
    gap ≤ 3 * (a ^ 4 / γ) ^ (1 / 3 : ℝ) := by
  have he := GradientOnlyExecution.rpow_third_cube (by positivity : 0 ≤ a ^ 4 / γ)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, he]
  have hh : gap ^ 3 * γ ≤ 27 * a ^ 4 := by nlinarith [sq_nonneg (a ^ 2)]
  have hh' := (le_div_iff₀ hγ).mpr hh
  convert hh' using 1; ring

lemma initial_gap_envelope {γ L a D r : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L)
    (hD : 0 ≤ D)
    (ha : a ^ 4 ≤ 2 * L * D ^ 3) (hDupper : D ≤ 2 * L * r ^ 4) :
    3 * (a ^ 4 / γ) ^ (1 / 3 : ℝ) ≤
      10 * (L ^ 4 / γ) ^ (1 / 3 : ℝ) * r ^ 4 := by
  have he₁ := GradientOnlyExecution.rpow_third_cube (by positivity : 0 ≤ a ^ 4 / γ)
  have he₂ := GradientOnlyExecution.rpow_third_cube (by positivity : 0 ≤ L ^ 4 / γ)
  have hpow := pow_le_pow_left₀ hD hDupper 3
  have ha' : a ^ 4 ≤ 16 * L ^ 4 * r ^ 12 := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * L by positivity)
    nlinarith
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  simp only [mul_pow, he₁, he₂]
  have hh : 27 * a ^ 4 ≤ 1000 * L ^ 4 * r ^ 12 := by
    nlinarith [show 0 ≤ L ^ 4 * r ^ 12 by positivity]
  have hh' := (div_le_div_iff_of_pos_right hγ).mpr hh
  convert hh' using 1 <;> ring


lemma small_gradient_accuracy {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {γ R B tol ε : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R)
    (hsmall : 32 * tol ≤ γ * R ^ 3) (haccuracy : 33 * tol * (B + R) ≤ ε)
    (c y xstar : E) (hcstar : ‖c - xstar‖ ≤ B)
    (hg : ‖gradient (fun x => f x + penalty γ 0 c c x) y‖ ≤ tol)
    (hres : γ * ‖y - c‖ ^ 3 ≤ 32 * tol) : f y - f xstar ≤ ε := by
  let F := fun x => f x + penalty γ 0 c c x
  have htol : 0 ≤ tol := (norm_nonneg _).trans hg
  have hdist : ‖y - c‖ ≤ R := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hR
    exact (mul_le_mul_iff_right₀ hγ).mp (hres.trans hsmall)
  have he : gradient F y = gradient f y + γ • grad (y - c) := by
    have hh := (QuarticProximalGeometry.add_penalty_hasGradientAt (fun x => (hf x).hasGradientAt) γ 0 c c y).gradient
    simpa [F, penaltyGrad] using hh
  have hn : ‖γ • grad (y - c)‖ = γ * ‖y - c‖ ^ 3 := by
    rw [grad, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hγ, abs_of_nonneg (sq_nonneg _)]
    ring
  have hgrad : ‖gradient f y‖ ≤ 33 * tol := by
    have hh := norm_sub_le (gradient F y) (γ • grad (y - c))
    rw [he, add_sub_cancel_right, hn] at hh
    change ‖gradient F y‖ ≤ tol at hg
    rw [he] at hg
    linarith
  have hdiststar : ‖y - xstar‖ ≤ B + R := by
    have hh := norm_add_le (y - c) (c - xstar)
    have he : y - c + (c - xstar) = y - xstar := by module
    rw [he] at hh
    linarith
  have hsupp := OracleTemplate.Gradient.convex_support hc
    (fun x => (hf x).hasGradientAt) y xstar
  have hi : ⟪gradient f y, xstar - y⟫ = -⟪gradient f y, y - xstar⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [hi] at hsupp
  have hh : ‖gradient f y‖ * ‖y - xstar‖ ≤ 33 * tol * (B + R) := by gcongr
  have hin := real_inner_le_norm (gradient f y) (y - xstar)
  linarith


lemma terminal_residual {γ a d r s : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (htriangle : r ≤ d + s) (hgrowth : γ * d ^ 3 ≤ 12 * a)
    (ha : a ≤ γ * r ^ 3 / 2048) : a ≤ γ * s ^ 3 / 32 := by
  have hdist : d ≤ r / 4 := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
    apply (mul_le_mul_iff_right₀ hγ).mp
    nlinarith [show 0 ≤ γ * r ^ 3 by positivity]
  have hfour : r ≤ 4 * s := by linarith
  have hp := pow_le_pow_left₀ hr hfour 3
  have hh := mul_le_mul_of_nonneg_left hp hγ.le
  nlinarith

end LongTails.Proofs.QuarticProximalBounds
