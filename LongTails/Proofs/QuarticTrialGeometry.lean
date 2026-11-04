import LongTails.Proofs.QuarticProximalBounds
import LongTails.Proofs.QuarticTrialStages
import LongTails.Proofs.QuarticLocalTuning

namespace LongTails.Proofs.QuarticTrialGeometry

open LongTails.Algorithms.QuarticProximal
open LongTails.Proofs.TensorFreeModelTuning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma prox_min_center {f : E → ℝ} {γ : ℝ} (hγ : 0 < γ) (c u xstar : E)
    (hfmin : ∀ x, f xstar ≤ f x)
    (hmin : ∀ x, f u + penalty γ 0 c c u ≤ f x + penalty γ 0 c c x) :
    ‖u - c‖ ≤ ‖c - xstar‖ := by
  have hh := hmin xstar
  simp only [penalty, zero_div, zero_mul, add_zero, value] at hh
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (norm_nonneg _)
  apply (mul_le_mul_iff_right₀ hγ).mp
  rw [norm_sub_rev c xstar]
  linarith [hfmin u]

lemma model_radius_factor {γ L d r Q : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) (hQ : 3 ≤ Q)
    (hL : L ≤ γ * Q ^ 2) (hgap : γ * d ^ 4 ≤ 24 * L * r ^ 4) : d ≤ Q ^ 2 * r := by
  have h6 : 24 ≤ Q ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 6
    norm_num at hh
    linarith
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  apply (mul_le_mul_iff_right₀ hγ).mp
  calc
    γ * d ^ 4 ≤ 24 * L * r ^ 4 := hgap
    _ ≤ 24 * (γ * Q ^ 2) * r ^ 4 := by gcongr
    _ ≤ Q ^ 6 * (γ * Q ^ 2) * r ^ 4 := by gcongr
    _ = γ * (Q ^ 2 * r) ^ 4 := by ring

lemma initial_radius_factor {γ L Δ ρ r Q : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L) (hr : 0 ≤ r) (hQ : 3 ≤ Q)
    (hκ : L ≤ γ * Q ^ 2) (hinit : γ * Δ ^ 3 ≤ 1000 * L ^ 4 * r ^ 12)
    (hρ : ρ ^ 4 = 12 * Δ / γ) : ρ ≤ Q ^ 2 * r := by
  have hQpos : 0 < Q := by linarith
  have h16 : (1728000 : ℝ) ≤ Q ^ 16 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 16
    norm_num at hh
    linarith
  have hi : Δ ^ 3 ≤ 1000 * L ^ 4 * r ^ 12 / γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith [hinit]
  apply le_of_pow_le_pow_left₀ (by decide : (12 : ℕ) ≠ 0) (by positivity)
  calc
    ρ ^ 12 = (ρ ^ 4) ^ 3 := by ring
    _ = (12 * Δ / γ) ^ 3 := by rw [hρ]
    _ = (1728 / γ ^ 3) * Δ ^ 3 := by ring
    _ ≤ (1728 / γ ^ 3) * (1000 * L ^ 4 * r ^ 12 / γ) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1728000 * r ^ 12 / γ ^ 4) * L ^ 4 := by ring
    _ ≤ (1728000 * r ^ 12 / γ ^ 4) * (γ * Q ^ 2) ^ 4 := by gcongr
    _ = 1728000 * Q ^ 8 * r ^ 12 := by field_simp
    _ ≤ Q ^ 16 * Q ^ 8 * r ^ 12 := by gcongr
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma initial_points_radius {R Q : ℝ} (hR : 0 ≤ R) (hQ : 3 ≤ Q)
    (x0 c u z0 y0 : E) (hcenter : ‖c - x0‖ ≤ R * (Q ^ 8 + 1))
    (hmin : ‖u - c‖ ≤ R * Q ^ 8)
    (hz : ‖z0 - u‖ ≤ Q ^ 2 * ‖c - u‖) (hy : ‖y0 - u‖ ≤ Q ^ 2 * ‖z0 - u‖) :
    ‖c - x0‖ ≤ R * Q ^ 14 ∧
    ‖z0 - x0‖ ≤ R * Q ^ 14 ∧ ‖z0 - c‖ ≤ R * Q ^ 14 ∧
    ‖y0 - x0‖ ≤ R * Q ^ 13 ∧ ‖y0 - c‖ ≤ R * Q ^ 13 := by
  have hQpos : 0 < Q := by linarith
  have h1 : 1 ≤ Q := by linarith
  have huc : ‖c - u‖ ≤ R * Q ^ 8 := by simpa only [norm_sub_rev] using hmin
  have hzx : ‖z0 - u‖ ≤ R * Q ^ 10 := by
    have hh := hz.trans (mul_le_mul_of_nonneg_left huc (by positivity))
    convert hh using 1; ring
  have hyx : ‖y0 - u‖ ≤ R * Q ^ 12 := by
    have hh := hy.trans (mul_le_mul_of_nonneg_left hzx (by positivity))
    convert hh using 1; ring
  have hpow8 := polynomial_power_mono h1 (by decide : 8 ≤ 12)
  have hpow10 := polynomial_power_mono h1 (by decide : 10 ≤ 12)
  have hp1 : (1 : ℝ) ≤ Q ^ 12 := one_le_pow₀ h1
  have h13 : 3 * Q ^ 12 ≤ Q ^ 13 := by
    have hh := mul_le_mul_of_nonneg_right hQ (show 0 ≤ Q ^ 12 by positivity)
    convert hh using 1; ring
  have h14 := polynomial_power_mono h1 (by decide : 13 ≤ 14)
  have hcx : ‖c - x0‖ ≤ R * Q ^ 13 := by
    nlinarith [mul_le_mul_of_nonneg_left hpow8 hR, mul_le_mul_of_nonneg_left hp1 hR,
      mul_le_mul_of_nonneg_left h13 hR]
  have hux := norm_sub_le_norm_sub_add_norm_sub u c x0
  have hz0 := norm_sub_le_norm_sub_add_norm_sub z0 u x0
  have hzc := norm_sub_le_norm_sub_add_norm_sub z0 u c
  have hy0 := norm_sub_le_norm_sub_add_norm_sub y0 u x0
  have hyc := norm_sub_le_norm_sub_add_norm_sub y0 u c
  have h8 : R * Q ^ 8 ≤ R * Q ^ 12 := mul_le_mul_of_nonneg_left hpow8 hR
  have h10 : R * Q ^ 10 ≤ R * Q ^ 12 := mul_le_mul_of_nonneg_left hpow10 hR
  have h12 : R ≤ R * Q ^ 12 := by nlinarith [mul_le_mul_of_nonneg_left hp1 hR]
  have h13R := mul_le_mul_of_nonneg_left h13 hR
  have h14R := mul_le_mul_of_nonneg_left h14 hR
  refine ⟨hcx.trans h14R, ?_, ?_, ?_, ?_⟩ <;> nlinarith


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma stage_points_radius {R Q ρ : ℝ} (hR : 0 ≤ R) (hQ : 3 ≤ Q)
    (x0 c y0 y : E) (hρ : ρ ≤ R * Q ^ 10)
    (hy0 : ‖y0 - x0‖ ≤ R * Q ^ 13) (hyc : ‖y0 - c‖ ≤ R * Q ^ 13)
    (hy : ‖y - y0‖ ≤ 16 * ρ) :
    ‖y - x0‖ ≤ R * Q ^ 14 ∧ ‖y - c‖ ≤ R * Q ^ 14 := by
  have hQpos : 0 < Q := by linarith
  have h3 : 8 ≤ Q ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 3
    norm_num at hh
    linarith
  have hten : 16 * R * Q ^ 10 ≤ 2 * R * Q ^ 13 := by
    have hh := mul_le_mul_of_nonneg_right h3 (show 0 ≤ 2 * R * Q ^ 10 by positivity)
    convert hh using 1 <;> ring
  have hfourteen : 3 * R * Q ^ 13 ≤ R * Q ^ 14 := by
    have hh := mul_le_mul_of_nonneg_right hQ (show 0 ≤ R * Q ^ 13 by positivity)
    convert hh using 1 <;> ring
  have h₀ := norm_sub_le_norm_sub_add_norm_sub y y0 x0
  have h₁ := norm_sub_le_norm_sub_add_norm_sub y y0 c
  constructor <;> nlinarith


lemma model_prox_distance {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {γ L Q : ℝ} (hγ : 0 < γ) (hL : 0 < L) (hQ : 3 ≤ Q)
    (hκ : L ≤ γ * Q ^ 2) (c z s u : E)
    (hmin : ∀ x, f u + penalty γ 0 c c u ≤ f x + penalty γ 0 c c x)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) x -
      fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) y‖ ≤ L * ‖x - y‖)
    (hm : let F := fun v => f v + penalty γ 0 c c v
      ‖LongTails.Algorithms.TensorFreeModel.exactGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (fderiv ℝ (fderiv ℝ (gradient F)) z) L s‖ ≤ ‖gradient F (z + s)‖ / 6) :
    ‖z + s - u‖ ≤ Q ^ 2 * ‖z - u‖ := by
  let F := fun v => f v + penalty γ 0 c c v
  have hF : ContDiff ℝ 3 F := hf.add ((QuarticProximalGeometry.penalty_contDiff γ 0 c c).of_le le_top)
  have hcF : ConvexOn ℝ Set.univ F :=
    QuarticFiniteSum.component_convex (fun _ : Fin 1 => f) (fun _ => hf) (fun _ => hc) hγ.le le_rfl c c 0
  have hd := TensorFreeProximal.model_distance_bounds hF hcF hL hT z s u hmin hm
  have hmin' : ∀ x, f u + γ * value (u - c) ≤ f x + γ * value (x - c) := by
    intro x
    simpa [penalty] using hmin x
  have hg := QuarticFiniteSumStage.quartic_min_growth (hf.differentiable (by norm_num)) hc hγ.le c u (z + s) hmin'
  have hgap : γ * ‖z + s - u‖ ^ 4 ≤ 24 * L * ‖z - u‖ ^ 4 := by
    have hh := hd.2
    dsimp [F, penalty] at hh
    simp only [zero_div, zero_mul, add_zero] at hh
    linarith
  exact model_radius_factor hγ (norm_nonneg _) hQ hκ hgap

end LongTails.Proofs.QuarticTrialGeometry
