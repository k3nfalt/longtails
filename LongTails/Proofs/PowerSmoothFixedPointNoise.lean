import LongTails.Setups.StochasticPowerSmoothFixedPoint
import LongTails.Proofs.SmoothBanachAnchoring
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

open MeasureTheory

namespace LongTails.Proofs.PowerSmoothFixedPointNoise

open LongTails.Setups.StochasticPowerSmoothFixedPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma centered_noise_bound {s K c v : ℝ} {j : E → E →L[ℝ] ℝ}
    (hsm : PowerSmooth E s K j) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (a : E) (ζ : Ω → E) (hζ : Integrable ζ P) (hz : ∫ ω, ζ ω ∂P = 0)
    (hm : Integrable (fun ω => ‖ζ ω‖ ^ s) P)
    (hv : ∫ ω, ‖ζ ω‖ ^ s ∂P ≤ v) :
    ∫⁻ ω, ENNReal.ofReal (‖a + c • ζ ω‖ ^ s) ∂P ≤
      ENNReal.ofReal (‖a‖ ^ s + K * c ^ s * v) := by
  let g : Ω → ℝ := fun ω => ‖a‖ ^ s + s * c * j a (ζ ω) + K * c ^ s * ‖ζ ω‖ ^ s
  have hi : Integrable (fun ω => j a (ζ ω)) P := (j a).integrable_comp hζ
  have hg : Integrable g P :=
    ((integrable_const _).add (hi.const_mul (s * c))).add (hm.const_mul _)
  have hpt : ∀ ω, ‖a + c • ζ ω‖ ^ s ≤ g ω := by
    intro ω
    have h := hsm a (c • ζ ω)
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
      Real.mul_rpow hc (norm_nonneg _)] at h
    dsimp [g]
    nlinarith
  have hgint : ∫ ω, g ω ∂P = ‖a‖ ^ s + K * c ^ s * ∫ ω, ‖ζ ω‖ ^ s ∂P := by
    have hi1 : Integrable (fun ω => s * c * j a (ζ ω)) P := hi.const_mul _
    have hi2 : Integrable (fun ω => K * c ^ s * ‖ζ ω‖ ^ s) P := hm.const_mul _
    calc
      ∫ ω, g ω ∂P = (∫ ω, ‖a‖ ^ s + s * c * j a (ζ ω) ∂P) +
          ∫ ω, K * c ^ s * ‖ζ ω‖ ^ s ∂P :=
        integral_add ((integrable_const _).add hi1) hi2
      _ = ((∫ _ : Ω, ‖a‖ ^ s ∂P) + ∫ ω, s * c * j a (ζ ω) ∂P) +
          ∫ ω, K * c ^ s * ‖ζ ω‖ ^ s ∂P := by
        rw [integral_add (integrable_const _) hi1]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, (j a).integral_comp_comm hζ, hz]
        simp
  calc
    ∫⁻ ω, ENNReal.ofReal (‖a + c • ζ ω‖ ^ s) ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (g ω) ∂P :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, g ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun ω =>
        (Real.rpow_nonneg (norm_nonneg _) _).trans (hpt ω))).symm
    _ ≤ ENNReal.ofReal (‖a‖ ^ s + K * c ^ s * v) := by
      rw [hgint]
      apply ENNReal.ofReal_le_ofReal
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv
        (mul_nonneg hK (Real.rpow_nonneg hc s)))

lemma contraction_power {s ρ r a : ℝ} (hs : 1 ≤ s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (h : a ≤ ρ * r) : a ^ s ≤ ρ * r ^ s := by
  calc
    a ^ s ≤ (ρ * r) ^ s := Real.rpow_le_rpow ha h (by linarith)
    _ = ρ ^ s * r ^ s := Real.mul_rpow hρ0 hr
    _ ≤ ρ * r ^ s := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _)
      rcases eq_or_lt_of_le hρ0 with hzero | hpos
      · simp [← hzero, Real.zero_rpow (by linarith : s ≠ 0)]
      · simpa using Real.rpow_le_rpow_of_exponent_ge hpos hρ1 hs

lemma picard_moment_bound {s K a η v : ℝ} {j : E → E →L[ℝ] ℝ}
    (hsm : PowerSmooth E s K j) (hs : 1 ≤ s) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hη : 0 ≤ η) (hstep : η * (1 + a) ≤ 1)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (b x u : E)
    (hu : (1 + a) • u - T u - b = 0) (G : Ω → E)
    (hG : Integrable G P) (hmean : ∫ ω, G ω ∂P = T x)
    (hm : Integrable (fun ω => ‖G ω - T x‖ ^ s) P)
    (hv : ∫ ω, ‖G ω - T x‖ ^ s ∂P ≤ v) :
    ∫⁻ ω, ENNReal.ofReal
        (‖(1 - η * (1 + a)) • x + η • G ω + η • b - u‖ ^ s) ∂P ≤
      ENNReal.ofReal ((1 - η * a) * ‖x - u‖ ^ s + K * η ^ s * v) := by
  let d := (1 - η * (1 + a)) • x + η • T x + η • b - u
  let ζ : Ω → E := fun ω => G ω - T x
  have hζ : Integrable ζ P := hG.sub (integrable_const _)
  have hz : ∫ ω, ζ ω ∂P = 0 := by
    dsimp [ζ]
    rw [integral_sub hG (integrable_const _), hmean, integral_const]
    simp
  have hroot : (1 - η * (1 + a)) • u + η • T u + η • b = u := by
    have he : (1 + a) • u = T u + b := by
      have := sub_eq_zero.mp hu
      calc
        (1 + a) • u = b + T u := sub_eq_iff_eq_add.mp this
        _ = T u + b := add_comm _ _
    calc
      _ = u - η • ((1 + a) • u) + η • (T u + b) := by module
      _ = u := by rw [he]; module
  have hd : ‖d‖ ≤ (1 - η * a) * ‖x - u‖ := by
    have := SmoothBanachAnchoring.damped_picard_contraction T hT a η hη hstep b x u
    rw [hroot] at this
    exact this
  have hp : ‖d‖ ^ s ≤ (1 - η * a) * ‖x - u‖ ^ s :=
    contraction_power hs (by nlinarith) (by nlinarith) (norm_nonneg _) (norm_nonneg _) hd
  have hdec : ∀ ω, (1 - η * (1 + a)) • x + η • G ω + η • b - u = d + η • ζ ω := by
    intro ω
    dsimp [d, ζ]
    module
  simp_rw [hdec]
  exact (centered_noise_bound hsm hK hη d ζ hζ hz hm hv).trans
    (ENNReal.ofReal_le_ofReal (add_le_add hp le_rfl))

end LongTails.Proofs.PowerSmoothFixedPointNoise
