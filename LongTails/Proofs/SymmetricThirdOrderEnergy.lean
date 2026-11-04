import LongTails.Proofs.CompositeCubicAcceleration
import Mathlib.MeasureTheory.Function.L2Space

namespace LongTails.Proofs.SymmetricThirdOrderEnergy

open LongTails.Proofs.CompositeCubicAcceleration
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residual_dissipation_error {s d : E} {lam σ c b W : ℝ}
    (hlam : 0 < lam) (hb : 0 ≤ b) (hcb : c * lam ≤ b)
    (hr : ‖s + lam • d‖ ^ 2 ≤ σ ^ 2 * lam ^ 2 * ‖d‖ ^ 2 + W) :
    b * ⟪s, d⟫ + c * ‖s‖ ^ 2 / 2 ≤
      -(1 - σ ^ 2) * b * lam * ‖d‖ ^ 2 / 2 + b * W / (2 * lam) := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
    inner_smul_right] at hr
  have h₁ := mul_le_mul_of_nonneg_left hr hb
  have h₂ := mul_le_mul_of_nonneg_right hcb (sq_nonneg ‖s‖)
  have he : lam * (b * W / (2 * lam)) = b * W / 2 := by field_simp
  apply (mul_le_mul_iff_left₀ hlam).mp
  nlinarith only [h₁, h₂, he]

lemma damped_potential_error {x v y z xstar s : E}
    {A a T β Anew lam σ W Fx Fz Fstar Fnew : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hT : T = A + a)
    (hweight : Anew = (1 - β) * A + β * T)
    (hcenter : T • y = A • x + a • v)
    (hconvex : Anew * Fnew ≤ (1 - β) * A * Fx + β * T * Fz)
    (hsx : Fz - Fx ≤ ⟪s, z - x⟫)
    (hsstar : Fz - Fstar ≤ ⟪s, z - xstar⟫)
    (hlam : 0 < lam) (hstep : (β * a) ^ 2 * lam ≤ β * T)
    (hr : ‖s + lam • (z - y)‖ ^ 2 ≤ σ ^ 2 * lam ^ 2 * ‖z - y‖ ^ 2 + W) :
    Anew * (Fnew - Fstar) + ‖v - (β * a) • s - xstar‖ ^ 2 / 2 +
      (1 - σ ^ 2) * β * T * lam * ‖z - y‖ ^ 2 / 2 ≤
      A * (Fx - Fstar) + ‖v - xstar‖ ^ 2 / 2 + β * T * W / (2 * lam) := by
  have hbalance : A • (z - x) + a • (z - xstar) =
      T • (z - y) + a • (v - xstar) := by
    calc
      _ = (A + a) • z - (A • x + a • v) + a • (v - xstar) := by module
      _ = _ := by rw [← hT, ← hcenter]; module
  have hi := congrArg (fun w => ⟪s, w⟫) hbalance
  simp only [inner_add_right, inner_smul_right] at hi
  have hx := mul_le_mul_of_nonneg_left hsx hA
  have hs := mul_le_mul_of_nonneg_left hsstar ha
  have hbase : T * (Fz - Fstar) - A * (Fx - Fstar) ≤
      T * ⟪s, z - y⟫ + a * ⟪s, v - xstar⟫ := by
    rw [hT] at hi ⊢
    nlinarith only [hx, hs, hi]
  have hmul := mul_le_mul_of_nonneg_left hbase hβ
  have hm := norm_momentum v xstar s (β * a)
  have ht0 : 0 ≤ β * T := mul_nonneg hβ (by linarith)
  have hd := residual_dissipation_error hlam ht0 hstep hr
  rw [hweight] at hconvex ⊢
  nlinarith only [hmul, hm, hd, hconvex]

lemma noisy_momentum (v xstar s ξ : E) (b : ℝ) :
    ‖v - b • (s + ξ) - xstar‖ ^ 2 / 2 =
      ‖v - b • s - xstar‖ ^ 2 / 2 - b * ⟪ξ, v - b • s - xstar⟫ + b ^ 2 * ‖ξ‖ ^ 2 / 2 := by
  have hh := norm_momentum (v - b • s) xstar ξ b
  have he : v - b • (s + ξ) - xstar = v - b • s - b • ξ - xstar := by module
  rw [he]
  linarith

lemma projected_noisy_potential {x v y z xstar s ξ vnew : E}
    {A a T β Anew lam σ W Fx Fz Fstar Fnew : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hT : T = A + a)
    (hweight : Anew = (1 - β) * A + β * T)
    (hcenter : T • y = A • x + a • v)
    (hconvex : Anew * Fnew ≤ (1 - β) * A * Fx + β * T * Fz)
    (hsx : Fz - Fx ≤ ⟪s, z - x⟫)
    (hsstar : Fz - Fstar ≤ ⟪s, z - xstar⟫)
    (hlam : 0 < lam) (hstep : (β * a) ^ 2 * lam ≤ β * T)
    (hr : ‖s + lam • (z - y)‖ ^ 2 ≤ σ ^ 2 * lam ^ 2 * ‖z - y‖ ^ 2 + W)
    (hproj : ‖vnew - xstar‖ ≤ ‖v - (β * a) • (s + ξ) - xstar‖) :
    Anew * (Fnew - Fstar) + ‖vnew - xstar‖ ^ 2 / 2 +
      (1 - σ ^ 2) * β * T * lam * ‖z - y‖ ^ 2 / 2 ≤
      A * (Fx - Fstar) + ‖v - xstar‖ ^ 2 / 2 + β * T * W / (2 * lam) -
      (β * a) * ⟪ξ, v - (β * a) • s - xstar⟫ + (β * a) ^ 2 * ‖ξ‖ ^ 2 / 2 := by
  have hh := damped_potential_error hA ha hβ hT hweight hcenter hconvex hsx hsstar hlam hstep hr
  have hm := noisy_momentum v xstar s ξ (β * a)
  have hp : ‖vnew - xstar‖ ^ 2 ≤ ‖v - (β * a) • (s + ξ) - xstar‖ ^ 2 := by gcongr
  linarith

lemma residual_square_bound {r lam a t : ℝ} (ht : 0 ≤ t) (hres : t ≤ (3 / 16) * lam * r + 35 * a) :
    t ^ 2 ≤ (1 / 4) * lam ^ 2 * r ^ 2 + 2450 * a ^ 2 := by
  have hh : t ^ 2 ≤ ((3 / 16) * lam * r + 35 * a) ^ 2 := by gcongr
  nlinarith [sq_nonneg ((3 / 16) * lam * r - 35 * a), sq_nonneg (lam * r)]

lemma error_coefficients {δ lam b c Amax W V : ℝ}
    (hδ : 0 < δ) (hlam : δ ≤ lam) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hweight : b ≤ Amax) (hstep : c * lam ≤ b) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    b * W / (2 * lam) + c * V / 2 ≤ Amax * (W + V) / (2 * δ) := by
  have hl : 0 < lam := hδ.trans_le hlam
  have hA : 0 ≤ Amax := hb.trans hweight
  have hcoef : b / (2 * lam) ≤ Amax / (2 * δ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * lam) (by positivity : 0 < 2 * δ)).mpr
    have h₁ := mul_le_mul_of_nonneg_right hweight hδ.le
    have h₂ := mul_le_mul_of_nonneg_left hlam hA
    nlinarith
  have hcδ : c / 2 ≤ Amax / (2 * δ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
    have hh := mul_le_mul_of_nonneg_left hlam hc
    nlinarith
  have hw := mul_le_mul_of_nonneg_right hcoef hW
  have hv := mul_le_mul_of_nonneg_right hcδ hV
  calc
    _ = (b / (2 * lam)) * W + (c / 2) * V := by ring
    _ ≤ (Amax / (2 * δ)) * W + (Amax / (2 * δ)) * V := add_le_add hw hv
    _ = _ := by ring

lemma damped_weight_bound {A a T β Anew : ℝ} (hA : 0 ≤ A) (hβ : β ≤ 1)
    (hT : T = A + a) (hnew : Anew = A + β * a) : β * T ≤ Anew := by
  have hh := mul_nonneg (sub_nonneg.mpr hβ) hA
  rw [hT, hnew]
  nlinarith

lemma stopping_overshoot {A μ X β : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (hAX : A < X) (hμX : 1 ≤ μ * X) (hβ : β ≤ 1) :
    A + β * LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ A ≤ 3 * X := by
  have hX : 0 < X := hA.trans_lt hAX
  have hu := trial_weight_upper hμ hA (by linarith : A ≤ 2 * X) hμX
  have hp := trialWeight_pos hμ hA
  have hb := mul_le_mul_of_nonneg_right hβ hp.le
  nlinarith

open MeasureTheory

lemma expected_energy_increment [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Integrable ξ P) (hmean : ∫ ω, ξ ω ∂P = 0)
    (hξ₂ : Integrable (fun ω => ‖ξ ω‖ ^ 2) P)
    {V δ lam B b Amax W Eold : ℝ} (hvar : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hδ : 0 < δ) (hlam : δ ≤ lam) (hB : 0 ≤ B) (hweight : B ≤ Amax)
    (hstep : b ^ 2 * lam ≤ B) (hW : 0 ≤ W) (w : E) {Enew : Ω → ℝ}
    (hEi : Integrable Enew P)
    (hE : ∀ ω, Enew ω ≤ Eold + B * W / (2 * lam) -
      b * ⟪ξ ω, w⟫ + b ^ 2 * ‖ξ ω‖ ^ 2 / 2) :
    (∫ ω, Enew ω ∂P) ≤ Eold + Amax * (W + V) / (2 * δ) := by
  have hinner : (∫ ω, ⟪ξ ω, w⟫ ∂P) = 0 := by
    simp_rw [real_inner_comm]
    rw [integral_inner hξ, hmean]
    simp
  have hi := (hξ.inner_const w).const_mul b
  have h₂ := (hξ₂.const_mul (b ^ 2)).div_const 2
  have hR := ((integrable_const (Eold + B * W / (2 * lam))).sub hi).add h₂
  have hh := integral_mono hEi hR hE
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  have h₀ : Integrable (fun ω => Eold + B * W / (2 * lam) - b * ⟪ξ ω, w⟫) P :=
    (integrable_const _).sub hi
  rw [integral_add h₀ h₂,
    integral_sub (integrable_const (Eold + B * W / (2 * lam))) hi, integral_const_mul, hinner,
    integral_div, integral_const_mul] at hh
  simp at hh
  have hV : 0 ≤ V := (integral_nonneg (fun _ => sq_nonneg _)).trans hvar
  have hm := mul_le_mul_of_nonneg_left hvar (sq_nonneg b)
  have hc := error_coefficients hδ hlam hB (sq_nonneg b) hweight hstep hW hV
  linarith

end LongTails.Proofs.SymmetricThirdOrderEnergy
