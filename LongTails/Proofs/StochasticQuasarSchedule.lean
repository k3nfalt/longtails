import LongTails.Algorithms.StochasticQuasarAcceleration
import LongTails.Proofs.GradientOnlyQuasarWeights
import LongTails.Proofs.GradientOnlyQuasarEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

open GradientOnlyQuasar

lemma ramp_slope_square (s : ℝ) : smoothRampSlope s ^ 2 ≤ 8 * smoothRamp s := by
  by_cases h0 : s ≤ 0
  · rw [smoothRamp_of_nonpos h0, smoothRampSlope_of_nonpos h0]
    norm_num
  by_cases h1 : 1 ≤ s
  · rw [smoothRamp_of_one_le h1, smoothRampSlope_of_one_le h1]
    norm_num
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s - 1 ≤ 0 := by linarith
  by_cases hh : s ≤ 1 / 2
  · simp only [smoothRamp, smoothRampSlope, max_eq_right hs0, max_eq_left hs1,
      max_eq_left (by linarith : s - 1 / 2 ≤ 0)]
    nlinarith
  · simp only [smoothRamp, smoothRampSlope, max_eq_right hs0, max_eq_left hs1,
      max_eq_right (by linarith : 0 ≤ s - 1 / 2)]
    nlinarith [sq_nonneg (1 - s)]

lemma acceleration_weight_pos {A0 a T : ℝ} (hA0 : 0 < A0) (ha : 0 ≤ a) (t : ℝ) :
    0 < accelerationWeight A0 a T t := by
  have hr := (smoothRamp_bounds (t / (2 * T))).1
  unfold accelerationWeight
  positivity

lemma acceleration_weight_initial (A0 a T : ℝ) : accelerationWeight A0 a T 0 = A0 := by
  simp only [accelerationWeight, zero_div, smoothRamp_of_nonpos le_rfl, mul_zero, add_zero]

lemma acceleration_weight_after {A0 a T t : ℝ} (hT : 0 < T) (ht : 2 * T ≤ t) :
    accelerationWeight A0 a T t = A0 + 2 * a * T ^ 2 := by
  have hr : 1 ≤ t / (2 * T) := (le_div_iff₀ (by positivity : 0 < 2 * T)).2 (by linarith)
  simp only [accelerationWeight, smoothRamp_of_one_le hr, mul_one]

lemma acceleration_slope_after {a T t : ℝ} (hT : 0 < T) (ht : 2 * T ≤ t) :
    accelerationWeightSlope a T t = 0 := by
  have hr : 1 ≤ t / (2 * T) := (le_div_iff₀ (by positivity : 0 < 2 * T)).2 (by linarith)
  simp only [accelerationWeightSlope, smoothRampSlope_of_one_le hr, mul_zero]

lemma acceleration_slope_nonneg {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ accelerationWeightSlope a T t := by
  exact mul_nonneg (mul_nonneg ha hT) (smoothRampSlope_bounds _).1

lemma acceleration_weight_deriv {A0 a T : ℝ} (hT : T ≠ 0) (t : ℝ) :
    HasDerivAt (accelerationWeight A0 a T) (accelerationWeightSlope a T t) t := by
  have hr := (hasDerivAt_smoothRamp (t / (2 * T))).comp t
    ((hasDerivAt_id t).div_const (2 * T))
  convert (hr.const_mul (2 * a * T ^ 2)).const_add A0 using 1
  · rfl
  · simp only [accelerationWeightSlope]
    field_simp

lemma continuous_acceleration_weight (A0 a T : ℝ) : Continuous (accelerationWeight A0 a T) := by
  unfold accelerationWeight
  exact continuous_const.add (continuous_const.mul
    (continuous_smoothRamp.comp (continuous_id.div_const _)))

lemma continuous_acceleration_slope (a T : ℝ) : Continuous (accelerationWeightSlope a T) := by
  unfold accelerationWeightSlope
  exact continuous_const.mul (continuous_smoothRampSlope.comp (continuous_id.div_const _))

lemma acceleration_slope_square {A0 a T : ℝ} (t : ℝ) :
    accelerationWeightSlope a T t ^ 2 ≤ 4 * a * (accelerationWeight A0 a T t - A0) := by
  have hr := mul_le_mul_of_nonneg_left (ramp_slope_square (t / (2 * T)))
    (sq_nonneg (a * T))
  dsimp only [accelerationWeightSlope, accelerationWeight]
  nlinarith

lemma acceleration_mirror_tuning {A0 a T γ q η : ℝ}
    (hA0 : 0 ≤ A0) (ha : 0 ≤ a) (hγ : 0 < γ)
    (htune : 4 * a = γ ^ 2 * q * η) (t : ℝ) :
    (accelerationWeightSlope a T t / γ) ^ 2 ≤ accelerationWeight A0 a T t * q * η := by
  have hs := acceleration_slope_square (A0 := A0) (a := a) (T := T) t
  have hm : 4 * a * (accelerationWeight A0 a T t - A0) ≤
      γ ^ 2 * (accelerationWeight A0 a T t * q * η) := by
    calc
      _ ≤ 4 * a * accelerationWeight A0 a T t := by nlinarith
      _ = _ := by rw [htune]; ring
  rw [div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hγ)).2 (by nlinarith)

section Flow

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma acceleration_flow_initial {A : ℝ → ℝ} {γ s : ℝ} (hA : A s ≠ 0) (x z : E) :
    accelerationFlow A γ s s x z = x := by
  simp [accelerationFlow, hA]

lemma acceleration_flow_deriv {A c : ℝ → ℝ} {γ s t : ℝ} (hγ : γ ≠ 0)
    (hAs : 0 < A s) (hAt : 0 < A t) (hAder : HasDerivAt A (γ * c t) t) (x z : E) :
    HasDerivAt (fun v => accelerationFlow A γ s v x z)
      ((c t / A t) • (z - accelerationFlow A γ s t x z)) t := by
  have hr : 0 < A s / A t := div_pos hAs hAt
  have hd := (hasDerivAt_const t (A s)).div hAder (ne_of_gt hAt)
  have hp : HasDerivAt (fun v => (A s / A v) ^ (1 / γ))
      (-(c t / A t) * (A s / A t) ^ (1 / γ)) t := by
    convert hd.rpow_const (Or.inl (ne_of_gt hr)) using 1
    simp only [Pi.div_apply]
    rw [Real.rpow_sub_one (ne_of_gt hr)]
    field_simp
    ring
  have hh := (hp.smul_const (x - z)).const_add z
  convert! hh using 1
  simp only [accelerationFlow]
  module

lemma acceleration_flow_energy_deriv [CompleteSpace E] {A c : ℝ → ℝ} {γ s t : ℝ} (hγ : γ ≠ 0)
    (hAs : 0 < A s) (hAt : 0 < A t) (hAder : HasDerivAt A (γ * c t) t)
    {f : E → ℝ} {G : E → E} (hf : ∀ y, HasGradientAt f (G y) y) (x z u : E) :
    HasDerivAt (fun v => weightedEnergy f u (A v) (accelerationFlow A γ s v x z) z)
      (γ * c t * (f (accelerationFlow A γ s t x z) - f u) +
        c t * ⟪G (accelerationFlow A γ s t x z), z - accelerationFlow A γ s t x z⟫) t := by
  have hy := acceleration_flow_deriv hγ hAs hAt hAder x z
  have hfy := (hf (accelerationFlow A γ s t x z)).hasFDerivAt.comp_hasDerivAt t hy
  have hh := (hAder.mul (hfy.sub_const (f u))).add_const (‖z - u‖ ^ 2 / 2)
  convert! hh using 1
  simp only [InnerProductSpace.toDual_apply_apply, inner_smul_right, Function.comp_apply]
  field_simp [ne_of_gt hAt]

lemma continuous_acceleration_flow {A : ℝ → ℝ} {γ : ℝ} (hA : Continuous A)
    (hAp : ∀ t, 0 < A t) (hγ : 0 ≤ γ) :
    Continuous (fun w : (ℝ × ℝ) × E × E => accelerationFlow A γ w.1.1 w.1.2 w.2.1 w.2.2) := by
  have hn := hA.comp (continuous_fst.fst : Continuous (fun w : (ℝ × ℝ) × E × E => w.1.1))
  have hd := hA.comp (continuous_fst.snd : Continuous (fun w : (ℝ × ℝ) × E × E => w.1.2))
  have hr := hn.div hd (fun w => ne_of_gt (hAp w.1.2))
  have hp := hr.rpow_const (fun _ => Or.inr (one_div_nonneg.mpr hγ))
  exact continuous_snd.snd.add (hp.smul (continuous_snd.fst.sub continuous_snd.snd))

end Flow

end OracleTemplate.StochasticQuasar
