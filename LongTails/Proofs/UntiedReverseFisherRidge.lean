import LongTails.Proofs.SymmetricReverseFisherRidge
import LongTails.Proofs.SymmetricReverseFisherDynamics
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.UntiedReverseFisherRidge

open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherRadial
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherHermite
open LongTails.Proofs.SymmetricReverseFisherCoefficients

noncomputable def weightedSechDerivative (y : ℝ) : ℝ :=
  -4 * Real.tanh y * sech y ^ 2 - 2 * y * sech y ^ 4 + 4 * y * Real.tanh y ^ 2 * sech y ^ 2

noncomputable def sechSquaredThird (y : ℝ) : ℝ :=
  -8 * Real.tanh y * sech y ^ 2 + 24 * Real.tanh y * sech y ^ 4

noncomputable def ridgeSecond (a c : ℝ) : ℝ :=
  2 * sechMeanPrime a c +
    2 * (∫ y, weightedSechDerivative y ∂gaussianReal c (a ^ 2).toNNReal) -
    a ^ 2 * ∫ y, sechSquaredThird y ∂gaussianReal c (a ^ 2).toNNReal

lemma sech_sq_le_one' (y : ℝ) : sech y ^ 2 ≤ 1 := by
  simpa only [abs_of_nonneg (sq_nonneg (sech y))] using abs_sech_sq_le_one y

lemma tanh_abs_le (y : ℝ) : |Real.tanh y| ≤ 1 := (Real.abs_tanh_lt_one y).le

lemma hasDerivAt_weightedSech (y : ℝ) :
    HasDerivAt (fun x => sech x ^ 2 - 2 * x * Real.tanh x * sech x ^ 2)
      (weightedSechDerivative y) y := by
  have h1 := hasDerivAt_sech_sq y
  have h2 := (((hasDerivAt_id y).const_mul 2).mul (hasDerivAt_tanh y)).mul (hasDerivAt_sech_sq y)
  convert h1.sub h2 using 1
  · ext x; simp [mul_assoc]
  · unfold weightedSechDerivative
    simp only [id_eq, Pi.mul_apply]
    ring

lemma abs_weightedSechDerivative_le (y : ℝ) : |weightedSechDerivative y| ≤ 10 := by
  have hs := sech_sq_le_one' y
  have hs0 : 0 ≤ sech y ^ 2 := sq_nonneg _
  have ht := tanh_abs_le y
  have hy := abs_mul_sech_sq_le_one y
  have hy' : |y| * sech y ^ 2 ≤ 1 := by rwa [abs_mul, abs_of_nonneg hs0] at hy
  have ht2 : Real.tanh y ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.tanh y), sq_abs (Real.tanh y)]
  have e1 : |-4 * Real.tanh y * sech y ^ 2| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0]
    norm_num
    nlinarith [abs_nonneg (Real.tanh y)]
  have e2 : |2 * y * sech y ^ 4| ≤ 2 := by
    rw [show 2 * y * sech y ^ 4 = 2 * (y * sech y ^ 2) * sech y ^ 2 by ring, abs_mul, abs_mul,
      abs_of_nonneg hs0]
    norm_num
    nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) hs0]
  have e3 : |4 * y * Real.tanh y ^ 2 * sech y ^ 2| ≤ 4 := by
    rw [show 4 * y * Real.tanh y ^ 2 * sech y ^ 2 = 4 * (y * sech y ^ 2) * Real.tanh y ^ 2 by ring,
      abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.tanh y))]
    norm_num
    nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) hs0]
  unfold weightedSechDerivative
  calc
    _ ≤ |-4 * Real.tanh y * sech y ^ 2| + |2 * y * sech y ^ 4| +
        |4 * y * Real.tanh y ^ 2 * sech y ^ 2| := by
      have := abs_sub (-4 * Real.tanh y * sech y ^ 2) (2 * y * sech y ^ 4)
      have := abs_add_le (-4 * Real.tanh y * sech y ^ 2 - 2 * y * sech y ^ 4)
        (4 * y * Real.tanh y ^ 2 * sech y ^ 2)
      linarith
    _ ≤ 10 := by linarith

lemma hasDerivAt_sechSquaredSecond (y : ℝ) :
    HasDerivAt sechSquaredSecond (sechSquaredThird y) y := by
  have h := ((hasDerivAt_sech_sq y).const_mul 4).sub
    (((hasDerivAt_sech_sq y).pow 2).const_mul 6)
  convert h using 1
  · ext x; unfold sechSquaredSecond; simp only [Pi.sub_apply, Pi.pow_apply]; ring
  · unfold sechSquaredThird; ring

lemma abs_sechSquaredThird_le (y : ℝ) : |sechSquaredThird y| ≤ 32 := by
  have hs := sech_sq_le_one' y
  have hs0 : 0 ≤ sech y ^ 2 := sq_nonneg _
  have ht := tanh_abs_le y
  have e1 : |-8 * Real.tanh y * sech y ^ 2| ≤ 8 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0]
    norm_num
    nlinarith [abs_nonneg (Real.tanh y)]
  have e2 : |24 * Real.tanh y * sech y ^ 4| ≤ 24 := by
    rw [show sech y ^ 4 = sech y ^ 2 * sech y ^ 2 by ring, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hs0]
    norm_num
    nlinarith [abs_nonneg (Real.tanh y), mul_le_mul hs hs hs0 zero_le_one]
  unfold sechSquaredThird
  linarith [abs_add_le (-8 * Real.tanh y * sech y ^ 2) (24 * Real.tanh y * sech y ^ 4)]

lemma hasDerivAt_weightedSechPrime (a c : ℝ) :
    HasDerivAt (weightedSechPrime a)
      (∫ y, weightedSechDerivative y ∂gaussianReal c (a ^ 2).toNNReal) c :=
  hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal
    (fun y => sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2) weightedSechDerivative
    (by unfold weightedSechDerivative; fun_prop) hasDerivAt_weightedSech
    abs_mul_sech_sq_prime_le_three abs_weightedSechDerivative_le c

lemma hasDerivAt_sechMeanSecond (a c : ℝ) :
    HasDerivAt (sechMeanSecond a)
      (∫ y, sechSquaredThird y ∂gaussianReal c (a ^ 2).toNNReal) c :=
  hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal sechSquaredSecond sechSquaredThird
    (by unfold sechSquaredThird; fun_prop) hasDerivAt_sechSquaredSecond
    abs_sechSquaredSecond_le_two abs_sechSquaredThird_le c

lemma hasDerivAt_ridgeDerivative (a c : ℝ) :
    HasDerivAt (ridgeDerivative a) (ridgeSecond a c) c := by
  have h := (((hasDerivAt_sechMean a c).const_mul 2).add
    ((hasDerivAt_weightedSechPrime a c).const_mul 2)).sub
    ((hasDerivAt_sechMeanSecond a c).const_mul (a ^ 2))
  convert h using 1
  · ext t
    rfl
  · rfl

lemma integral_abs_le_gaussian (c : ℝ) (v : NNReal) (f : ℝ → ℝ) (_hf : Continuous f) {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) : |∫ y, f y ∂gaussianReal c v| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal c v)
    (ae_of_all _ (fun y => (show ‖f y‖ ≤ C by simpa [Real.norm_eq_abs] using hb y)))
  simpa [Real.norm_eq_abs] using h

lemma abs_sechMeanPrime_le (a c : ℝ) : |sechMeanPrime a c| ≤ 2 := by
  unfold sechMeanPrime
  rw [← integral_const_mul]
  exact integral_abs_le_gaussian c _ _ (by fun_prop)
    (fun y => by simpa [mul_assoc] using abs_sech_sq_derivative_le_two y)

lemma abs_ridgeSecond_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (c : ℝ) :
    |ridgeSecond a c| ≤ 32 := by
  have h1 := abs_sechMeanPrime_le a c
  have h2 := integral_abs_le_gaussian c (a ^ 2).toNNReal weightedSechDerivative
    (by unfold weightedSechDerivative; fun_prop) abs_weightedSechDerivative_le
  have h3 := integral_abs_le_gaussian c (a ^ 2).toNNReal sechSquaredThird
    (by unfold sechSquaredThird; fun_prop) abs_sechSquaredThird_le
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have h4 : |a ^ 2 * ∫ y, sechSquaredThird y ∂gaussianReal c (a ^ 2).toNNReal| ≤ 8 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    nlinarith [abs_nonneg (∫ y, sechSquaredThird y ∂gaussianReal c (a ^ 2).toNNReal)]
  have h5 : |2 * sechMeanPrime a c| ≤ 4 := by rw [abs_mul]; norm_num; linarith
  have h6 : |2 * ∫ y, weightedSechDerivative y ∂gaussianReal c (a ^ 2).toNNReal| ≤ 20 := by
    rw [abs_mul]; norm_num; linarith
  unfold ridgeSecond
  have k := abs_sub (2 * sechMeanPrime a c + 2 * ∫ y, weightedSechDerivative y ∂gaussianReal c (a ^ 2).toNNReal)
    (a ^ 2 * ∫ y, sechSquaredThird y ∂gaussianReal c (a ^ 2).toNNReal)
  have k2 := abs_add_le (2 * sechMeanPrime a c) (2 * ∫ y, weightedSechDerivative y ∂gaussianReal c (a ^ 2).toNNReal)
  linarith

lemma integrable_bounded_real (c : ℝ) (v : NNReal) (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) : Integrable f (gaussianReal c v) :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hb y))

lemma mul_tanh_nonneg (y : ℝ) : 0 ≤ y * Real.tanh y := by
  rcases le_total 0 y with hy | hy
  · exact mul_nonneg hy (by simpa using tanh_monotone hy)
  · exact mul_nonneg_of_nonpos_of_nonpos hy (by simpa using tanh_monotone hy)

lemma weightedSechPrime_le_sechMean (a c : ℝ) : weightedSechPrime a c ≤ sechMean a c := by
  unfold weightedSechPrime sechMean
  apply integral_mono
    (integrable_bounded_real c _ _ (by fun_prop) abs_mul_sech_sq_prime_le_three)
    (integrable_bounded_real c _ _ (by fun_prop) abs_sech_sq_le_one)
  intro y
  have h := mul_tanh_nonneg y
  have hs : 0 ≤ sech y ^ 2 := sq_nonneg _
  simp only
  nlinarith [mul_nonneg h hs]

lemma ridgeDerivative_upper {a : ℝ} (c : ℝ) : ridgeDerivative a c ≤ 4 + 2 * a ^ 2 := by
  have h1 := weightedSechPrime_le_sechMean a c
  have h2 := sechMean_le_one a c
  have h3 : |sechMeanSecond a c| ≤ 2 :=
    integral_abs_le_gaussian c _ _ (by unfold sechSquaredSecond; fun_prop) abs_sechSquaredSecond_le_two
  have h4 : -(a ^ 2 * sechMeanSecond a c) ≤ 2 * a ^ 2 := by
    nlinarith [neg_abs_le (sechMeanSecond a c), sq_nonneg a]
  unfold ridgeDerivative
  linarith

lemma ridgeDerivative_lower {a : ℝ} (c : ℝ) : -6 - 2 * a ^ 2 ≤ ridgeDerivative a c := by
  have h1 : |weightedSechPrime a c| ≤ 3 :=
    integral_abs_le_gaussian c _ _ (by fun_prop) abs_mul_sech_sq_prime_le_three
  have h2 := sechMean_nonneg a c
  have h3 : |sechMeanSecond a c| ≤ 2 :=
    integral_abs_le_gaussian c _ _ (by unfold sechSquaredSecond; fun_prop) abs_sechSquaredSecond_le_two
  have h4 : a ^ 2 * sechMeanSecond a c ≤ 2 * a ^ 2 := by
    nlinarith [le_abs_self (sechMeanSecond a c), sq_nonneg a]
  unfold ridgeDerivative
  linarith [neg_abs_le (weightedSechPrime a c)]

lemma abs_sub_le_of_deriv (f f' : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (f' x) x) {C : ℝ}
    (hb : ∀ x, |f' x| ≤ C) (x y : ℝ) : |f y - f x| ≤ C * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f')
    (s := Set.univ) (fun z _ => (hd z).hasDerivWithinAt)
    (fun z _ => by simpa [Real.norm_eq_abs] using hb z) convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using h

lemma abs_ridgeDerivative_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (c : ℝ) :
    |ridgeDerivative a c| ≤ 13 / 2 := by
  have h1 := ridgeDerivative_upper (a := a) c
  have h2 := ridgeDerivative_lower (a := a) c
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  rw [abs_le]
  constructor <;> linarith

lemma ridgeForce_lipschitz {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (x y : ℝ) :
    |ridgeForce a y - ridgeForce a x| ≤ 13 / 2 * |y - x| :=
  abs_sub_le_of_deriv (ridgeForce a) (ridgeDerivative a) (hasDerivAt_ridgeForce a)
    (abs_ridgeDerivative_le ha ha1) x y

lemma ridgeDerivative_lipschitz {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (x y : ℝ) :
    |ridgeDerivative a y - ridgeDerivative a x| ≤ 32 * |y - x| :=
  abs_sub_le_of_deriv (ridgeDerivative a) (ridgeSecond a) (hasDerivAt_ridgeDerivative a)
    (abs_ridgeSecond_le ha ha1) x y

lemma ridge_difference_crude {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (σ κ : ℝ) :
    |ridgeForce a (σ + κ) - ridgeForce a (σ - κ)| ≤ 13 * |κ| := by
  have h := ridgeForce_lipschitz ha ha1 (σ - κ) (σ + κ)
  rw [show σ + κ - (σ - κ) = 2 * κ by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
  linarith

lemma ridge_difference_shift {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (σ κ : ℝ) :
    |ridgeForce a (σ + κ) - ridgeForce a (σ - κ) - 2 * ridgeForce a κ| ≤ 64 * |κ| * |σ| := by
  have hd (t : ℝ) : HasDerivAt (fun t => ridgeForce a (t + κ) - ridgeForce a (t - κ))
      (ridgeDerivative a (t + κ) - ridgeDerivative a (t - κ)) t := by
    have h1 := (hasDerivAt_ridgeForce a (t + κ)).comp t ((hasDerivAt_id t).add_const κ)
    have h2 := (hasDerivAt_ridgeForce a (t - κ)).comp t ((hasDerivAt_id t).sub_const κ)
    convert h1.sub h2 using 1
    · ext x; simp
    · ring
  have hb (t : ℝ) : |ridgeDerivative a (t + κ) - ridgeDerivative a (t - κ)| ≤ 64 * |κ| := by
    have h := ridgeDerivative_lipschitz ha ha1 (t - κ) (t + κ)
    rw [show t + κ - (t - κ) = 2 * κ by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
    linarith
  have h := abs_sub_le_of_deriv _ _ hd hb 0 σ
  have h0 : ridgeForce a (0 + κ) - ridgeForce a (0 - κ) = 2 * ridgeForce a κ := by
    rw [zero_add, zero_sub, ridgeForce_neg]; ring
  rw [h0, sub_zero] at h
  exact h

lemma centre_contraction {a γ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2)
    (σ κ : ℝ) :
    |(1 - γ) * σ + γ / 4 * a ^ 2 * (ridgeForce a (σ + κ) + ridgeForce a (σ - κ))| ≤
      (1 - 7 * γ / 16) * |σ| := by
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have hd (t : ℝ) : HasDerivAt
      (fun t => (1 - γ) * t + γ / 4 * a ^ 2 * (ridgeForce a (t + κ) + ridgeForce a (t - κ)))
      ((1 - γ) + γ / 4 * a ^ 2 * (ridgeDerivative a (t + κ) + ridgeDerivative a (t - κ))) t := by
    have h1 := (hasDerivAt_ridgeForce a (t + κ)).comp t ((hasDerivAt_id t).add_const κ)
    have h2 := (hasDerivAt_ridgeForce a (t - κ)).comp t ((hasDerivAt_id t).sub_const κ)
    have h3 := ((hasDerivAt_id t).const_mul (1 - γ)).add ((h1.add h2).const_mul (γ / 4 * a ^ 2))
    convert h3 using 1
    · ext x; simp
    · ring
  have hb (t : ℝ) : |(1 - γ) + γ / 4 * a ^ 2 *
      (ridgeDerivative a (t + κ) + ridgeDerivative a (t - κ))| ≤ 1 - 7 * γ / 16 := by
    have u1 := ridgeDerivative_upper (a := a) (t + κ)
    have u2 := ridgeDerivative_upper (a := a) (t - κ)
    have l1 := ridgeDerivative_lower (a := a) (t + κ)
    have l2 := ridgeDerivative_lower (a := a) (t - κ)
    have hu : a ^ 2 * (ridgeDerivative a (t + κ) + ridgeDerivative a (t - κ)) ≤ 9 / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add u1 u2) (sq_nonneg a)]
    have hl : -(13 / 4) ≤ a ^ 2 * (ridgeDerivative a (t + κ) + ridgeDerivative a (t - κ)) := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add l1 l2) (sq_nonneg a)]
    rw [abs_le]
    constructor <;> nlinarith
  have h := abs_sub_le_of_deriv _ _ hd hb 0 σ
  have h0 : (1 - γ) * 0 + γ / 4 * a ^ 2 * (ridgeForce a (0 + κ) + ridgeForce a (0 - κ)) = 0 := by
    rw [zero_add, zero_sub, ridgeForce_neg]; ring
  rw [h0, sub_zero, sub_zero] at h
  exact h

end LongTails.Proofs.UntiedReverseFisherRidge
