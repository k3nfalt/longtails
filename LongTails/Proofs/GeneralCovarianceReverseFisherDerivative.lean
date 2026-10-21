import LongTails.Proofs.GeneralCovarianceReverseFisherScore
import LongTails.Proofs.GeneralCovarianceReverseFisherDensity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherDerivative

open LongTails.Proofs.GeneralCovarianceReverseFisherScore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

abbrev Means (E : Type*) (n : ℕ) :=
  PiLp 2 (fun _ : Fin n => E)

noncomputable def proj (i : Fin n) : Means E n →L[ℝ] E := PiLp.proj 2 (fun _ : Fin n => E) i

omit [FiniteDimensional ℝ E] in
lemma proj_apply (i : Fin n) (θ : Means E n) : proj i θ = θ i := rfl

lemma hasFDerivAt_weight_param (A : E ≃L[ℝ] E) (x : E) (θ : Means E n) (i : Fin n) :
    HasFDerivAt (fun η : Means E n => weight A (fun j => η j) x i)
      (weight A (fun j => θ j) x i • (innerSL ℝ (precision A (x - θ i))).comp (proj i)) θ := by
  have h1 := (hasFDerivAt_exponent A x (θ i)).comp θ (proj (E := E) i).hasFDerivAt
  have h2 := h1.exp
  convert h2 using 1
  · ext η
    simp only [weight, Function.comp_apply, proj_apply]
    rw [← norm_neg, ← map_neg, neg_sub]
  · simp only [weight, Function.comp_apply, proj_apply]
    rw [← norm_neg (A.symm (θ i - x)), ← map_neg, neg_sub]

lemma hasFDerivAt_weight_point (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) (i : Fin k) :
    HasFDerivAt (fun y => weight A c y i)
      (weight A c x i • innerSL ℝ (precision A (c i - x))) x :=
  (hasFDerivAt_exponent A (c i) x).exp

lemma precision_symm (A : E ≃L[ℝ] E) (u v : E) :
    ⟪precision A u, v⟫ = ⟪u, precision A v⟫ := by
  rw [precision_inner, inner_precision]

noncomputable def numer (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) : E :=
  ∑ i, weight A (fun j => θ j) x i • (θ i - t)

noncomputable def center (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) : E :=
  posteriorMean A (fun j => θ j) x - t

noncomputable def integrand (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) : ℝ :=
  ‖precision A (numer A t θ x)‖ ^ 2 * (total A (fun j => θ j) x)⁻¹

noncomputable def psi (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) (i : Fin n) : ℝ :=
  2 * ⟪precision A (center A t θ x), precision A (θ i - t)⟫ - ‖precision A (center A t θ x)‖ ^ 2

noncomputable def integrandDeriv (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    Means E n →L[ℝ] ℝ :=
  ∑ i, weight A (fun j => θ j) x i •
    (((2 : ℝ) • innerSL ℝ (precision A (precision A (center A t θ x))) +
      psi A t θ x i • innerSL ℝ (precision A (x - θ i))).comp (proj i))

omit [FiniteDimensional ℝ E] in
lemma numer_eq [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    numer A t θ x = total A (fun j => θ j) x • center A t θ x := by
  have hb := (total_pos A (fun j => θ j) x).ne'
  unfold numer center posteriorMean resp
  rw [smul_sub, Finset.smul_sum]
  simp_rw [smul_sub, Finset.sum_sub_distrib, smul_smul]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    field_simp
  · rw [← Finset.sum_smul]
    rfl

lemma integrand_eq [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    integrand A t θ x = total A (fun j => θ j) x * ‖precision A (center A t θ x)‖ ^ 2 := by
  have hb := (total_pos A (fun j => θ j) x).ne'
  unfold integrand
  rw [numer_eq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (total_pos A _ x)]
  field_simp

lemma hasFDerivAt_integrand [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    HasFDerivAt (fun η : Means E n => integrand A t η x) (integrandDeriv A t θ x) θ := by
  have hb : HasFDerivAt (fun η : Means E n => total A (fun j => η j) x)
      (∑ i, weight A (fun j => θ j) x i • (innerSL ℝ (precision A (x - θ i))).comp (proj i)) θ :=
    HasFDerivAt.fun_sum (fun i _ => hasFDerivAt_weight_param A x θ i)
  have hnum : HasFDerivAt (fun η : Means E n => numer A t η x)
      (∑ i, (weight A (fun j => θ j) x i • proj i +
        (weight A (fun j => θ j) x i • (innerSL ℝ (precision A (x - θ i))).comp (proj i)).smulRight
          (θ i - t))) θ := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hasFDerivAt_weight_param A x θ i).fun_smul ((proj (E := E) i).hasFDerivAt.sub_const t)
  have hN := ((precision A).hasFDerivAt.comp θ hnum).norm_sq
  have hinv := (hasDerivAt_inv (total_pos A (fun j => θ j) x).ne').comp_hasFDerivAt θ hb
  have hH := hN.mul hinv
  unfold integrand
  convert hH using 1
  · funext η
    simp only [Pi.mul_apply, Function.comp_apply]
  ext h
  have hbpos := total_pos A (fun j => θ j) x
  set b := total A (fun j => θ j) x with hbdef
  set D := center A t θ x with hD
  have e1 : ((∑ i, (weight A (fun j => θ j) x i • proj i +
      (weight A (fun j => θ j) x i • (innerSL ℝ (precision A (x - θ i))).comp (proj i)).smulRight
        (θ i - t)) : Means E n →L[ℝ] E)) h =
      ∑ i, (weight A (fun j => θ j) x i • h i +
        (weight A (fun j => θ j) x i * ⟪precision A (x - θ i), h i⟫) • (θ i - t)) := by
    simp [proj_apply, map_sub, inner_sub_left]
  have e2 : ((∑ i, weight A (fun j => θ j) x i • (innerSL ℝ (precision A (x - θ i))).comp (proj i) :
      Means E n →L[ℝ] ℝ)) h =
      ∑ i, weight A (fun j => θ j) x i * ⟪precision A (x - θ i), h i⟫ := by
    simp [proj_apply, map_sub, inner_sub_left]
  have e3 : integrandDeriv A t θ x h = ∑ i, weight A (fun j => θ j) x i *
      (2 * ⟪precision A D, precision A (h i)⟫ + psi A t θ x i * ⟪precision A (x - θ i), h i⟫) := by
    simp only [integrandDeriv, sum_apply, smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, add_apply, innerSL_apply_apply, proj_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [precision_symm A (precision A _)]
  have e4 : ⟪precision A D, precision A (∑ i, (weight A (fun j => θ j) x i • h i +
        (weight A (fun j => θ j) x i * ⟪precision A (x - θ i), h i⟫) • (θ i - t)))⟫ =
      ∑ i, weight A (fun j => θ j) x i * (⟪precision A D, precision A (h i)⟫ +
        ⟪precision A (x - θ i), h i⟫ * ⟪precision A D, precision A (θ i - t)⟫) := by
    simp only [map_sum, map_add, map_smul, inner_sum, inner_add_right, inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [e3]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  rw [e1, e2, numer_eq, ← hbdef, ← hD, map_smul, inner_smul_left, conj_trivial, e4,
    norm_smul, Real.norm_eq_abs, abs_of_pos hbpos]
  simp only [psi, ← hD]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp
  ring

lemma integrandDeriv_apply (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) (h : Means E n) :
    integrandDeriv A t θ x h = ∑ i, weight A (fun j => θ j) x i *
      (2 * ⟪precision A (precision A (center A t θ x)), h i⟫ +
        psi A t θ x i * ⟪precision A (x - θ i), h i⟫) := by
  simp only [integrandDeriv, sum_apply, smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, add_apply, innerSL_apply_apply, proj_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] in
lemma center_eq [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    center A t θ x = ∑ i, resp A (fun j => θ j) x i • (θ i - t) := by
  unfold center posteriorMean
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_resp, one_smul]

omit [FiniteDimensional ℝ E] in
lemma resp_le_one [NeZero n] (A : E ≃L[ℝ] E) (θ : Means E n) (x : E) (i : Fin n) :
    resp A (fun j => θ j) x i ≤ 1 := by
  rw [← sum_resp A (fun j => θ j) x]
  exact Finset.single_le_sum (fun j _ => resp_nonneg A _ x j) (Finset.mem_univ i)

noncomputable def spread (t : E) (θ : Means E n) : ℝ := ∑ i, ‖θ i - t‖

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma norm_sub_le_spread (t : E) (θ : Means E n) (i : Fin n) : ‖θ i - t‖ ≤ spread t θ :=
  Finset.single_le_sum (f := fun j => ‖θ j - t‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma spread_nonneg (t : E) (θ : Means E n) : 0 ≤ spread t θ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [FiniteDimensional ℝ E] in
lemma norm_center_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    ‖center A t θ x‖ ≤ spread t θ := by
  rw [center_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (resp_nonneg A _ x i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (resp_le_one A θ x i)

lemma abs_psi_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) (i : Fin n) :
    |psi A t θ x i| ≤ 3 * ‖precision A‖ ^ 2 * spread t θ ^ 2 := by
  have hc := norm_center_le A t θ x
  have hi := norm_sub_le_spread t θ i
  have hP1 : ‖precision A (center A t θ x)‖ ≤ ‖precision A‖ * spread t θ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  have hP2 : ‖precision A (θ i - t)‖ ≤ ‖precision A‖ * spread t θ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
  have hn1 := norm_nonneg (precision A (center A t θ x))
  have hn2 := norm_nonneg (precision A (θ i - t))
  have hin := abs_real_inner_le_norm (precision A (center A t θ x)) (precision A (θ i - t))
  unfold psi
  have hprod : ‖precision A (center A t θ x)‖ * ‖precision A (θ i - t)‖ ≤
      (‖precision A‖ * spread t θ) ^ 2 := by
    rw [sq]; exact mul_le_mul hP1 hP2 hn2 (mul_nonneg (norm_nonneg _) (spread_nonneg t θ))
  have hsq : ‖precision A (center A t θ x)‖ ^ 2 ≤ (‖precision A‖ * spread t θ) ^ 2 :=
    pow_le_pow_left₀ hn1 hP1 2
  rw [abs_le] at hin ⊢
  constructor <;> nlinarith

lemma norm_integrandDeriv_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) :
    ‖integrandDeriv A t θ x‖ ≤ ∑ i, weight A (fun j => θ j) x i *
      (2 * ‖precision A‖ ^ 2 * spread t θ +
        3 * ‖precision A‖ ^ 3 * spread t θ ^ 2 * ‖x - θ i‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos A _ x i).le (by
      have := spread_nonneg t θ; positivity)))
  intro h
  rw [integrandDeriv_apply, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_pos (weight_pos A _ x i), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (weight_pos A _ x i).le
  have hh : ‖h i‖ ≤ ‖h‖ := PiLp.norm_apply_le h i
  have hc := norm_center_le A t θ x
  have hs := spread_nonneg t θ
  have hpn := norm_nonneg (precision A)
  have h1 : |⟪precision A (precision A (center A t θ x)), h i⟫| ≤
      ‖precision A‖ ^ 2 * spread t θ * ‖h‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul ?_ hh (norm_nonneg _) (by positivity)
    calc ‖precision A (precision A (center A t θ x))‖
        ≤ ‖precision A‖ * ‖precision A (center A t θ x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖precision A‖ * (‖precision A‖ * ‖center A t θ x‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hpn
      _ ≤ ‖precision A‖ ^ 2 * spread t θ := by
          rw [← mul_assoc, ← sq]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  have h2 : |⟪precision A (x - θ i), h i⟫| ≤ ‖precision A‖ * ‖x - θ i‖ * ‖h‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (ContinuousLinearMap.le_opNorm _ _) hh (norm_nonneg _) (by positivity)
  have h3 := abs_psi_le A t θ x i
  calc |2 * ⟪precision A (precision A (center A t θ x)), h i⟫ +
        psi A t θ x i * ⟪precision A (x - θ i), h i⟫|
      ≤ 2 * |⟪precision A (precision A (center A t θ x)), h i⟫| +
          |psi A t θ x i| * |⟪precision A (x - θ i), h i⟫| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_two]
    _ ≤ 2 * (‖precision A‖ ^ 2 * spread t θ * ‖h‖) +
          (3 * ‖precision A‖ ^ 2 * spread t θ ^ 2) * (‖precision A‖ * ‖x - θ i‖ * ‖h‖) := by
        gcongr
    _ = _ := by ring

lemma le_two_exp_sq (s : ℝ) : s ≤ 2 * Real.exp (s ^ 2 / 4) := by
  have h := Real.add_one_le_exp (s ^ 2 / 4)
  nlinarith [sq_nonneg (s / 2 - 1)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_sq_shift_ge (a b : E) : ‖a‖ ^ 2 / 2 - ‖b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a + b) - b‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le _ _
  have h2 := norm_nonneg a
  nlinarith [sq_nonneg (‖a + b‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg b]

omit [FiniteDimensional ℝ E] in
lemma weight_poly_le (A : E ≃L[ℝ] E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (x c c' : E)
    (hc : ‖c' - c‖ ≤ 1) :
    Real.exp (-‖A.symm (x - c')‖ ^ 2 / 2) * (α + β * ‖x - c'‖) ≤
      (α + 2 * β * ‖(A : E →L[ℝ] E)‖) * Real.exp (‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4) *
        Real.exp (-(1 / 8) * ‖A.symm (x - c)‖ ^ 2) := by
  set u := ‖A.symm (x - c')‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have hxa : ‖x - c'‖ ≤ ‖(A : E →L[ℝ] E)‖ * u := by
    have : x - c' = (A : E →L[ℝ] E) (A.symm (x - c')) := by simp
    rw [this]
    exact ContinuousLinearMap.le_opNorm _ _
  have hA := norm_nonneg (A : E →L[ℝ] E)
  have h1 : Real.exp (-u ^ 2 / 2) * (α + β * ‖x - c'‖) ≤
      Real.exp (-u ^ 2 / 4) * (α + 2 * β * ‖(A : E →L[ℝ] E)‖) := by
    have e1 : Real.exp (-u ^ 2 / 2) ≤ Real.exp (-u ^ 2 / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
    have e2 : u * Real.exp (-u ^ 2 / 2) ≤ 2 * Real.exp (-u ^ 2 / 4) := by
      have := le_two_exp_sq u
      have hsplit : Real.exp (-u ^ 2 / 4) = Real.exp (-u ^ 2 / 2) * Real.exp (u ^ 2 / 4) := by
        rw [← Real.exp_add]; ring_nf
      rw [hsplit]
      nlinarith [Real.exp_pos (-u ^ 2 / 2), Real.exp_pos (u ^ 2 / 4)]
    have hpos := Real.exp_pos (-u ^ 2 / 2)
    calc Real.exp (-u ^ 2 / 2) * (α + β * ‖x - c'‖)
        ≤ Real.exp (-u ^ 2 / 2) * (α + β * (‖(A : E →L[ℝ] E)‖ * u)) := by gcongr
      _ = α * Real.exp (-u ^ 2 / 2) + β * ‖(A : E →L[ℝ] E)‖ * (u * Real.exp (-u ^ 2 / 2)) := by ring
      _ ≤ α * Real.exp (-u ^ 2 / 4) + β * ‖(A : E →L[ℝ] E)‖ * (2 * Real.exp (-u ^ 2 / 4)) := by
          gcongr
      _ = _ := by ring
  have h2 : -u ^ 2 / 4 ≤ ‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4 + -(1 / 8) * ‖A.symm (x - c)‖ ^ 2 := by
    have hs := norm_sq_shift_ge (A.symm (x - c)) (A.symm (c - c'))
    have hsum : A.symm (x - c) + A.symm (c - c') = A.symm (x - c') := by
      rw [← map_add]; congr 1; abel
    rw [hsum] at hs
    have hb : ‖A.symm (c - c')‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ := by
      have := ContinuousLinearMap.le_opNorm (A.symm : E →L[ℝ] E) (c - c')
      rw [norm_sub_rev] at hc
      exact this.trans (mul_le_of_le_one_right (norm_nonneg _) hc)
    have hb2 : ‖A.symm (c - c')‖ ^ 2 ≤ ‖(A.symm : E →L[ℝ] E)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [← hu] at hs
    nlinarith
  have h3 : Real.exp (-u ^ 2 / 4) ≤ Real.exp (‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4) *
      Real.exp (-(1 / 8) * ‖A.symm (x - c)‖ ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr h2
  have hk : 0 ≤ α + 2 * β * ‖(A : E →L[ℝ] E)‖ := by positivity
  calc Real.exp (-u ^ 2 / 2) * (α + β * ‖x - c'‖)
      ≤ Real.exp (-u ^ 2 / 4) * (α + 2 * β * ‖(A : E →L[ℝ] E)‖) := h1
    _ ≤ (Real.exp (‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4) *
          Real.exp (-(1 / 8) * ‖A.symm (x - c)‖ ^ 2)) * (α + 2 * β * ‖(A : E →L[ℝ] E)‖) := by
        gcongr
    _ = _ := by ring

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma spread_le_of_dist (t : E) {θ η : Means E n} (h : ‖η - θ‖ ≤ 1) :
    spread t η ≤ spread t θ + n := by
  unfold spread
  have : ∀ i, ‖η i - t‖ ≤ ‖θ i - t‖ + 1 := by
    intro i
    have hi : ‖η i - θ i‖ ≤ 1 := by
      have := PiLp.norm_apply_le (η - θ) i
      simp only [PiLp.sub_apply] at this
      linarith
    calc ‖η i - t‖ = ‖(η i - θ i) + (θ i - t)‖ := by congr 1; abel
      _ ≤ ‖η i - θ i‖ + ‖θ i - t‖ := norm_add_le _ _
      _ ≤ ‖θ i - t‖ + 1 := by linarith
  calc ∑ i, ‖η i - t‖ ≤ ∑ i, (‖θ i - t‖ + 1) := Finset.sum_le_sum (fun i _ => this i)
    _ = ∑ i, ‖θ i - t‖ + n := by simp [Finset.sum_add_distrib]

omit [FiniteDimensional ℝ E] in
lemma continuous_weight (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (i : Fin k) :
    Continuous (fun x => weight A c x i) := by
  unfold weight
  fun_prop

omit [FiniteDimensional ℝ E] in
lemma continuous_total (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) :
    Continuous (fun x => total A c x) :=
  continuous_finsetSum _ (fun i _ => continuous_weight A c i)

omit [FiniteDimensional ℝ E] in
lemma continuous_resp (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (i : Fin k) :
    Continuous (fun x => resp A c x i) :=
  (continuous_weight A c i).div (continuous_total A c) (fun x => (total_pos A c x).ne')

omit [FiniteDimensional ℝ E] in
lemma continuous_posteriorMean (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) :
    Continuous (fun x => posteriorMean A c x) :=
  continuous_finsetSum _ (fun i _ => (continuous_resp A c i).smul continuous_const)

omit [FiniteDimensional ℝ E] in
lemma continuous_center [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    Continuous (fun x => center A t θ x) :=
  (continuous_posteriorMean A _).sub continuous_const

lemma continuous_psi [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (i : Fin n) :
    Continuous (fun x => psi A t θ x i) := by
  have hc := (precision A).continuous.comp (continuous_center A t θ)
  unfold psi
  exact (continuous_const.mul (hc.inner continuous_const)).sub (hc.norm.pow 2)

lemma continuous_integrandDeriv [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    Continuous (fun x => integrandDeriv A t θ x) := by
  unfold integrandDeriv
  refine continuous_finsetSum _ (fun i _ => (continuous_weight A _ i).smul ?_)
  have h1 : Continuous (fun x => innerSL ℝ (precision A (precision A (center A t θ x)))) :=
    (innerSL ℝ).continuous.comp ((precision A).continuous.comp
      ((precision A).continuous.comp (continuous_center A t θ)))
  have h2 : Continuous (fun x => innerSL ℝ (precision A (x - θ i))) :=
    (innerSL ℝ).continuous.comp ((precision A).continuous.comp (continuous_id.sub continuous_const))
  exact (((continuous_const (y := (2 : ℝ))).smul h1).add
    ((continuous_psi A t θ i).smul h2)).clm_comp
    continuous_const

lemma continuous_integrand [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    Continuous (fun x => integrand A t θ x) := by
  simp_rw [integrand_eq]
  exact (continuous_total A _).mul
    (((precision A).continuous.comp (continuous_center A t θ)).norm.pow 2)

section Integral

variable [MeasurableSpace E] [BorelSpace E]

open LongTails.Proofs.GeneralCovarianceReverseFisherDensity

lemma integrable_weight (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (i : Fin k) :
    Integrable (fun x => weight A c x i) := by
  refine (integrable_exp_quad A (c i) (1 / 2) (by norm_num)).congr (ae_of_all _ (fun x => ?_))
  simp only [weight]
  ring_nf

lemma integrable_weight_mul (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (i : Fin k)
    {F : E → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Integrable (fun x => weight A c x i * F x) :=
  (integrable_weight A c i).mul_bdd hF.aestronglyMeasurable
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hC x))

lemma integrable_integrand [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    Integrable (fun x => integrand A t θ x) := by
  have hb : Integrable (fun x => ∑ i, weight A (fun j => θ j) x i *
      (‖precision A‖ * spread t θ) ^ 2) :=
    integrable_finsetSum _ (fun i _ => (integrable_weight A _ i).mul_const _)
  refine hb.mono' (continuous_integrand A t θ).aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  rw [integrand_eq, Real.norm_eq_abs, abs_of_nonneg (by
    have := (total_pos A (fun j => θ j) x).le; positivity), ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (total_pos A _ x).le
  have h := (ContinuousLinearMap.le_opNorm (precision A) (center A t θ x)).trans
    (mul_le_mul_of_nonneg_left (norm_center_le A t θ x) (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

noncomputable def dominator (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) : ℝ :=
  ∑ i, (2 * ‖precision A‖ ^ 2 * (spread t θ + n) +
      2 * (3 * ‖precision A‖ ^ 3 * (spread t θ + n) ^ 2) * ‖(A : E →L[ℝ] E)‖) *
    Real.exp (‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4) * Real.exp (-(1 / 8) * ‖A.symm (x - θ i)‖ ^ 2)

lemma integrable_dominator (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    Integrable (fun x => dominator A t θ x) :=
  integrable_finsetSum _ (fun i _ =>
    (integrable_exp_quad A (θ i) (1 / 8) (by norm_num)).const_mul _)

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_integrandDeriv_le_dominator [NeZero n] (A : E ≃L[ℝ] E) (t : E) {θ η : Means E n}
    (hd : ‖η - θ‖ ≤ 1) (x : E) :
    ‖integrandDeriv A t η x‖ ≤ dominator A t θ x := by
  set α := 2 * ‖precision A‖ ^ 2 * (spread t θ + n)
  set β := 3 * ‖precision A‖ ^ 3 * (spread t θ + n) ^ 2
  have hs0 := spread_nonneg t θ
  have hα : 0 ≤ α := by positivity
  have hβ : 0 ≤ β := by positivity
  have hsp := spread_le_of_dist t hd
  have hsp0 := spread_nonneg t η
  refine (norm_integrandDeriv_le A t η x).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hi : ‖η i - θ i‖ ≤ 1 := by
    have := PiLp.norm_apply_le (η - θ) i
    simp only [PiLp.sub_apply] at this
    linarith
  have hw := weight_poly_le A hα hβ x (θ i) (η i) hi
  refine le_trans ?_ hw
  unfold weight
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hpn := norm_nonneg (precision A)
  have hxn := norm_nonneg (x - η i)
  have hα' : 2 * ‖precision A‖ ^ 2 * spread t η ≤ α := by
    have : 0 ≤ 2 * ‖precision A‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hsp this
  have hβ' : 3 * ‖precision A‖ ^ 3 * spread t η ^ 2 ≤ β := by
    have : 0 ≤ 3 * ‖precision A‖ ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0 hsp 2) this
  gcongr

theorem hasFDerivAt_integral_integrand [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) :
    HasFDerivAt (fun η : Means E n => ∫ x, integrand A t η x)
      (∫ x, integrandDeriv A t θ x) θ :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := dominator A t θ)
    (Metric.ball_mem_nhds θ one_pos)
    (Filter.Eventually.of_forall (fun η => (continuous_integrand A t η).aestronglyMeasurable))
    (integrable_integrand A t θ) (continuous_integrandDeriv A t θ).aestronglyMeasurable
    (ae_of_all _ (fun x η hη => norm_integrandDeriv_le_dominator A t
      (by rw [Metric.mem_ball, dist_eq_norm] at hη; exact hη.le) x))
    (integrable_dominator A t θ)
    (ae_of_all _ (fun x η _ => hasFDerivAt_integrand A t η x))

theorem integral_integrandDeriv_apply_eq [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n)
    (h : Means E n) :
    (∫ x, integrandDeriv A t θ x) h = ∫ x, integrandDeriv A t θ x h := by
  set ε := 1 / (‖h‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hline : HasDerivAt (fun s : ℝ => θ + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add θ
  have h1 : HasDerivAt (fun s : ℝ => ∫ x, integrand A t (θ + s • h) x)
      ((∫ x, integrandDeriv A t θ x) h) 0 :=
    (hasFDerivAt_integral_integrand A t θ).comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline
      (by simp)
  have hsmall : ∀ s ∈ Metric.ball (0 : ℝ) ε, ‖(θ + s • h) - θ‖ ≤ 1 := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖h‖ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
      _ ≤ 1 := by
        rw [hε, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
  have h2 : HasDerivAt (fun s : ℝ => ∫ x, integrand A t (θ + s • h) x)
      (∫ x, integrandDeriv A t (θ + (0 : ℝ) • h) x h) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := (0 : ℝ))
      (F := fun s x => integrand A t (θ + s • h) x)
      (F' := fun s x => integrandDeriv A t (θ + s • h) x h)
      (bound := fun x => dominator A t θ x * ‖h‖) (Metric.ball_mem_nhds 0 hε0)
      (Filter.Eventually.of_forall (fun s =>
        (continuous_integrand A t (θ + s • h)).aestronglyMeasurable))
      (by simpa using integrable_integrand A t θ)
      ((continuous_integrandDeriv A t (θ + (0 : ℝ) • h)).clm_apply
        continuous_const).aestronglyMeasurable
      (ae_of_all _ (fun x s hs => ?_)) ((integrable_dominator A t θ).mul_const _)
      (ae_of_all _ (fun x s _ => ?_))).2
    · rw [Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
        (norm_integrandDeriv_le_dominator A t (hsmall s hs) x) (norm_nonneg _))
    · have hl : HasDerivAt (fun s : ℝ => θ + s • h) h s := by
        simpa using ((hasDerivAt_id s).smul_const h).const_add θ
      exact (hasFDerivAt_integrand A t (θ + s • h) x).comp_hasDerivAt s hl
  have := h1.unique h2
  simpa using this

end Integral

end LongTails.Proofs.GeneralCovarianceReverseFisherDerivative
