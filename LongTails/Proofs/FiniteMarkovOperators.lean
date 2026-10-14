import LongTails.Proofs.MarkovOperatorRenewal
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {S B : Type*} [Fintype S] [NormedAddCommGroup B] [NormedSpace ℂ B]

noncomputable def stateAverage (p : S → ℝ) : (S → B) →L[ℂ] B :=
  ∑ i, (p i : ℂ) • ContinuousLinearMap.proj i

noncomputable def stateConstant : B →L[ℂ] (S → B) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ B)

noncomputable def stateMix (Q : S → S → ℝ) : (S → B) →L[ℂ] (S → B) :=
  ContinuousLinearMap.pi (fun i => stateAverage (Q i))

noncomputable def stateAction (T : S → B →L[ℂ] B) : (S → B) →L[ℂ] (S → B) :=
  ContinuousLinearMap.pi (fun i => (T i).comp (ContinuousLinearMap.proj i))

@[simp] lemma stateAverage_apply (p : S → ℝ) (x : S → B) :
    stateAverage p x = ∑ i, (p i : ℂ) • x i := by simp [stateAverage]

omit [Fintype S] in
@[simp] lemma stateConstant_apply (x : B) (i : S) : stateConstant x i = x := rfl

@[simp] lemma stateMix_apply (Q : S → S → ℝ) (x : S → B) (i : S) :
    stateMix Q x i = ∑ j, (Q i j : ℂ) • x j := by simp [stateMix]

omit [Fintype S] in
@[simp] lemma stateAction_apply (T : S → B →L[ℂ] B) (x : S → B) (i : S) :
    stateAction T x i = T i (x i) := rfl

lemma norm_stateAverage_le (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ‖stateAverage (B := B) p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [stateAverage_apply, one_mul]
  calc
    _ ≤ ∑ i, ‖(p i : ℂ) • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (hp i)
    _ = ‖x‖ := by rw [← Finset.sum_mul, hs, one_mul]

lemma norm_stateConstant_le : ‖(stateConstant : B →L[ℂ] (S → B))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact le_rfl

lemma norm_stateMix_le (Q : S → S → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hs : ∀ i, ∑ j, Q i j = 1) : ‖stateMix (B := B) Q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  change ‖stateAverage (Q i) x‖ ≤ ‖x‖
  exact ((stateAverage (Q i)).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_stateAverage_le (B := B) (Q i) (hQ i) (hs i)) (norm_nonneg x))

lemma norm_stateAction_le (T : S → B →L[ℂ] B) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖stateAction T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg x))).mpr
  intro i
  change ‖T i (x i)‖ ≤ C * ‖x‖
  exact ((T i).le_opNorm _).trans (mul_le_mul (hT i) (norm_le_pi_norm x i)
    (norm_nonneg (x i)) hC)

lemma stateMix_constant (Q : S → S → ℝ) (hs : ∀ i, ∑ j, Q i j = 1) :
    (stateMix (B := B) Q).comp stateConstant = stateConstant := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, stateMix_apply, stateConstant_apply]
  rw [← Finset.sum_smul]
  have hc : ∑ j, (Q i j : ℂ) = 1 := by exact_mod_cast hs i
  rw [hc, one_smul]

lemma stateAverage_constant (p : S → ℝ) (hs : ∑ i, p i = 1) :
    (stateAverage (B := B) p).comp stateConstant = 1 := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, stateAverage_apply, stateConstant_apply, one_apply_eq_self]
  rw [← Finset.sum_smul]
  have hc : ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hs
  rw [hc, one_smul]

lemma stateAverage_mix (p : S → ℝ) (Q : S → S → ℝ)
    (hs : ∀ j, ∑ i, p i * Q i j = p j) :
    (stateAverage (B := B) p).comp (stateMix Q) = stateAverage p := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, stateAverage_apply, stateMix_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_smul]
  congr 1
  exact_mod_cast hs j

omit [Fintype S] in
lemma stateAction_sub_one (T : S → B →L[ℂ] B) :
    stateAction T - 1 = stateAction (fun i => T i - 1) := by
  ext x i
  simp [stateAction]

lemma stateMix_refresh (p : S → ℝ) (Q : S → S → ℝ) (q α : ℝ) :
    stateMix (B := B) (fun i j => q * Q i j + α * p j) =
      (q : ℂ) • stateMix Q + (α : ℂ) • stateConstant.comp (stateAverage p) := by
  ext x i
  simp [stateMix_apply, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma norm_stateAction_sub_one_le (T : S → B →L[ℂ] B) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i - 1‖ ≤ C) : ‖stateAction T - 1‖ ≤ C := by
  rw [stateAction_sub_one]
  exact norm_stateAction_le _ hC hT

lemma noncommutative_power_difference {A : Type*} [Ring A] (F C : A) (n : ℕ) :
    F ^ n - C ^ n = ∑ k ∈ Finset.range n, C ^ k * (F - C) * F ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    rw [pow_succ F, pow_succ C]
    calc
      _ = (F ^ n - C ^ n) * F + C ^ n * (F - C) := by noncomm_ring
      _ = (∑ k ∈ Finset.range n, C ^ k * (F - C) * F ^ (n - k)) + C ^ n * (F - C) := by
        rw [ih, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [mul_assoc, ← pow_succ]
        congr 2
        omega

section Transfer

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

noncomputable def transferCovariance (M : G →L[ℂ] B) (A : G →L[ℂ] G) (J : B →L[ℂ] G)
    (n : ℕ) : B →L[ℂ] B := M.comp ((A ^ n).comp J)

lemma transferCovariance_tail (D Q : G →L[ℂ] G) (J : B →L[ℂ] G)
    (hQJ : Q.comp J = J) (n : ℕ) :
    ((D * Q) ^ n).comp (D.comp J) = ((D * Q) ^ (n + 1)).comp J := by
  have hDJ : D.comp J = (D * Q).comp J := by
    change D.comp J = D.comp (Q.comp J)
    rw [hQJ]
  rw [hDJ, ← ContinuousLinearMap.comp_assoc, pow_succ]
  rfl

lemma transferCovariance_endpoint (D Q : G →L[ℂ] G) (M : G →L[ℂ] B) (J : B →L[ℂ] G)
    (hQJ : Q.comp J = J) (hMQ : M.comp Q = M) (n : ℕ) :
    transferCovariance M (D * Q) J (n + 2) - transferCovariance M (D * Q) J (n + 1) -
      transferCovariance M (D * Q) J (n + 1) + transferCovariance M (D * Q) J n =
      M.comp (((D - 1) * Q * (D * Q) ^ n * (D - 1)).comp J) := by
  have htail := transferCovariance_tail D Q J hQJ n
  have htail' := transferCovariance_tail D Q J hQJ (n + 1)
  symm
  simp only [sub_mul, mul_sub, one_mul, mul_one, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub]
  have hpow : D * Q * (D * Q) ^ n = (D * Q) ^ (n + 1) := (pow_succ' _ n).symm
  rw [hpow]
  change M.comp (((D * Q) ^ (n + 1)).comp (D.comp J)) -
    (M.comp Q).comp (((D * Q) ^ n).comp (D.comp J)) -
    (M.comp (((D * Q) ^ (n + 1)).comp J) -
      (M.comp Q).comp (((D * Q) ^ n).comp J)) = _
  rw [hMQ, htail, htail']
  simp only [transferCovariance]
  abel

lemma norm_power_contraction (A : G →L[ℂ] G) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (A ^ n), norm_nonneg A])

lemma norm_transferCovariance_le (M : G →L[ℂ] B) (A : G →L[ℂ] G) (J : B →L[ℂ] G)
    (hM : ‖M‖ ≤ 1) (hA : ‖A‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (n : ℕ) :
    ‖transferCovariance M A J n‖ ≤ 1 := by
  have hp : ‖A ^ n‖ ≤ 1 := norm_power_contraction A hA n
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have hc := ContinuousLinearMap.opNorm_comp_le (A ^ n) J
    have hc' : ‖(A ^ n).comp J‖ ≤ 1 := hc.trans (by nlinarith [norm_nonneg J, norm_nonneg (A ^ n)])
    nlinarith [norm_nonneg M, norm_nonneg ((A ^ n).comp J)])

lemma norm_transferCovariance_endpoint_le (D Q : G →L[ℂ] G) (M : G →L[ℂ] B)
    (J : B →L[ℂ] G) (hQJ : Q.comp J = J) (hMQ : M.comp Q = M)
    (hD : ‖D‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hM : ‖M‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    {b : ℝ} (hb : 0 ≤ b) (hsmall : ‖D - 1‖ ≤ b) (n : ℕ) :
    ‖transferCovariance M (D * Q) J (n + 2) - transferCovariance M (D * Q) J (n + 1) -
      transferCovariance M (D * Q) J (n + 1) + transferCovariance M (D * Q) J n‖ ≤ b ^ 2 := by
  rw [transferCovariance_endpoint D Q M J hQJ hMQ]
  have hDQ : ‖D * Q‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg D, norm_nonneg Q])
  have hp : ‖(D * Q) ^ n‖ ≤ 1 := norm_power_contraction (D * Q) hDQ n
  calc
    _ ≤ ‖M‖ * (‖D - 1‖ * ‖Q‖ * ‖(D * Q) ^ n‖ * ‖D - 1‖ * ‖J‖) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (norm_mul_le _ _).trans
      gcongr
      apply (norm_mul_le _ _).trans
      gcongr
      exact norm_mul_le _ _
    _ ≤ 1 * (b * 1 * 1 * b * 1) := by gcongr
    _ = b ^ 2 := by ring

lemma transferCovariance_duhamel (M₀ M : G →L[ℂ] B) (J : B →L[ℂ] G)
    (F C D : G →L[ℂ] G) (a : ℂ) (hF : F - C = a • D.comp (J.comp M)) (n : ℕ) :
    transferCovariance M₀ F J n - transferCovariance M₀ C J n =
      ∑ k ∈ Finset.range n, a • (M₀.comp ((C ^ k).comp (D.comp J))) *
        transferCovariance M F J (n - 1 - k) := by
  have hh := noncommutative_power_difference F C n
  rw [hF] at hh
  ext x
  have hh' := congrArg (fun V : G →L[ℂ] G => M₀ (V (J x))) hh
  simpa only [transferCovariance, ContinuousLinearMap.comp_apply, sub_apply, map_sub,
    sum_apply, map_sum, smul_apply, map_smul, mul_apply_eq_comp] using hh'

end Transfer

end OracleTemplate.MarkovProduct
