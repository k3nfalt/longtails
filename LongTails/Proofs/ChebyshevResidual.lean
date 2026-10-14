import LongTails.Proofs.ChebyshevRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Polynomial
open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

noncomputable def residualNumerator : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 - 4 * X
  | n + 2 => (2 - 4 * X) * residualNumerator (n + 1) - residualNumerator n

lemma residualNumerator_eval_zero (T : ℕ) :
    (residualNumerator T).eval 0 = 2 * (T : ℝ) + 1 := by
  induction T using Nat.twoStepInduction with
  | zero => simp [residualNumerator]
  | one => norm_num [residualNumerator]
  | more n ih1 ih2 =>
    simp only [residualNumerator, eval_sub, eval_mul, eval_ofNat, eval_X, mul_zero,
      sub_zero, ih1, ih2]
    push_cast
    ring

lemma residualNumerator_degree (T : ℕ) : (residualNumerator T).natDegree ≤ T := by
  induction T using Nat.twoStepInduction with
  | zero => simp [residualNumerator]
  | one => simp only [residualNumerator]; compute_degree
  | more n ih1 ih2 =>
    rw [residualNumerator]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hlin : (2 - 4 * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      omega
    · omega

lemma residualNumerator_sin (T : ℕ) (θ : ℝ) :
    (residualNumerator T).eval (Real.sin θ ^ 2) * Real.sin θ =
      Real.sin ((2 * (T : ℝ) + 1) * θ) := by
  induction T using Nat.twoStepInduction with
  | zero => simp [residualNumerator]
  | one =>
    norm_num [residualNumerator]
    rw [Real.sin_three_mul]
    ring
  | more n ih1 ih2 =>
    have hsum := Real.sin_add_sin ((2 * ((n : ℝ) + 2) + 1) * θ)
      ((2 * (n : ℝ) + 1) * θ)
    have havg : (((2 * ((n : ℝ) + 2) + 1) * θ) + ((2 * (n : ℝ) + 1) * θ)) / 2 =
        (2 * ((n : ℝ) + 1) + 1) * θ := by ring
    have hdiff : (((2 * ((n : ℝ) + 2) + 1) * θ) - ((2 * (n : ℝ) + 1) * θ)) / 2 =
        2 * θ := by ring
    rw [havg, hdiff, Real.cos_two_mul] at hsum
    have htrig := Real.sin_sq_add_cos_sq θ
    simp only [residualNumerator, eval_sub, eval_mul, eval_ofNat, eval_X, sub_mul,
      mul_assoc, ih1, ih2]
    push_cast
    linear_combination -hsum - 4 * Real.sin ((2 * ((n : ℝ) + 1) + 1) * θ) * htrig

lemma abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) :
    |Real.sin ((n : ℝ) * θ)| ≤ (n : ℝ) * |Real.sin θ| := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    Real.abs_sin_sum_le (Finset.range n) (fun _ => θ)

noncomputable def residualFactors (T : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range T, (1 - C ((root T (i + 1))⁻¹) * X)

lemma residualFactors_eval (T : ℕ) (z : ℝ) :
    (residualFactors T).eval z = ∏ i ∈ Finset.range T, (1 - z / root T (i + 1)) := by
  simp only [residualFactors, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma residualFactors_eval_zero (T : ℕ) : (residualFactors T).eval 0 = 1 := by
  simp [residualFactors_eval]

lemma residualFactors_degree (T : ℕ) : (residualFactors T).natDegree ≤ T := by
  unfold residualFactors
  apply (natDegree_prod_le _ _).trans
  have h : ∀ i ∈ Finset.range T, (1 - C ((root T (i + 1))⁻¹) * X : ℝ[X]).natDegree ≤ 1 := by
    intro i _
    compute_degree
  simpa using Finset.sum_le_sum h

lemma residualFactors_eval_root {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T) :
    (residualFactors T).eval (root T i) = 0 := by
  rw [residualFactors_eval]
  apply Finset.prod_eq_zero (i := i - 1)
  · exact Finset.mem_range.mpr (by omega)
  · rw [show i - 1 + 1 = i by omega, div_self (root_pos hi hiT).ne']
    exact sub_self _

lemma residualNumerator_eval_root {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T) :
    (residualNumerator T).eval (root T i) = 0 := by
  let θ := (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1)
  have hs : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [θ]
      positivity
    · exact (angle_lt_half_pi hiT).trans (by linarith [Real.pi_pos])
  have h := residualNumerator_sin T θ
  have heq : (2 * (T : ℝ) + 1) * θ = (i : ℝ) * Real.pi := by
    dsimp [θ]
    field_simp
  rw [heq, Real.sin_nat_mul_pi] at h
  exact (mul_eq_zero.mp h).resolve_right hs.ne'

lemma residualNumerator_eq_factors (T : ℕ) :
    residualNumerator T = C (2 * (T : ℝ) + 1) * residualFactors T := by
  have hinj : Function.Injective (fun i : Fin (T + 1) => root T i) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (root_strictMono hlt (by omega))) hij
    · exact (ne_of_lt (root_strictMono hgt (by omega))) hij.symm
  apply eq_of_natDegree_lt_card_of_eval_eq _ _ hinj
  · intro i
    by_cases hi : (i : ℕ) = 0
    · simp [hi, root, residualNumerator_eval_zero, residualFactors_eval_zero]
    · have hi' : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi
      have hiT : (i : ℕ) ≤ T := by omega
      simp only [eval_mul, eval_C, residualNumerator_eval_root hi' hiT,
        residualFactors_eval_root hi' hiT, mul_zero]
  · have hleft := residualNumerator_degree T
    have hright : (C (2 * (T : ℝ) + 1) * residualFactors T).natDegree ≤ T := by
      apply natDegree_mul_le.trans
      simpa only [natDegree_C, zero_add] using residualFactors_degree T
    simp only [Fintype.card_fin]
    omega

lemma residualFactors_sin (T : ℕ) (θ : ℝ) :
    (2 * (T : ℝ) + 1) * (residualFactors T).eval (Real.sin θ ^ 2) * Real.sin θ =
      Real.sin ((2 * (T : ℝ) + 1) * θ) := by
  have h := residualNumerator_sin T θ
  rw [residualNumerator_eq_factors, eval_mul, eval_C] at h
  exact h

lemma residualFactors_bounds (T : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    |(residualFactors T).eval z| ≤ 1 ∧
      z * ((residualFactors T).eval z) ^ 2 ≤ 1 / (2 * (T : ℝ) + 1) ^ 2 := by
  by_cases hz0 : z = 0
  · subst z
    simp only [residualFactors_eval_zero, abs_one, le_refl, zero_mul, true_and]
    positivity
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  let θ := Real.arcsin (Real.sqrt z)
  have hroot : 0 < Real.sqrt z := Real.sqrt_pos.mpr hzpos
  have hroot1 : Real.sqrt z ≤ 1 := (Real.sqrt_le_one).mpr hz1
  have hsin : Real.sin θ = Real.sqrt z :=
    Real.sin_arcsin (by linarith) hroot1
  have hidentity := residualFactors_sin T θ
  rw [hsin, Real.sq_sqrt hz] at hidentity
  have hm : 0 < 2 * (T : ℝ) + 1 := by positivity
  have habs := congrArg abs hidentity
  rw [abs_mul, abs_mul, abs_of_pos hm, abs_of_pos hroot] at habs
  have hlinear := abs_sin_nat_mul_le (2 * T + 1) θ
  rw [hsin, abs_of_pos hroot] at hlinear
  push_cast at hlinear
  have hcontract : |(residualFactors T).eval z| ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hm hroot)).mp
    nlinarith [hlinear, habs]
  refine ⟨hcontract, ?_⟩
  have hsin_bound := Real.abs_sin_le_one ((2 * (T : ℝ) + 1) * θ)
  have hsq : (Real.sin ((2 * (T : ℝ) + 1) * θ)) ^ 2 ≤ 1 := by
    have := abs_le.mp hsin_bound
    nlinarith
  have hid2 := congrArg (fun x : ℝ => x ^ 2) hidentity
  simp only [mul_pow, Real.sq_sqrt hz] at hid2
  apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
  nlinarith [hid2, hsq]

end OracleTemplate.BatchedChebyshev
