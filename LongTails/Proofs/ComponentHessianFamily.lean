import LongTails.Proofs.ComponentHessianLocalization
import LongTails.Proofs.RelativeHessianSimulation
import LongTails.Proofs.FiniteSumNondualLowerComponents

namespace LongTails.Proofs.ComponentHessianFamily

open scoped RealInnerProductSpace
open ComponentHessianChain ComponentHessianLocalization RelativeHessianSimulation

variable {d k n : ℕ}

noncomputable def row (π : Fin (k + 1) ↪ Fin d) : Fin (k + 1) → EuclideanSpace ℝ (Fin d) :=
  Fin.cases (-axes π 0) (fun j => axes π j.castSucc - axes π j.succ)

def offset (k : ℕ) : Fin (k + 1) → ℝ := Fin.cases (4 * (k + 1 : ℕ)) (fun _ => 0)

noncomputable def radius (n K : ℝ) : ℝ := 2 ^ 70 * n * K ^ 4

noncomputable def ridge (n K : ℝ) : ℝ := 1 / (64 * n * K ^ 2)

noncomputable def part (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  masked (radius n (k + 1 : ℕ)) s (row π) (offset k) x +
    FullGeneralizedSmoothZeroQuery.quadratic (ridge n (k + 1 : ℕ)) 0 x

lemma row_norm (π : Fin (k + 1) ↪ Fin d) (j : Fin (k + 1)) : ‖row π j‖ ≤ 2 := by
  have h := (axes_orthonormal π).norm_eq_one
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [row, h]
  · change ‖axes π j.castSucc - axes π j.succ‖ ≤ 2
    exact (norm_sub_le _ _).trans (by simp [h]; norm_num)

lemma row_frame (π : Fin (k + 1) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d)) :
    ∑ j, ⟪row π j, v⟫ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
  have h := (FiniteSumNondualLowerComponents.selectedChain π).le_opNorm v
  have h' := h.trans (mul_le_mul_of_nonneg_right
    (FiniteSumNondualLowerComponents.selectedChain_opNorm π) (norm_nonneg v))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hsq
  rw [Fin.sum_univ_succ]
  simp only [row, Fin.cases_zero, Fin.cases_succ, inner_neg_left, inner_sub_left,
    axes_inner, neg_sq]
  norm_num [FiniteSumNondualLowerComponents.selectedChain_apply_zero,
    FiniteSumNondualLowerComponents.selectedChain_apply_succ, mul_pow] at hsq
  exact hsq

lemma offset_abs (k : ℕ) (j : Fin (k + 1)) : |offset k j| ≤ 4 * (k + 1 : ℕ) := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [offset, abs_of_nonneg (by positivity : 0 ≤ 4 * ((k : ℝ) + 1))]
  positivity

lemma radius_bounds {n K : ℝ} (hn : 1 ≤ n) (hK : 1 ≤ K) :
    K ≤ radius n K ∧ 2 ^ 62 * K / radius n K ≤ 1 / n ∧
      2 ^ 37 * K / radius n K ≤ ridge n K := by
  have hk : 0 < K := by linarith
  have hn' : 0 < n := by linarith
  unfold radius ridge
  have h₁ := pow_le_pow_right₀ hK (by decide : 1 ≤ 4)
  have h₂ := pow_le_pow_right₀ hK (by decide : 3 ≤ 4)
  simp only [pow_one] at h₁
  refine ⟨?_, ?_, ?_⟩
  · calc
      K ≤ K ^ 4 := h₁
      _ ≤ 2 ^ 70 * n * K ^ 4 := by nlinarith [mul_le_mul_of_nonneg_right hn (pow_nonneg hk.le 4)]
  · rw [div_le_div_iff₀ (by positivity) hn']
    nlinarith [mul_le_mul_of_nonneg_right h₁ hn'.le, mul_nonneg hn'.le (pow_nonneg hk.le 4)]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h₂ hn'.le, mul_nonneg hn'.le (pow_nonneg hk.le 4)]

lemma part_smooth (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) (n : ℕ) :
    ContDiff ℝ 3 (part π s n) := (masked_smooth _ _ _ _).add (RelativeHessianGuard.quadratic_smooth _)

lemma part_convex (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) (hn : 0 < n) :
    ConvexOn ℝ Set.univ (part π s n) := by
  apply convex_of_curvature (part_smooth π s n)
  intro x u
  let K : ℝ := (k + 1 : ℕ)
  have hK : 1 ≤ K := by dsimp [K]; norm_num
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB := radius_bounds hn' hK
  have hs : (s.card : ℝ) ≤ K := by
    change (s.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
    exact_mod_cast (show s.card ≤ k + 1 by simpa using s.card_le_univ)
  have h := masked_curvature hK hB.1 s hs (row π) (offset k) (row_norm π) (offset_abs k) x u
  have he := ThirdOrderAffineCalculus.combination_hessian
    (masked_smooth (radius n K) s (row π) (offset k)) (RelativeHessianGuard.quadratic_smooth (E := EuclideanSpace ℝ (Fin d)) (ridge n K)) 1 1 x
  have hQ : fderiv ℝ (gradient (FullGeneralizedSmoothZeroQuery.quadratic (ridge n K) 0)) x u =
      ridge n K • u := by
    rw [show gradient (FullGeneralizedSmoothZeroQuery.quadratic (ridge n K) (0 : EuclideanSpace ℝ (Fin d))) =
      fun y => ridge n K • y from funext (RelativeHessianGuard.quadratic_gradient _)]
    exact congrArg (fun A : _ →L[ℝ] _ => A u) (((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (ridge n K)).fderiv)
  simp only [one_mul, one_smul] at he
  unfold part
  rw [he, add_apply, inner_add_left, hQ, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith [mul_le_mul_of_nonneg_right hB.2.2 (sq_nonneg ‖u‖)]

lemma part_hessian_difference (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) (hn : 0 < n)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (gradient (part π s n)) x - fderiv ℝ (gradient (part π s n)) y‖ ≤
      2 ^ 26 * energy s (row π) (x - y) + (1 / n) * ‖x - y‖ := by
  apply segment_bound (part_smooth π s n)
  intro z
  let K : ℝ := (k + 1 : ℕ)
  have hK : 1 ≤ K := by dsimp [K]; norm_num
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB := radius_bounds hn' hK
  have hs : (s.card : ℝ) ≤ K := by
    change (s.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
    exact_mod_cast (show s.card ≤ k + 1 by simpa using s.card_le_univ)
  have he := ThirdOrderAffineCalculus.combination_third
    (masked_smooth (radius n K) s (row π) (offset k)) (RelativeHessianGuard.quadratic_smooth (E := EuclideanSpace ℝ (Fin d)) (ridge n K)) 1 1 z
  simp only [one_mul, one_smul, RelativeHessianGuard.quadratic_third, add_zero] at he
  unfold part
  rw [he]
  exact (direction_bound hK hB.1 s hs (row π) (offset k) (row_norm π) (offset_abs k)
    (row_frame π) z (x - y)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hB.2.1 (norm_nonneg _)))

def owned {J : Type*} [Fintype J] (owner : J → Fin n) (i : Fin n) : Finset J :=
  Finset.univ.filter (fun j => owner j = i)

lemma partition_sum {J : Type*} [Fintype J] (owner : J → Fin n) (f : J → ℝ) :
    ∑ i, ∑ j ∈ owned owner i, f j = ∑ j, f j := by
  simp only [owned, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

lemma family_squared_bound (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (hn : 0 < n) (x y : EuclideanSpace ℝ (Fin d)) :
    ∑ i, ‖fderiv ℝ (gradient (part π (owned owner i) n)) x -
      fderiv ℝ (gradient (part π (owned owner i) n)) y‖ ^ 2 ≤ 2 ^ 56 * ‖x - y‖ ^ 2 := by
  let u := x - y
  let e := fun i => energy (owned owner i) (row π) u
  have he : ∑ i, e i ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
    simpa [e, energy, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), partition_sum]
      using row_frame π u
  have h (i : Fin n) :
      ‖fderiv ℝ (gradient (part π (owned owner i) n)) x -
        fderiv ℝ (gradient (part π (owned owner i) n)) y‖ ^ 2 ≤
      2 ^ 53 * e i ^ 2 + 2 * ((1 / (n : ℝ)) * ‖u‖) ^ 2 := by
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) (part_hessian_difference π (owned owner i) hn x y) 2
    change _ ≤ (2^26 * e i + (1 / n) * ‖u‖)^2 at h₁
    nlinarith only [h₁, sq_nonneg (2^26 * e i - (1 / n) * ‖u‖)]
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at ht
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℝ) * (2 * ((1 / n) * ‖u‖) ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) * (n - 1) by positivity) (sq_nonneg ‖u‖)]
  change _ ≤ 2^56 * ‖u‖^2
  refine ht.trans ((add_le_add (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2^53)) hc).trans ?_)
  nlinarith [sq_nonneg ‖u‖]

lemma part_nonneg (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ part π s n x := by
  unfold part masked FullGeneralizedSmoothZeroQuery.quadratic ridge
  exact add_nonneg (mul_nonneg (RelativeHessianCutoff.bounds _).1 (raw_nonneg _ _ _ _)) (by positivity)

end LongTails.Proofs.ComponentHessianFamily
