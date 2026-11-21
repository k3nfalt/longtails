import LongTails.Proofs.ComponentHessianLink
import LongTails.Proofs.RidgeJets
import LongTails.Proofs.ThirdOrderAffineCalculus
import LongTails.Proofs.SparseTensorBounds

namespace LongTails.Proofs.ComponentHessianChain

open scoped RealInnerProductSpace
open ComponentHessianLink RelativeHessianGate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def edge (a : E) (b : ℝ) := RidgeJets.value (fun t => link (b + t)) a

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma edge_smooth (a : E) (b : ℝ) : ContDiff ℝ 3 (edge a b) :=
  RidgeJets.smooth (link_smooth.comp (contDiff_const.add contDiff_id)) _

private lemma shifted {φ ψ : ℝ → ℝ} (h : ∀ t, HasDerivAt φ (ψ t) t) (b t : ℝ) :
    HasDerivAt (fun r => φ (b + r)) (ψ (b + t)) t := by
  simpa [Function.comp_def] using (h (b + t)).comp t ((hasDerivAt_id t).const_add b)

omit [FiniteDimensional ℝ E] in
lemma edge_gradient (a x : E) (b : ℝ) : gradient (edge a b) x = gate (b + ⟪a, x⟫) • a :=
  RidgeJets.gradient_eq (shifted link_hasDerivAt b) a x

omit [FiniteDimensional ℝ E] in
lemma edge_hessian (a x v : E) (b : ℝ) :
    fderiv ℝ (gradient (edge a b)) x v = (gateSlope (b + ⟪a, x⟫) * ⟪a, v⟫) • a :=
  RidgeJets.hessian_apply (link_smooth.comp (contDiff_const.add contDiff_id))
    (shifted link_hasDerivAt b) (shifted gate_hasDerivAt b) a x v

lemma edge_third (a x u v : E) (b : ℝ) :
    fderiv ℝ (fderiv ℝ (gradient (edge a b))) x u v =
      (gateCurvature (b + ⟪a, x⟫) * ⟪a, u⟫ * ⟪a, v⟫) • a :=
  RidgeJets.third_apply (link_smooth.comp (contDiff_const.add contDiff_id))
    (shifted link_hasDerivAt b) (shifted gate_hasDerivAt b) (shifted gateSlope_hasDerivAt b) a x u v

variable {J : Type*} [Fintype J]

noncomputable def raw (s : Finset J) (a : J → E) (b : J → ℝ) (x : E) :=
  ∑ j ∈ s, edge (a j) (b j) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype J] in
lemma raw_smooth (s : Finset J) (a : J → E) (b : J → ℝ) : ContDiff ℝ 3 (raw s a b) :=
  ContDiff.sum (fun j _ => edge_smooth (a j) (b j))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype J] in
lemma raw_nonneg (s : Finset J) (a : J → E) (b : J → ℝ) (x : E) : 0 ≤ raw s a b x :=
  Finset.sum_nonneg (fun _ _ => link_nonneg _)

omit [Fintype J] in
lemma raw_hessian_nonneg (s : Finset J) (a : J → E) (b : J → ℝ) (x v : E) :
    0 ≤ ⟪fderiv ℝ (gradient (raw s a b)) x v, v⟫ := by
  unfold raw
  rw [ThirdOrderAffineCalculus.sum_hessian s (fun j _ => edge_smooth (a j) (b j))]
  simp only [sum_apply, sum_inner, edge_hessian, real_inner_smul_left]
  apply Finset.sum_nonneg
  intro j _
  nlinarith [mul_nonneg (gateSlope_nonneg (b j + ⟪a j, x⟫)) (sq_nonneg ⟪a j, v⟫)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma frame_sum (s : Finset J) (a : J → E)
    (ha : ∀ u, ∑ j, ⟪a j, u⟫ ^ 2 ≤ 4 * ‖u‖ ^ 2) (c : J → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ j ∈ s, |c j| ≤ M) (v : E) :
    ‖∑ j ∈ s, (c j * ⟪a j, v⟫) • a j‖ ≤ 4 * M * ‖v‖ := by
  let z := ∑ j ∈ s, (c j * ⟪a j, v⟫) • a j
  have hsum := SparseTensorBounds.sum_product_bound (fun j => |⟪a j, v⟫|)
    (fun j => |⟪a j, z⟫|) (norm_nonneg v) (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 4)
    (by simpa only [sq_abs] using ha v) (by simpa only [sq_abs] using ha z)
  have h : ‖z‖ ^ 2 ≤ M * (4 * ‖v‖ * ‖z‖) := calc
    ‖z‖ ^ 2 = ⟪z, z⟫ := (real_inner_self_eq_norm_sq _).symm
    _ = ∑ j ∈ s, c j * ⟪a j, v⟫ * ⟪a j, z⟫ := by
      change ⟪∑ j ∈ s, (c j * ⟪a j, v⟫) • a j, z⟫ = _
      simp [sum_inner, real_inner_smul_left]
    _ ≤ ∑ j ∈ s, M * (|⟪a j, v⟫| * |⟪a j, z⟫|) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (le_abs_self _).trans
      rw [abs_mul, abs_mul, mul_assoc]
      gcongr
      exact hc j hj
    _ ≤ ∑ j, M * (|⟪a j, v⟫| * |⟪a j, z⟫|) := Finset.sum_le_univ_sum_of_nonneg (fun j => by positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; gcongr
  change ‖z‖ ≤ _
  by_contra! hn
  nlinarith [mul_pos (sub_pos.mpr hn) (show 0 < ‖z‖ from lt_of_le_of_lt (by positivity) hn)]

noncomputable def energy (s : Finset J) (a : J → E) (u : E) : ℝ :=
  Real.sqrt (∑ j ∈ s, ⟪a j, u⟫ ^ 2)

lemma raw_third_bound (s : Finset J) (a : J → E) (b : J → ℝ)
    (ha : ∀ u, ∑ j, ⟪a j, u⟫ ^ 2 ≤ 4 * ‖u‖ ^ 2) (x u : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (raw s a b))) x u‖ ≤ 2 ^ 26 * energy s a u := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro v
  unfold raw
  rw [ThirdOrderAffineCalculus.sum_third s (fun j _ => edge_smooth (a j) (b j))]
  simp only [sum_apply, edge_third]
  have h := frame_sum s a ha (fun j => gateCurvature (b j + ⟪a j, x⟫) * ⟪a j, u⟫)
    (2 ^ 24 * energy s a u) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by
      intro j hj
      rw [abs_mul]
      apply mul_le_mul (gate_jet_bounds _).2.1 _ (abs_nonneg _) (by norm_num)
      apply Real.le_sqrt_of_sq_le
      rw [sq_abs]
      exact Finset.single_le_sum (fun i _ => sq_nonneg ⟪a i, u⟫) hj) v
  convert h using 1
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype J] in
lemma raw_value_bound (s : Finset J) (a : J → E) (b : J → ℝ) {A : ℝ}
    (ha : ∀ j, ‖a j‖ ≤ 2) (hb : ∀ j, |b j| ≤ A) (x : E) :
    |raw s a b x| ≤ s.card * (A + 2 * ‖x‖) := by
  rw [abs_of_nonneg (raw_nonneg s a b x)]
  calc
    _ ≤ ∑ j ∈ s, (A + 2 * ‖x‖) := by
      apply Finset.sum_le_sum
      intro j _
      exact (link_le _).trans ((abs_add_le _ _).trans (add_le_add (hb j)
        ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg x)))))
    _ = _ := by simp [mul_add]

omit [Fintype J] in
lemma raw_gradient_bound (s : Finset J) (a : J → E) (b : J → ℝ)
    (ha : ∀ j, ‖a j‖ ≤ 2) (x : E) : ‖gradient (raw s a b) x‖ ≤ 2 * s.card := by
  unfold raw
  rw [ThirdOrderAffineCalculus.sum_gradient s (fun j _ => edge_smooth (a j) (b j))]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ s, (1 : ℝ) * 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [edge_gradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (gate_bounds _).1]
      exact mul_le_mul (gate_bounds _).2 (ha j) (norm_nonneg _) zero_le_one
    _ = _ := by simp [mul_comm]

lemma raw_hessian_bound (s : Finset J) (a : J → E) (b : J → ℝ)
    (ha : ∀ u, ∑ j, ⟪a j, u⟫ ^ 2 ≤ 4 * ‖u‖ ^ 2) (x : E) :
    ‖fderiv ℝ (gradient (raw s a b)) x‖ ≤ 2 ^ 26 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  unfold raw
  rw [ThirdOrderAffineCalculus.sum_hessian s (fun j _ => edge_smooth (a j) (b j))]
  simp only [sum_apply, edge_hessian]
  have h := frame_sum s a ha (fun j => gateSlope (b j + ⟪a j, x⟫))
    (2 ^ 24) (by norm_num) (fun j _ => (gate_jet_bounds _).1) v
  norm_num at h ⊢
  exact h

end LongTails.Proofs.ComponentHessianChain
