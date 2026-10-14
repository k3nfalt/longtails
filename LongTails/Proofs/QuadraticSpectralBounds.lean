import LongTails.Proofs.QuadraticTemporalEnergy
import Mathlib.Analysis.InnerProductSpace.Spectrum

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BatchedChebyshev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

lemma factor_energy_coordinates (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (μ : ι → ℝ)
    (hdiag : ∀ x i, b.repr (A.adjoint (A x)) i = μ i * b.repr x i) (x : E) :
    ‖A x‖ ^ 2 = ∑ i, μ i * (b.repr x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left,
    ← b.sum_inner_mul_inner (A.adjoint (A x)) x]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (b i) (A.adjoint (A x)),
    ← b.repr_apply_apply, ← b.repr_apply_apply, hdiag]
  ring

lemma spectral_factor_bound (A B : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (μ p : ι → ℝ) {C : ℝ}
    (hdiag : ∀ x i, b.repr (A.adjoint (A x)) i = μ i * b.repr x i)
    (hB : ∀ x i, b.repr (B x) i = p i * b.repr x i)
    (hp : ∀ i, μ i * (p i) ^ 2 ≤ C) (x : E) :
    ‖A (B x)‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  rw [factor_energy_coordinates A b μ hdiag]
  have hx : ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right x
  rw [← hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hB, mul_pow]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hp i) (sq_nonneg (b.repr x i))

lemma factor_eigenvalue_bounds (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (μ : ι → ℝ) {L : ℝ}
    (heigen : ∀ i, A.adjoint (A (b i)) = μ i • b i)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) (i : ι) :
    0 ≤ μ i ∧ μ i ≤ L := by
  have he : ‖A (b i)‖ ^ 2 = μ i := by
    rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left,
      heigen, real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  constructor
  · rw [← he]
    positivity
  · have h := hupper (b i)
    simpa only [he, b.norm_eq_one, one_pow, mul_one] using h

lemma factor_symmetric (A : E →L[ℝ] E) : (A.adjoint.comp A).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪A.adjoint (A x), y⟫ = ⟪x, A.adjoint (A y)⟫
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

noncomputable def propagator (H : E →L[ℝ] E) (η : ℕ → ℝ) : ℕ → ℕ → E →L[ℝ] E
  | 0, _ => ContinuousLinearMap.id ℝ E
  | n + 1, i => (propagator H η n (i + 1)).comp
      (ContinuousLinearMap.id ℝ E - η i • H)

omit [CompleteSpace E] in
lemma propagator_coordinates (H : E →L[ℝ] E) (η : ℕ → ℝ)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hH : ∀ x j, b.repr (H x) j = μ j * b.repr x j)
    (n i : ℕ) (x : E) (j : ι) :
    b.repr (propagator H η n i x) j =
      (∏ k ∈ Finset.Ico i (i + n), (1 - η k * μ j)) * b.repr x j := by
  induction n generalizing i x with
  | zero => simp [propagator]
  | succ n ih =>
    change b.repr (propagator H η n (i + 1) (x - η i • H x)) j = _
    rw [ih]
    have hr : b.repr (x - η i • H x) j = (1 - η i * μ j) * b.repr x j := by
      simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hH]
      ring
    rw [hr, Finset.prod_eq_prod_Ico_succ_bot (show i < i + (n + 1) by omega)]
    rw [show i + (n + 1) = (i + 1) + n by omega]
    ring

omit [CompleteSpace E] in
lemma propagator_zero (H : E →L[ℝ] E) (η : ℕ → ℝ) (n i : ℕ) :
    propagator H η n i 0 = 0 := map_zero _

end OracleTemplate.BatchedChebyshev
