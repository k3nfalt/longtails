import LongTails.Proofs.ChebyshevNoise
import LongTails.Proofs.QuadraticSpectralBounds

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BatchedChebyshev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
lemma propagator_suffix_coordinates (H : E →L[ℝ] E) (L : ℝ) (T i : ℕ)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hH : ∀ x j, b.repr (H x) j = μ j * b.repr x j)
    (hi : i ≤ T) (x : E) (j : ι) :
    b.repr (propagator H (fun k => 1 / (L * root T k)) (T - i) (i + 1) x) j =
      suffix T i (μ j / L) * b.repr x j := by
  rw [propagator_coordinates H _ b μ hH]
  congr 1
  rw [show i + 1 + (T - i) = T + 1 by omega]
  unfold suffix
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_add_right]
  apply Finset.prod_congr rfl
  intro k hk
  rw [show i + 1 + k = i + k + 1 by omega]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [CompleteSpace E] in
lemma propagator_full_coordinates (H : E →L[ℝ] E) (L : ℝ) (T : ℕ)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hH : ∀ x j, b.repr (H x) j = μ j * b.repr x j) (x : E) (j : ι) :
    b.repr (propagator H (fun k => 1 / (L * root T k)) T 1 x) j =
      (residualFactors T).eval (μ j / L) * b.repr x j := by
  have h := propagator_suffix_coordinates H L T 0 b μ hH (Nat.zero_le _) x j
  simpa only [Nat.sub_zero, Nat.zero_add, suffix, Nat.Ico_zero_eq_range,
    residualFactors_eval] using h

lemma full_energy_bound (A : E →L[ℝ] E) {L : ℝ} (hL : 0 < L) (T : ℕ)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hH : ∀ x j, b.repr (A.adjoint (A x)) j = μ j * b.repr x j)
    (hμ : ∀ j, 0 ≤ μ j ∧ μ j ≤ L) (x : E) :
    ‖A (propagator (A.adjoint.comp A) (fun k => 1 / (L * root T k)) T 1 x)‖ ^ 2 ≤
      L / (2 * (T : ℝ) + 1) ^ 2 * ‖x‖ ^ 2 := by
  apply spectral_factor_bound A _ b μ (fun j => (residualFactors T).eval (μ j / L)) hH
    (propagator_full_coordinates _ L T b μ hH)
  intro j
  have hz : 0 ≤ μ j / L := div_nonneg (hμ j).1 hL.le
  have hz1 : μ j / L ≤ 1 := (div_le_one hL).mpr (hμ j).2
  have h := mul_le_mul_of_nonneg_left (residualFactors_bounds T hz hz1).2 hL.le
  convert h using 1 <;> field_simp

lemma noise_energy_bound (A : E →L[ℝ] E) {L : ℝ} (hL : 0 < L) {T i : ℕ}
    (hi : 0 < i) (hiT : i ≤ T)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hH : ∀ x j, b.repr (A.adjoint (A x)) j = μ j * b.repr x j)
    (hμ : ∀ j, 0 ≤ μ j ∧ μ j ≤ L) (x : E) :
    ‖(-(1 / (L * root T i))) • A (propagator (A.adjoint.comp A)
      (fun k => 1 / (L * root T k)) (T - i) (i + 1) x)‖ ^ 2 ≤
        (weight T i ^ 2 / L) * ‖x‖ ^ 2 := by
  let B := (-(1 / (L * root T i))) • propagator (A.adjoint.comp A)
    (fun k => 1 / (L * root T k)) (T - i) (i + 1)
  have hB (y : E) (j : ι) : b.repr (B y) j =
      (-(1 / (L * root T i)) * suffix T i (μ j / L)) * b.repr y j := by
    simp only [B, smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul,
      propagator_suffix_coordinates (A.adjoint.comp A) L T i b μ hH hiT]
    ring
  have hb := spectral_factor_bound A B b μ
    (fun j => -(1 / (L * root T i)) * suffix T i (μ j / L)) hH hB
    (C := weight T i ^ 2 / L) (fun j => by
      have hz : 0 ≤ μ j / L := div_nonneg (hμ j).1 hL.le
      have hz1 : μ j / L ≤ 1 := (div_le_one hL).mpr (hμ j).2
      have h := div_le_div_of_nonneg_right (suffix_gain_bound hi hiT hz hz1) hL.le
      convert h using 1; field_simp) x
  simpa only [B, smul_apply, map_smul] using hb

end OracleTemplate.BatchedChebyshev
