import LongTails.Proofs.LogisticCloudCoordinates
import LongTails.Proofs.LogisticCloudDispersion
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.BigOperators.Expect

open scoped BigOperators RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudDispersion

namespace LongTails.Proofs.LogisticCloudAverages

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mean_norm_le (f : ι → E) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) :
    ‖(Fintype.card ι : ℝ)⁻¹ • ∑ i, f i‖ ≤ M := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have ht : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs := (norm_sum_le (s := Finset.univ) (f := f)).trans
    (Finset.sum_le_sum (g := fun _ => M) (fun i _ => h i))
  rw [← div_eq_inv_mul, div_le_iff₀ ht]
  simpa [mul_comm] using hs

omit [Nonempty ι] in
lemma weighted_inner_bound (w : E) (z : ι → E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    |𝔼 i, b i * ⟪z i,w⟫| ≤ (𝔼 i, b i)*‖w‖ := by
  refine (Finset.abs_expect_le ..).trans ?_
  rw [Finset.expect_mul]
  apply Finset.expect_le_expect
  intro i _
  rw [abs_mul,abs_of_nonneg (hb i)]
  apply mul_le_mul_of_nonneg_left _ (hb i)
  exact (abs_real_inner_le_norm _ _).trans (by simpa using
    (mul_le_mul_of_nonneg_right (hz i) (norm_nonneg w)))

lemma effective_deficit (c D : ℝ) (f : ι → ℝ) (hD : 0 ≤ D)
    (hf : ∀ i, D/2 ≤ f i ∧ f i ≤ 2*D) :
    ∃ d ∈ Set.Icc (D/2) (2*D), Real.sigmoid (c-d) = 𝔼 i, Real.sigmoid (c-f i) := by
  apply intermediate_value_Icc' (by linarith : D/2 ≤ 2*D)
    (f := fun d => Real.sigmoid (c-d)) (by fun_prop)
  constructor
  · apply Finset.le_expect Finset.univ_nonempty
    intro i _
    exact Real.sigmoid_monotone (by linarith [(hf i).2])
  · apply Finset.expect_le Finset.univ_nonempty
    intro i _
    exact Real.sigmoid_monotone (by linarith [(hf i).1])

lemma mean_transverse (w : E) (z : ι → E) (c : ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hz : ∑ i, z i = 0) (hs : ∀ i, η*‖z i‖^2 ≤ 8) :
    ‖w - η • ((Fintype.card ι : ℝ)⁻¹ • ∑ i, Real.sigmoid (c+⟪z i,w⟫) • z i)‖ ≤ ‖w‖ := by
  let n : ℝ := Fintype.card ι
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : n⁻¹ • (∑ i, (w - (η*(Real.sigmoid (c+⟪z i,w⟫)-Real.sigmoid c)) • z i)) =
      w - η • (n⁻¹ • ∑ i, Real.sigmoid (c+⟪z i,w⟫) • z i) := by
    simp_rw [mul_smul,sub_smul,Finset.sum_sub_distrib,← Finset.smul_sum,
      Finset.sum_sub_distrib,← Finset.smul_sum,hz,smul_zero,sub_zero]
    rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul]
    change (n⁻¹*n) • w - _ = _
    rw [inv_mul_cancel₀ hn,one_smul,smul_comm (n⁻¹) η]
  rw [← he]
  exact mean_norm_le _ _ (fun i => transverse_step w (z i) c hη (hs i))

end LongTails.Proofs.LogisticCloudAverages
