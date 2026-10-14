import LongTails.Proofs.QuadraticContractions
import LongTails.Proofs.ReshufflingWordEnergy
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_operator_pow_apply (H : E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hH : ‖H‖ ≤ L) (k : ℕ) (x : E) : ‖(H ^ k) x‖ ≤ L ^ k * ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact ((H.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))).trans
        ((mul_le_mul_of_nonneg_left ih hL).trans_eq (by rw [pow_succ']; ring))

lemma positive_power_energy (H : E →L[ℝ] E) {L : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫) (hH : ‖H‖ ≤ L)
    (k : ℕ) (x : E) :
    |⟪x, (H ^ (k + 2)) x⟫| ≤ L ^ (k + 1) * ⟪x, H x⟫ := by
  have hb : ∀ y, ⟪y, H y⟫ ≤ L * ‖y‖ ^ 2 := by
    intro y
    calc
      _ ≤ ‖y‖ * ‖H y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (L * ‖y‖) := mul_le_mul_of_nonneg_left
        ((H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
  have hc := OracleTemplate.MarkovQuadratic.quadratic_cocoercivity H hL hs hp hb x
  have he : ⟪x, (H ^ (k + 2)) x⟫ = ⟪H x, (H ^ k) (H x)⟫ := by
    rw [show H ^ (k + 2) = H * (H ^ k * H) by
      rw [← pow_succ, ← pow_succ']]
    simp only [mul_apply_eq_comp]
    simpa only [hs] using H.adjoint_inner_right x ((H ^ k) (H x))
  rw [he]
  calc
    _ ≤ ‖H x‖ * ‖(H ^ k) (H x)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖H x‖ * (L ^ k * ‖H x‖) :=
      mul_le_mul_of_nonneg_left (norm_operator_pow_apply H hL.le hH k (H x)) (norm_nonneg _)
    _ = L ^ k * ‖H x‖ ^ 2 := by ring
    _ ≤ L ^ k * (L * ⟪x, H x⟫) := mul_le_mul_of_nonneg_left hc (pow_nonneg hL.le _)
    _ = _ := by rw [pow_succ]; ring

lemma geometric_partial_le_two {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1 / 2) (k : ℕ) :
    (∑ j ∈ Finset.range k, r ^ j) ≤ 2 := by
  apply le_trans _ (sum_geometric_two_le k)
  exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ hr hr2 j)

lemma single_component_contract (H : E →L[ℝ] E) {L μ η : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hstep : η * L ≤ 1)
    (hs : H.adjoint = H) (hH : ‖H‖ ≤ L)
    (hμH : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪x, H x⟫) (x : E) :
    ‖x - η • H x‖ ^ 2 ≤ (1 - η * μ) * ‖x‖ ^ 2 := by
  have hp : ∀ y, 0 ≤ ⟪y, H y⟫ := fun y =>
    (mul_nonneg hμ (sq_nonneg ‖y‖)).trans (hμH y)
  have hb : ∀ y, ⟪y, H y⟫ ≤ L * ‖y‖ ^ 2 := by
    intro y
    calc
      _ ≤ ‖y‖ * ‖H y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (L * ‖y‖) := mul_le_mul_of_nonneg_left
        ((H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
  have he := OracleTemplate.MarkovQuadratic.quadratic_step_objective H hL hs hp hb hη hstep x
  have hm := mul_le_mul_of_nonneg_left (hμH x) hη
  nlinarith

lemma positive_power_tail (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hη : 0 ≤ η) (hstep : 2 * η * L ≤ 1 / 2)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫) (hH : ‖H‖ ≤ L)
    (K : ℕ) (x : E) :
    (∑ j ∈ Finset.range K, (-2 * η) ^ (j + 2) / ((j + 2).factorial : ℝ) *
      ⟪x, (H ^ (j + 2)) x⟫) ≤ 8 * η ^ 2 * L * ⟪x, H x⟫ := by
  have hx := hp x
  have ht : ∀ j, (-2 * η) ^ (j + 2) / ((j + 2).factorial : ℝ) *
      ⟪x, (H ^ (j + 2)) x⟫ ≤ 4 * η ^ 2 * L * ⟪x, H x⟫ * (2 * η * L) ^ j := by
    intro j
    have hf : (1 : ℝ) ≤ (j + 2).factorial := by exact_mod_cast Nat.factorial_pos (j + 2)
    have ha : |(-2 * η) ^ (j + 2) / ((j + 2).factorial : ℝ) *
        ⟪x, (H ^ (j + 2)) x⟫| =
        (2 * η) ^ (j + 2) / ((j + 2).factorial : ℝ) * |⟪x, (H ^ (j + 2)) x⟫| := by
      rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ (j + 2).factorial by positivity)]
      congr 3
      rw [abs_of_nonpos (by linarith : -2 * η ≤ 0)]
      ring
    calc
      _ ≤ |(-2 * η) ^ (j + 2) / ((j + 2).factorial : ℝ) *
          ⟪x, (H ^ (j + 2)) x⟫| := le_abs_self _
      _ = _ := ha
      _ ≤ (2 * η) ^ (j + 2) * |⟪x, (H ^ (j + 2)) x⟫| := by
        exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hf) (abs_nonneg _)
      _ ≤ (2 * η) ^ (j + 2) * (L ^ (j + 1) * ⟪x, H x⟫) :=
        mul_le_mul_of_nonneg_left (positive_power_energy H hL hs hp hH j x) (by positivity)
      _ = _ := by simp only [pow_add, pow_one, mul_pow]; ring
  calc
    _ ≤ ∑ j ∈ Finset.range K, 4 * η ^ 2 * L * ⟪x, H x⟫ * (2 * η * L) ^ j :=
      Finset.sum_le_sum (fun j _ => ht j)
    _ = (4 * η ^ 2 * L * ⟪x, H x⟫) * ∑ j ∈ Finset.range K, (2 * η * L) ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * η ^ 2 * L * ⟪x, H x⟫) * 2 :=
      mul_le_mul_of_nonneg_left (geometric_partial_le_two (by positivity) hstep K)
        (by positivity)
    _ = _ := by ring

lemma collision_tail_bound {η N C Q : ℝ} (hη : 0 ≤ η) (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hstep : 2 * η * N ≤ 1 / 2) (K : ℕ) :
    (∑ j ∈ Finset.range K, η ^ (j + 3) * (8 * C * (2 * N) ^ (j + 1) * Q)) ≤
      32 * C * η ^ 3 * N * Q := by
  have he : ∀ j, η ^ (j + 3) * (8 * C * (2 * N) ^ (j + 1) * Q) =
      (16 * C * η ^ 3 * N * Q) * (2 * η * N) ^ j := by
    intro j
    simp only [pow_add, pow_one, mul_pow]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (16 * C * η ^ 3 * N * Q) * 2 :=
      mul_le_mul_of_nonneg_left (geometric_partial_le_two (by positivity) hstep K) (by positivity)
    _ = _ := by ring

end OracleTemplate.Reshuffling
