import LongTails.Proofs.QuadraticContractions
import LongTails.Proofs.MarkovProductEnergy

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MarkovQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma weighted_quadratic_source (H : ℕ → E →L[ℝ] E) (x : ℕ → E)
    (w : ℕ → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k y, 0 ≤ ⟪y, H k y⟫)
    (hb : ∀ k y, ⟪y, H k y⟫ ≤ L * ‖y‖ ^ 2)
    (hx : ∀ k, x (k + 1) = x k - η • H k (x k))
    (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    η * (∑ k ∈ Finset.range n, w k * ⟪x 0, H k (x 0)⟫) ≤
      2 * (∑ k ∈ Finset.range n, w k * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2)) +
      2 * η * L * (∑ k ∈ Finset.range n, w k * ‖x k - x 0‖ ^ 2) := by
  have hpoint : ∀ k, η * ⟪x 0, H k (x 0)⟫ ≤
      2 * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2) + 2 * η * L * ‖x k - x 0‖ ^ 2 := by
    intro k
    have hc := mul_le_mul_of_nonneg_left
      (quadratic_comparison (H k) (hs k) (hp k) (hb k) (x 0) (x k)) hη
    rw [norm_sub_rev (x 0) (x k)] at hc
    have he := quadratic_step_objective (H k) hL (hs k) (hp k) (hb k) hη hηL (x k)
    rw [← hx k] at he
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun k _ => mul_le_mul_of_nonneg_left (hpoint k) (hw k))
  convert hsum using 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring

lemma weighted_quadratic_increment (H : ℕ → E →L[ℝ] E) (x : ℕ → E)
    (w : ℕ → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k y, 0 ≤ ⟪y, H k y⟫)
    (hb : ∀ k y, ⟪y, H k y⟫ ≤ L * ‖y‖ ^ 2)
    (hx : ∀ k, x (k + 1) = x k - η • H k (x k))
    (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    (∑ k ∈ Finset.range n, w k * ‖x (k + 1) - x k‖ ^ 2) ≤
      η * L * ∑ k ∈ Finset.range n, w k * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have he := quadratic_step_small_increment (H k) hL (hs k) (hp k) (hb k) hη hηL (x k)
  have hn : ‖x (k + 1) - x k‖ = ‖η • H k (x k)‖ := by
    rw [hx k, sub_sub_cancel_left, norm_neg]
  rw [← hx k, ← hn] at he
  have hm := mul_le_mul_of_nonneg_left he (hw k)
  nlinarith

lemma geometric_quadratic_source (H : ℕ → E →L[ℝ] E) (x : ℕ → E)
    {L η r : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k y, 0 ≤ ⟪y, H k y⟫)
    (hb : ∀ k y, ⟪y, H k y⟫ ≤ L * ‖y‖ ^ 2)
    (hx : ∀ k, x (k + 1) = x k - η • H k (x k)) (n : ℕ) :
    (1 - r ^ 2) ^ 2 * (η * ∑ k ∈ Finset.range n, r ^ (2 * k) * ⟪x 0, H k (x 0)⟫) ≤
      (2 * (1 - r ^ 2) ^ 2 + 8 * (η * L) ^ 2) *
      ∑ k ∈ Finset.range n, r ^ (2 * k) * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2) := by
  let D := ∑ k ∈ Finset.range n, r ^ (2 * k) * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2)
  let S := ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x k - x 0‖ ^ 2
  have hw : ∀ k : ℕ, 0 ≤ r ^ (2 * k) := fun k => pow_nonneg hr _
  have hsource := weighted_quadratic_source H x (fun k => r ^ (2 * k)) hL hη hηL hs hp hb hx hw n
  have hinc := weighted_quadratic_increment H x (fun k => r ^ (2 * k)) hL hη hηL hs hp hb hx hw n
  have hdisp := MarkovProduct.geometric_displacement_rescaled r hr hr1 x n
  have hd : (1 - r ^ 2) ^ 2 * S ≤ 4 * (η * L * D) :=
    hdisp.trans (mul_le_mul_of_nonneg_left hinc (by norm_num))
  have hβ : 0 ≤ 2 * η * L := by positivity
  calc
    _ ≤ (1 - r ^ 2) ^ 2 * (2 * D + 2 * η * L * S) :=
      mul_le_mul_of_nonneg_left hsource (sq_nonneg _)
    _ = 2 * (1 - r ^ 2) ^ 2 * D + 2 * η * L * ((1 - r ^ 2) ^ 2 * S) := by ring
    _ ≤ 2 * (1 - r ^ 2) ^ 2 * D + 2 * η * L * (4 * (η * L * D)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hβ)
    _ = _ := by dsimp [D]; ring

end OracleTemplate.MarkovQuadratic
