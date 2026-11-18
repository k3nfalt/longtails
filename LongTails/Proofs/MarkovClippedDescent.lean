import LongTails.Proofs.MarkovClippedExecution
import LongTails.Proofs.MarkovClippedDrift

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MarkovClippedDescent

open LongTails.Algorithms.MarkovClippedSgd MarkovClippedDrift

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma descent {f : E → ℝ} {L η : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hη : 0 ≤ η)
    (C : ℝ) (x v : E) :
    f (x - η • clip C v) ≤ f x + η * drift (L * η) C (gradient f x) v := by
  have h := Gradient.smooth_upper_bound hg hl x (x - η • clip C v)
  rw [show x - η • clip C v - x = -(η • clip C v) by abel,
    inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_of_nonneg hη,
    real_inner_comm (clip C v)] at h
  unfold drift
  exact h.trans_eq (by ring)

lemma sum_descent {f : E → ℝ} {L η : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hη : 0 ≤ η)
    (C ε : ℝ) (g : E → Z → E) (m : ℕ) (x0 : E) (z : ℕ → Z) (n : ℕ) :
    let X := point g η C m x0 z
    let U := fun k => gradient f (X k)
    let D := fun k => drift (L * η) C (U k) (g (X k) (z (k * m)))
    f (X n) + η * (ε / 4) * ∑ k ∈ Finset.range n, ‖U k‖ ≤
      f x0 + η * (∑ k ∈ Finset.range n, (D k + ε / 4 * ‖U k‖ - ε ^ 2 / 8)) +
      η * n * ε ^ 2 / 8 := by
  dsimp only
  induction n with
  | zero => simp [point]
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_succ]
    have h := descent hg hl hη C (point g η C m x0 z n) (g (point g η C m x0 z n) (z (n*m)))
    rw [← point.eq_2] at h
    linarith only [ih, h]

end LongTails.Proofs.MarkovClippedDescent
