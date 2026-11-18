import LongTails.Algorithms.MarkovClippedSgd
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.AbcSgdUpper

open OracleTemplate MeasureTheory

namespace LongTails.Proofs.MarkovClippedExecution

open LongTails.Algorithms.MarkovClippedSgd LongTails.Algorithms.AbcSgd
open HeavyTailedMarkovGradient StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma point_radius (g : E → Z → E) {η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (m : ℕ) (x0 : E) (z : ℕ → Z) (k : ℕ) :
    ‖point g η C m x0 z k - x0‖ ≤ k * η * C := by
  induction k with
  | zero => simp [point]
  | succ k ih =>
    set x := point g η C m x0 z k
    let y := clip C (g x (z (k * m)))
    change ‖x - η • y - x0‖ ≤ _
    rw [show x - η • y - x0 = (x - x0) - η • y by abel]
    have h := norm_sub_le (x - x0) (η • y)
    rw [norm_smul, Real.norm_of_nonneg hη] at h
    have hc := mul_le_mul_of_nonneg_left (norm_clip_le hC (g x (z (k * m)))) hη
    change η * ‖y‖ ≤ _ at hc
    push_cast
    linarith

lemma point_measurable [MeasurableSpace Z] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {g : E → Z → E} (hg : Measurable (Function.uncurry g))
    (η C : ℝ) (m : ℕ) (x0 : E) (k : ℕ) : Measurable (fun z => point g η C m x0 z k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact ih.sub (((measurable_clip C).comp (hg.comp (ih.prodMk
      (measurable_pi_apply _)))).const_smul _)

lemma point_congr (g : E → Z → E) (η C : ℝ) (m : ℕ) (x0 : E) (z w : ℕ → Z) (k : ℕ)
    (h : ∀ j < k, z (j * m) = w (j * m)) : point g η C m x0 z k = point g η C m x0 w k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [point, ih (fun j hj => h j (by omega)), h k (by omega)]

lemma execute_spaced [MeasurableSpace Z] (P : ProbabilityMeasure (ℕ → Z))
    (g : E → Z → E) (η C : ℝ) (K m : ℕ) (hm : 0 < m)
    (x0 : E) (z : ℕ → Z) (i : Fin (K + 1)) :
    execute { Seed := fun _ => Z, law := P, answer := fun _ (_, x) y => g x y }
      (spaced m (clipped η C K x0)) (fun _ => (K + 1) * m) i z = output g η C m x0 i z := by
  let A := clipped η C K x0
  let X := point g η C m x0 z
  let state := fun k => (i, k, X k, if i.val < k then X i.val else x0)
  have step (k : ℕ) : A.update (state k) (g (A.query (state k)).2 (z (k * m))) = state (k + 1) := by
    simp only [state, A, clipped, sampledSgd, X, point, Prod.mk.injEq, true_and]
    by_cases he : k = i.val
    · subst k; simp
    · by_cases hi : i.val < k
      · simp [he, hi, show i.val < k + 1 by omega]
      · simp [he, hi, show ¬ i.val < k + 1 by omega]
  have hrun (k : ℕ) :
      advance (fun call s => (spaced m A).update s (g ((spaced m A).query s).2 (z call)))
        (k * m) 0 ((spaced m A).initial i) = (k * m, state k) := by
    induction k with
    | zero => rw [Nat.zero_mul]; rfl
    | succ k ih =>
      rw [Nat.succ_mul, advance_add, ih, Nat.zero_add]
      exact (advance_spaced_block A g z hm k (state k)).trans (by rw [Nat.succ_mul, step]; rfl)
  erw [execute_advance]
  change A.output (advance _ ((K + 1) * m) 0 ((spaced m A).initial i)).2 = _
  rw [hrun]
  exact ite_eq_left i.isLt

end LongTails.Proofs.MarkovClippedExecution
