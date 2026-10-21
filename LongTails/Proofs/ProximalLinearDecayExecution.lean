import LongTails.Algorithms.ProximalLinearDecaySgd
import LongTails.Setups.SampledCompositeSmoothConvex
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace OracleTemplate.SampledComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type} [MeasurableSpace Ξ]

open LongTails.Setups.SampledCompositeSmoothConvex (Model oracleAnswer)

noncomputable def compositeOracle (M : Model E Ξ) : Oracle (E ⊕ (ℝ × E × E)) E where
  Seed := fun _ => Ξ
  law := ⟨Measure.infinitePi (fun _ : ℕ => (M.law : Measure Ξ)), inferInstance⟩
  answer := fun _ query ξ => oracleAnswer M query ξ

noncomputable def gprev (M : Model E Ξ) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) : ℕ → E
  | 0 => 0
  | k + 1 => M.grad (ξ (2 * k)) (path M.grad M.prox η T x0 ξ k)

omit [InnerProductSpace ℝ E] in
lemma advance_two (M : Model E Ξ) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) (j : ℕ) :
    StochasticGradient.advance
      (fun k state => (proximalLinearDecaySgd η T x0).update state
        (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
      2 (2 * j) (j, false, path M.grad M.prox η T x0 ξ j, gprev M η T x0 ξ j) =
      (j + 1, false, path M.grad M.prox η T x0 ξ (j + 1), gprev M η T x0 ξ (j + 1)) := by
  rfl

omit [InnerProductSpace ℝ E] in
lemma advance_iter (M : Model E Ξ) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ∀ K j, StochasticGradient.advance
      (fun k state => (proximalLinearDecaySgd η T x0).update state
        (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
      (2 * K) (2 * j) (j, false, path M.grad M.prox η T x0 ξ j, gprev M η T x0 ξ j) =
      (j + K, false, path M.grad M.prox η T x0 ξ (j + K), gprev M η T x0 ξ (j + K)) := by
  intro K
  induction K with
  | zero => intro j; rfl
  | succ K ih =>
    intro j
    have h2 : 2 * (K + 1) = 2 * K + 2 := by ring
    have hsplit : ∀ (c : ℕ) (st : ℕ × Bool × E × E), StochasticGradient.advance
        (fun k state => (proximalLinearDecaySgd η T x0).update state
          (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
        (2 * K + 2) c st =
        StochasticGradient.advance
          (fun k state => (proximalLinearDecaySgd η T x0).update state
            (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
          (2 * K) (c + 2) (StochasticGradient.advance
            (fun k state => (proximalLinearDecaySgd η T x0).update state
              (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
            2 c st) := by
      intro c st
      rfl
    rw [h2, hsplit, advance_two M η T x0 ξ j]
    have := ih (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    rw [this]
    congr 1 <;> [omega; (congr 1; rw [show j + 1 + K = j + (K + 1) by omega])]

omit [InnerProductSpace ℝ E] in
lemma execute_proximalLinearDecaySgd (M : Model E Ξ) (η : ℝ) (T : ℕ) (x0 : E) (K : ℕ) (ξ : ℕ → Ξ) :
    execute (compositeOracle M) (proximalLinearDecaySgd η T x0) (fun _ => 2 * K) () ξ =
      path M.grad M.prox η T x0 ξ K := by
  refine (StochasticGradient.execute_advance_indexed (compositeOracle M).law (fun _ => oracleAnswer M)
    (proximalLinearDecaySgd η T x0)
    (2 * K) () ξ).trans ?_
  have h := advance_iter M η T x0 ξ K 0
  rw [Nat.zero_add, Nat.mul_zero] at h
  change (proximalLinearDecaySgd η T x0).output (StochasticGradient.advance (fun k state =>
    (proximalLinearDecaySgd η T x0).update state
      (oracleAnswer M ((proximalLinearDecaySgd η T x0).query state) (ξ k)))
      (2 * K) 0 (0, false, path M.grad M.prox η T x0 ξ 0, gprev M η T x0 ξ 0)) = _
  rw [h]
  rfl

end OracleTemplate.SampledComposite
