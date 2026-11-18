import LongTails.Algorithms.MarkovNormalizedBatch
import LongTails.Proofs.BatchedExecution

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.MarkovNormalizedExecution

open LongTails.Algorithms.MarkovNormalizedBatch LongTails.Algorithms.AbcSgd
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_method [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E)
    (η : ℝ) (K B h : ℕ) (hB : 0 < B) (hh : 0 < h) (x0 : E) (seed : Fin (K + 1))
    (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (method η K B h hB hh x0) (fun _ => (K + 1) * (B * h)) seed ξ =
      output g η B h x0 ξ seed.val := by
  refine (execute_batched (Nat.mul_pos hB hh) (sampledSgd η K x0)
    (fun s _ => ((sampledSgd η K x0).query s).2)
    (fun _ values => direction (fun i => values (slot hh i))) 0 P g ξ (K + 1) seed).trans ?_
  let step := fun (t : ℕ) (s : (sampledSgd η K x0).State) =>
    (sampledSgd η K x0).update s (direction (fun i : Fin B =>
      g s.2.2.1 (ξ (t * (B * h) + i.val * h))))
  let X := output g η B h x0 ξ
  have hs (t : ℕ) : advance step t 0 ((sampledSgd η K x0).initial seed) =
      (seed, t, X t, if seed.val < t then X seed.val else x0) := by
    induction t with
    | zero => simp [advance, sampledSgd, X, output]
    | succ t ih =>
      rw [advance_add (K := t) (J := 1), ih]
      simp only [advance, Nat.zero_add, step, sampledSgd, Prod.mk.injEq, true_and]
      refine ⟨rfl, ?_⟩
      by_cases he : t = seed.val
      · subst t
        simp
      · rw [ite_eq_right he]
        by_cases hl : seed.val < t
        · rw [ite_eq_left hl, ite_eq_left (by omega)]
        · rw [ite_eq_right hl, ite_eq_right (by omega)]
  change (sampledSgd η K x0).output (advance step (K + 1) 0 _) = _
  rw [hs]
  simp [sampledSgd, seed.isLt, X]

lemma norm_direction {B : ℕ} (v : Fin B → E) : ‖direction v‖ ≤ 1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  by_cases hz : ‖∑ i, v i‖ = 0
  · simp [hz]
  · simp [hz]

lemma output_step_le (g : E → Ω → E) (η : ℝ) (hη : 0 ≤ η) (B h : ℕ)
    (x0 : E) (ξ : ℕ → Ω) (j : ℕ) :
    ‖output g η B h x0 ξ (j + 1) - output g η B h x0 ξ j‖ ≤ η := by
  rw [output, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hη]
  exact mul_le_of_le_one_right hη (norm_direction _)

lemma norm_bound {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (grad : E → E)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x-y‖)
    (g : E → Ω → E) (B h : ℕ) (x0 : E) (k : ℕ) (ξ : ℕ → Ω) :
    ‖grad (output g η B h x0 ξ k)‖ ≤ ‖grad x0‖ + k*(L*η) := by
  induction k with
  | zero => simp [output]
  | succ k ih =>
    have hh := (norm_sub_norm_le _ _).trans ((hlip _ _).trans
      (mul_le_mul_of_nonneg_left (output_step_le g η hη B h x0 ξ k) hL))
    rw [Nat.cast_succ]
    linarith

lemma measurable_output [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (η : ℝ) (B h : ℕ) (x0 : E) (j : ℕ) : Measurable (fun ξ => output g η B h x0 ξ j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [output, direction]
    have hm (i : Fin B) : Measurable (fun ξ => g (output g η B h x0 ξ j)
        (ξ (j * (B * h) + i.val * h))) :=
      hg.comp (ih.prodMk (measurable_pi_apply _))
    fun_prop

end LongTails.Proofs.MarkovNormalizedExecution
