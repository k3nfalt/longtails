import LongTails.Proofs.PolynomialMixingAccuracy
import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.MatrixGeneralizedExecution

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingExecution

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining LongTails.Proofs.PolynomialMixingAccuracy
open LongTails.Proofs.RecursiveEnvelopeExecution LongTails.Proofs.StochasticEnvelopeExecution
open OracleTemplate LongTails.Algorithms

variable {q : Params} (g : Point q → ℝ → Space q)

def blockCost (c : Schedule) := c.outerSkip + (c.innerSkip + 1) * c.samples

def cost (c : Schedule) := blockCost c * (c.trials + 1) * c.trials

def slice (gap call : ℕ) (z : Path) : Path := fun i => z (call + (gap + 1) * i)

def observations (c : Schedule) (z : Path) (k : Fin c.trials) (j : Fin (c.trials + 1)) : Path :=
  slice c.innerSkip (blockCost c * (k.val * (c.trials + 1) + j.val)) z

noncomputable def trial (c : Schedule) (w : Fin (c.trials + 1) → Path) : Point q × ℝ :=
  let x := average g c.samples (w 0)
  (x, RobustGradient.pilotCenter (q.ε / 2) (fun j => score g x c.samples (w j.succ)))

noncomputable def selected (c : Schedule) (w : Fin c.trials → Fin (c.trials + 1) → Path) : Point q :=
  MatrixGeneralizedZO.selectBest (origin q) (List.ofFn fun i => trial g c (w i))

lemma eval_padding {Q R U : Type} (reply : ℕ → Q → R) (x : Q) (u : U) (n call : ℕ) :
    evalAt reply (QueryLayers.paddingPlan x u n) call = u := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call + 1)

lemma eval_padded {Q R U : Type} (reply : ℕ → Q → R) (x : Q) {k : ℕ} (plan : QueryPlan Q R U k) (n call : ℕ) :
    evalAt reply (QueryLayers.paddedPlan x plan n) call = evalAt reply plan call := by
  rw [QueryLayers.paddedPlan, evalAt_bind, eval_padding]

lemma eval_spaced (z : Path) (gap call : ℕ) (x : Point q) :
    evalAt (fun t y => g y (z t)) (spacedQuery q gap x) call = g x (z call) :=
  eval_padding _ _ _ _ _

lemma eval_train (z : Path) (gap call n : ℕ) :
    evalAt (fun t y => g y (z t)) (train q gap n) call = state g n (slice gap call z) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [train, evalAt_castPlan, evalAt_bind, evalAt_map, eval_spaced, ih, state_succ]; rfl

lemma eval_candidate (z : Path) (c : Schedule) (call : ℕ) :
    evalAt (fun t y => g y (z t)) (candidatePlan q c) call =
      average g c.samples (slice c.innerSkip call z) := by
  rw [candidatePlan, eval_padded, evalAt_map, eval_train]; rfl

lemma eval_score (z : Path) (c : Schedule) (call : ℕ) (x : Point q) :
    evalAt (fun t y => g y (z t)) (scorePlan q c x) call =
      score g x c.samples (slice c.innerSkip call z) := by
  simp only [scorePlan, eval_padded, evalAt_map, evalAt_collectPlans, eval_spaced, score,
    slice]
  rw [← Fin.sum_univ_eq_sum_range]

lemma eval_output (z : Path) (c : Schedule) :
    evalAt (fun t y => g y (z t)) (output q c) 0 = selected g c (observations c z) := by
  simp only [output, evalAt_map, evalAt_collectPlans, trialPlan, evalAt_bind, eval_candidate,
    eval_score, Nat.zero_add, selected, trial, observations, blockCost, Fin.val_zero, Fin.val_succ,
    Nat.add_zero]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_left_comm, Nat.mul_comm]

lemma execute_output (P : ProbabilityMeasure Path) (K : ℕ) (hK : cost (schedule q) ≤ K)
    (s : Unit) (z : Path) :
    execute (⟨fun _ => ℝ, P, fun _ (_, x) v => g x v⟩ : Oracle (Point q) (Space q))
      (method q) (fun _ => K) s z = selected g (schedule q) (observations (schedule q) z) := by
  let O : Oracle (Point q) (Space q) := ⟨fun _ => ℝ, P, fun _ (_, x) v => g x v⟩
  have hr (n : ℕ) (x : Point q) : executeAnswerAt O (method q) s z n (0, x) = g x (z n) := by
    change g x (z (executeIndexedState O (method q) s z n).2.length) = _
    rw [executeIndexedState_length O (method q) s z n]
  exact (execute_plan_indexed (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit)
    (origin q) (origin q) (fun _ => output q (schedule q)) O s z hK).trans (by
      change evalAt (fun n x => executeAnswerAt O (method q) s z n (0, x)) _ _ = _
      simp_rw [hr]
      exact eval_output g z _)

end LongTails.Proofs.PolynomialMixingExecution
