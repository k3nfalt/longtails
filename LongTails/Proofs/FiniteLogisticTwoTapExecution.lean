import LongTails.Algorithms.FiniteLogisticTwoTap
import LongTails.Proofs.Execution

open MeasureTheory OracleTemplate
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Algorithms.FiniteLogisticTwoTap

namespace LongTails.Proofs.FiniteLogisticTwoTapExecution

lemma algorithm_family (p : Params) {η : ℝ} (hη : 0 < η) : family p (algorithm p η) :=
  ⟨η, id, id, hη, measurable_id, Measure.map_id, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl⟩

noncomputable def step {d : ℕ} (μ η : ℝ) (i : Fin d) (x : Weights d) : Weights d :=
  let a := answer (signedInput μ i false) x
  let b := answer (signedInput μ i true) x
  x + (η / 2) • (Real.sigmoid (-a.margin) • a.direction + Real.sigmoid (-b.margin) • b.direction)

noncomputable def stoppedStep {d : ℕ} (μ η : ℝ) (i : Fin d) (x : Weights d) : Weights d := by
  classical
  exact if Separates μ i x then x else step μ η i x

lemma execute_pairs (p : Params) (η : ℝ) (i : Fin p.d)
    (O : Oracle (Bool × Weights p.d) (Reply p.d))
    (hO : spec.admissible p i O) (g : Weights p.d) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    execute O (algorithm p η) (fun _ => 2 * n) g ξ =
      (stoppedStep p.μ η i)^[n] (start p.r g) := by
  classical
  let reply := fun q : Bool × Weights p.d => answer (signedInput p.μ i q.1) q.2
  erw [execute_eq_of_answer_eq O reply (fun k q s => hO k (0, q) s), execute_iterate]
  let next := fun s : State p.d => update η s (reply (s.first.isSome, s.point))
  have hpair (x : Weights p.d) : next (next ⟨x, none⟩) = ⟨stoppedStep p.μ η i x, none⟩ := by
    by_cases h : Separates p.μ i x
    · rw [stoppedStep, ite_eq_left h]
      unfold Separates at h
      simp [next, reply, update, h]
    · rw [stoppedStep, ite_eq_right h]
      unfold Separates at h
      simp [next, reply, update, step, h]
  have hstate (x : Weights p.d) :
      next^[2 * n] ⟨x, none⟩ = ⟨(stoppedStep p.μ η i)^[n] x, none⟩ := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, Function.iterate_succ_apply]
      change next^[2 * n] (next (next ⟨x, none⟩)) = _
      rw [hpair, ih, Function.iterate_succ_apply]
  exact congrArg output (hstate (start p.r g))

lemma separates_neg {d : ℕ} (μ : ℝ) (i : Fin d) (x : Weights d) :
    Separates μ i (-x) ↔ Separates μ i x := by simp [Separates, answer]

lemma step_neg {d : ℕ} (μ η : ℝ) (i : Fin d) (x : Weights d) :
    step μ η i (-x) = -step μ η i x := by
  simp only [step, answer, map_neg, inner_neg_left, inner_neg_right, neg_neg, smul_neg, ← neg_add]

lemma trajectory_neg {d : ℕ} (μ η : ℝ) (i : Fin d) (x : Weights d) (n : ℕ) :
    (step μ η i)^[n] (-x) = -(step μ η i)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_neg]

lemma stopped_reaches {d : ℕ} {μ η : ℝ} {i : Fin d} {x : Weights d} {m n : ℕ}
    (hm : m ≤ n) (hhit : Separates μ i ((step μ η i)^[m] x)) :
    Separates μ i ((stoppedStep μ η i)^[n] x) := by
  classical
  have hstay (y : Weights d) (hy : Separates μ i y) (k : ℕ) :
      (stoppedStep μ η i)^[k] y = y := Function.iterate_fixed (by simp [stoppedStep, hy]) k
  induction m generalizing x n with
  | zero =>
    rwa [hstay x hhit n]
  | succ m ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    by_cases hy : Separates μ i x
    · rwa [hstay x hy _]
    · rw [Function.iterate_succ_apply, stoppedStep, ite_eq_right hy]
      exact ih (by omega) (by simpa only [Function.iterate_succ_apply] using hhit)

end LongTails.Proofs.FiniteLogisticTwoTapExecution
