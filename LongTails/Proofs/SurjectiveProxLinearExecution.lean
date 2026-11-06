import LongTails.Proofs.SurjectiveProxLinearTrajectory
import LongTails.Proofs.Execution
import LongTails.Proofs.SurjectiveProxLinearSampling

open MeasureTheory

namespace LongTails.Proofs.SurjectiveProxLinearExecution

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory

noncomputable def recursiveMean {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : ℕ → V) : ℕ → V
  | 0 => 0
  | n + 1 => recursiveMean A n + (1 / ((n : ℝ) + 1)) • (A n - recursiveMean A n)

lemma recursiveMean_weighted {V : Type*} [AddCommGroup V] [Module ℝ V] (A : ℕ → V) :
    ∀ n : ℕ, (n : ℝ) • recursiveMean A n = ∑ i ∈ Finset.range n, A i
  | 0 => by simp [recursiveMean]
  | n + 1 => by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hcancel : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := mul_one_div_cancel hn
    simp only [recursiveMean, Nat.cast_add, Nat.cast_one, smul_add, smul_smul, hcancel,
      one_smul, Finset.sum_range_succ]
    rw [add_smul, one_smul, recursiveMean_weighted A n]
    abel

lemma recursiveMean_sum {V : Type*} [AddCommGroup V] [Module ℝ V] (A : ℕ → V)
    (n : ℕ) (hn : 0 < n) :
    recursiveMean A n = (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, A i := by
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have h := congrArg (fun z : V => (1 / (n : ℝ)) • z) (recursiveMean_weighted A n)
  simpa only [smul_smul, one_div_mul_cancel hn0, one_smul] using h

noncomputable def indexedStep (p : Params) (Z : p.E → p.Ω → Primitive p)
    (ξ : ℕ → p.Ω) (sc : State p × ℕ) : State p × ℕ :=
  (update p sc.1 (Z (query p sc.1).1 (ξ sc.2), Z (query p sc.1).2 (ξ sc.2)), sc.2 + 1)

noncomputable def rawRun (p : Params) (Z : p.E → p.Ω → Primitive p)
    (ξ : ℕ → p.Ω) (t n : ℕ) : State p × ℕ :=
  (indexedStep p Z ξ)^[n] (⟨t, 0, p.x0, 0, 0⟩, 0)

lemma rawRun_succ (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) (t n : ℕ) :
    rawRun p Z ξ t (n + 1) = indexedStep p Z ξ (rawRun p Z ξ t n) := by
  exact Function.iterate_succ_apply' _ _ _

lemma run_initial (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) (t : ℕ) :
    ∀ n, n ≤ initialBatch p → rawRun p Z ξ t n =
      (⟨t, n, p.x0, recursiveMean (fun j => Z p.x0 (ξ j)) n, 0⟩, n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [rawRun_succ, run_initial p Z ξ t n (by omega)]
    have hlt : n < initialBatch p := by omega
    have hnot : ¬initialBatch p ≤ n := by omega
    simp only [indexedStep, query, update, hlt, hnot, false_and, ite_false, ite_true,
      recursiveMean]

noncomputable def liftedOracle (p : Params) (Z : p.E → p.Ω → Primitive p)
    (x : p.E) (ω : p.Ω) : JointSpace p := jointEquiv p (Z x ω)

lemma initial_estimator_identity (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) :
    jointEquiv p (recursiveMean (fun j => Z p.x0 (ξ j)) (initialBatch p)) =
      initialEstimator p (liftedOracle p Z) ξ := by
  have hn : 0 < initialBatch p := by unfold initialBatch; omega
  rw [recursiveMean_sum _ _ hn]
  simp only [map_smul, map_sum, initialEstimator, liftedOracle]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun n => jointEquiv p (Z p.x0 (ξ n))) (initialBatch p)).symm

lemma initial_estimator_inverse (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) :
    recursiveMean (fun j => Z p.x0 (ξ j)) (initialBatch p) =
      (jointEquiv p).symm (initialEstimator p (liftedOracle p Z) ξ) := by
  apply (jointEquiv p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact initial_estimator_identity p Z ξ

lemma run_training (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) (t : ℕ) :
    ∀ j, j ≤ t → rawRun p Z ξ t (initialBatch p + j) =
      (⟨t, initialBatch p + j, (trajectory p (liftedOracle p Z) ξ j).1,
        (jointEquiv p).symm (trajectory p (liftedOracle p Z) ξ j).2, 0⟩, initialBatch p + j)
  | 0, _ => by
    rw [Nat.add_zero, run_initial p Z ξ t (initialBatch p) le_rfl, initial_estimator_inverse]
    rfl
  | j + 1, hj => by
    rw [show initialBatch p + (j + 1) = (initialBatch p + j) + 1 by omega,
      rawRun_succ, run_training p Z ξ t j (by omega)]
    have h1 : ¬initialBatch p + j < initialBatch p := by omega
    have h2 : initialBatch p + j < initialBatch p + t := by omega
    have h3 : initialBatch p ≤ initialBatch p + j := by omega
    simp only [indexedStep, query, update, h1, h2, h3, and_self, ite_false, ite_true,
      trajectory, nextPoint, liftedOracle, map_add, map_smul, map_sub,
      ContinuousLinearEquiv.symm_apply_apply]

lemma run_certificate (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) (t : ℕ) :
    ∀ j, j ≤ certificateBatch p → rawRun p Z ξ t (initialBatch p + t + j) =
      (⟨t, initialBatch p + t + j, (trajectory p (liftedOracle p Z) ξ t).1,
        (jointEquiv p).symm (trajectory p (liftedOracle p Z) ξ t).2,
        recursiveMean (fun l => Z (trajectory p (liftedOracle p Z) ξ t).1
          (ξ (initialBatch p + t + l))) j⟩, initialBatch p + t + j)
  | 0, _ => by
    rw [Nat.add_zero, run_training p Z ξ t t le_rfl]
    rfl
  | j + 1, hj => by
    rw [show initialBatch p + t + (j + 1) = (initialBatch p + t + j) + 1 by omega,
      rawRun_succ, run_certificate p Z ξ t j (by omega)]
    have h1 : ¬initialBatch p + t + j < initialBatch p := by omega
    have h2 : ¬initialBatch p + t + j < initialBatch p + t := by omega
    have h3 : initialBatch p + t + j < initialBatch p + t + certificateBatch p := by omega
    simp only [indexedStep, query, update, h1, h2, h3, and_false, ite_false, ite_true,
      Nat.add_sub_cancel_left, recursiveMean]

lemma run_frozen (p : Params) (Z : p.E → p.Ω → Primitive p) (ξ : ℕ → p.Ω) (t : ℕ) :
    ∀ n, (rawRun p Z ξ t (initialBatch p + t + certificateBatch p + n)).1 =
      ⟨t, initialBatch p + t + certificateBatch p, (trajectory p (liftedOracle p Z) ξ t).1,
        (jointEquiv p).symm (trajectory p (liftedOracle p Z) ξ t).2,
        recursiveMean (fun l => Z (trajectory p (liftedOracle p Z) ξ t).1
          (ξ (initialBatch p + t + l))) (certificateBatch p)⟩
  | 0 => by rw [Nat.add_zero, run_certificate p Z ξ t (certificateBatch p) le_rfl]
  | n + 1 => by
    rw [show initialBatch p + t + certificateBatch p + (n + 1) =
      (initialBatch p + t + certificateBatch p + n) + 1 by omega, rawRun_succ]
    change update p (rawRun p Z ξ t (initialBatch p + t + certificateBatch p + n)).1 _ = _
    rw [run_frozen p Z ξ t n]
    have h1 : ¬initialBatch p + t + certificateBatch p < initialBatch p := by omega
    have h2 : ¬initialBatch p + t + certificateBatch p < initialBatch p + t := by omega
    simp only [update, h1, h2, lt_self_iff_false, ite_false]

lemma execute_output (p : Params) (Z : p.E → p.Ω → Primitive p)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) (t : Fin (iterations p + 1))
    (ξ : ℕ → p.Ω) (hK : initialBatch p + iterations p + certificateBatch p ≤ K) :
    execute { Seed := fun _ => p.Ω
              law := P
              answer := fun _ (_, z) ω => (Z z.1 ω, Z z.2 ω) }
      (algorithm p) (fun _ => K) t ξ =
      ((trajectory p (liftedOracle p Z) ξ t.val).1,
        dualPoint p (recursiveMean (fun l => Z (trajectory p (liftedOracle p Z) ξ t.val).1
          (ξ (initialBatch p + t.val + l))) (certificateBatch p))) := by
  let O : Oracle (p.E × p.E) (Primitive p × Primitive p) :=
    { Seed := fun _ => p.Ω
      law := P
      answer := fun _ (_, z) ω => (Z z.1 ω, Z z.2 ω) }
  change execute O (algorithm p) (fun _ => K) t ξ = _
  refine (execute_indexed_of_answer O (algorithm p) K t ξ
    (fun k q => (Z q.2.1 (ξ k), Z q.2.2 (ξ k))) (fun _ _ => rfl)).trans ?_
  obtain ⟨n, hn⟩ : ∃ n, K = initialBatch p + t.val + certificateBatch p + n :=
    ⟨K - (initialBatch p + t.val + certificateBatch p), by have := t.isLt; omega⟩
  subst hn
  change output p (rawRun p Z ξ t.val
    (initialBatch p + t.val + certificateBatch p + n)).1 = _
  rw [run_frozen]
  rfl

lemma raw_certificate_eq (p : Params) (Z : p.E → p.Ω → Primitive p)
    (ξ : ℕ → p.Ω) (t : ℕ) :
    recursiveMean (fun l => Z (trajectory p (liftedOracle p Z) ξ t).1
      (ξ (initialBatch p + t + l))) (certificateBatch p) =
      (jointEquiv p).symm
        (SurjectiveProxLinearSampling.certificateEstimator p (liftedOracle p Z) ξ t) := by
  apply (jointEquiv p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    recursiveMean_sum _ _ (by unfold certificateBatch; omega)]
  simp only [map_smul, map_sum, SurjectiveProxLinearSampling.certificateEstimator, liftedOracle]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun n => jointEquiv p
    (Z (trajectory p (liftedOracle p Z) ξ t).1 (ξ (initialBatch p + t + n))))
    (certificateBatch p)).symm

lemma execute_selected (p : Params) (Z : p.E → p.Ω → Primitive p)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) (t : Fin (iterations p + 1))
    (ξ : ℕ → p.Ω) (hK : initialBatch p + iterations p + certificateBatch p ≤ K) :
    execute { Seed := fun _ => p.Ω
              law := P
              answer := fun _ (_, z) ω => (Z z.1 ω, Z z.2 ω) }
      (algorithm p) (fun _ => K) t ξ =
      ((trajectory p (liftedOracle p Z) ξ t.val).1,
        dualPoint p ((jointEquiv p).symm
          (SurjectiveProxLinearSampling.certificateEstimator p (liftedOracle p Z) ξ t.val))) := by
  rw [execute_output p Z P K t ξ hK, raw_certificate_eq]

end LongTails.Proofs.SurjectiveProxLinearExecution
