import LongTails.Algorithms.NonlinearTemporalAccelerated
import LongTails.Proofs.QueryPlan
import Mathlib.Algebra.BigOperators.Fin

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

variable {Q R U V : Type*}

def evaluateFrom (g : ℕ → Q → R) (start : ℕ) : {k : ℕ} → QueryPlan Q R U k → U
  | _, .done value => value
  | _, .ask query next => evaluateFrom g (start + 1) (next (g start query))

lemma evaluateFrom_map (g : ℕ → Q → R) (f : U → V) {k : ℕ}
    (plan : QueryPlan Q R U k) (start : ℕ) :
    evaluateFrom g start (plan.map f) = f (evaluateFrom g start plan) := by
  induction plan generalizing start with
  | done value => rfl
  | ask q rest ih => exact ih (g start q) (start + 1)

lemma evaluateFrom_bind (g : ℕ → Q → R) {k m : ℕ}
    (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m) (start : ℕ) :
    evaluateFrom g start (plan.bind next) =
      evaluateFrom g (start + k) (next (evaluateFrom g start plan)) := by
  induction plan generalizing start with
  | done value => rfl
  | @ask k q rest ih =>
      simpa only [QueryPlan.bind, evaluateFrom, Nat.add_assoc, Nat.add_comm 1 k] using
        ih (g start q) (start + 1)

lemma advance_timed_plan (g : ℕ → Q → R) (q0 : Q) {k K : ℕ}
    (plan : QueryPlan Q R U k) (h : k ≤ K) (start : ℕ) :
    StochasticGradient.advance (fun t s => QueryPlan.update s (g t (QueryPlan.query q0 s)))
      K start ⟨k, plan⟩ = ⟨0, .done (evaluateFrom g start plan)⟩ := by
  induction plan generalizing K start with
  | done value =>
      induction K generalizing start with
      | zero => rfl
      | succ K ih => exact ih (Nat.zero_le K) (start + 1)
  | @ask k q rest ih =>
      cases K with
      | zero => omega
      | succ K => exact ih (g start q) (by omega) (start + 1)

lemma execute_timed_plan {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k) (g : ℕ → Q → R)
    (seed : S) (h : k ≤ K) :
    execute { answer := fun t (_, q) _ => g t q } (QueryPlan.algorithm law q0 u0 k plan) (fun _ => K) seed =
      evaluateFrom g 0 (plan seed) := by
  erw [StochasticGradient.execute_advance]
  change QueryPlan.output u0 (StochasticGradient.advance
    (fun t s => QueryPlan.update s (g t (QueryPlan.query q0 s))) K 0 ⟨k, plan seed⟩) = _
  rw [advance_timed_plan g q0 _ h]
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma evaluateFrom_frozen (g : ℕ → E → E) (x : E) (b start : ℕ) :
    evaluateFrom g start (frozenQuery x b) = ∑ i ∈ Finset.range b, g (start + i) x := by
  induction b generalizing start with
  | zero => simp [frozenQuery, evaluateFrom]
  | succ b ih =>
      simp only [frozenQuery, evaluateFrom, evaluateFrom_map, ih]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero, Nat.add_assoc]
      rw [add_comm]
      simp only [Nat.add_comm 1]

lemma evaluateFrom_final_trajectory (g : ℕ → E → E) (θ μ : ℝ)
    (n start : ℕ) (v : ℕ → E × E)
    (hv : ∀ k, v (k + 1) = TemporalDiscrepancy.acceleratedUpdate θ μ (v k)
      (g (start + k) (TemporalDiscrepancy.acceleratedQuery θ (v k)))) :
    evaluateFrom g start (finalPlan θ μ n (v 0)) =
      List.ofFn (fun i : Fin n => (v (i + 1)).1) := by
  induction n generalizing start v with
  | zero => simp [finalPlan, evaluateFrom]
  | succ n ih =>
      simp only [finalPlan, evaluateFrom, evaluateFrom_map]
      have hv0 := hv 0
      simp only [Nat.add_zero] at hv0
      rw [← hv0]
      have hs (k : ℕ) : v (k + 1 + 1) =
          TemporalDiscrepancy.acceleratedUpdate θ μ (v (k + 1))
            (g (start + 1 + k) (TemporalDiscrepancy.acceleratedQuery θ (v (k + 1)))) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hv (k + 1)
      rw [ih (start + 1) (fun k => v (k + 1)) hs, List.ofFn_succ]
      rfl

lemma evaluateFrom_warmup_trajectory (g : ℕ → E → E) (θ μ : ℝ)
    (b n start : ℕ) (v : ℕ → E × E)
    (hv : ∀ k, v (k + 1) = TemporalDiscrepancy.acceleratedUpdate θ μ (v k)
      ((b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
        g (start + b * k + i) (TemporalDiscrepancy.acceleratedQuery θ (v k)))) :
    evaluateFrom g start (warmupPlan θ μ b n (v 0)) = v n := by
  induction n generalizing start v with
  | zero => rfl
  | succ n ih =>
      simp only [warmupPlan, id_eq, evaluateFrom_bind, evaluateFrom_frozen]
      have hv0 := hv 0
      simp only [Nat.mul_zero, Nat.add_zero] at hv0
      rw [← hv0]
      have hs (k : ℕ) : v (k + 1 + 1) =
          TemporalDiscrepancy.acceleratedUpdate θ μ (v (k + 1))
            ((b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
              g (start + b + b * k + i) (TemporalDiscrepancy.acceleratedQuery θ (v (k + 1)))) := by
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hv (k + 1)
      exact ih (start + b) (fun k => v (k + 1)) hs

lemma final_list_tail (v : ℕ → E × E) (n : ℕ) :
    (n : ℝ)⁻¹ • ((List.ofFn (fun i : Fin (2 * n) => (v (i + 1)).1)).drop n).sum =
      TemporalDiscrepancy.tailAverage (fun k => (v k).1) n n := by
  rw [two_mul]
  rw [List.ofFn_add]
  simp [List.sum_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun i => (v (i + n + 1)).1)]
  simp only [TemporalDiscrepancy.tailAverage, Nat.add_comm n]

lemma execute_twoPhase_trajectory (O : Oracle E E) (g : ℕ → E → E)
    (hO : ∀ k x seed, O.answer k (0, x) seed = g k x) (θ₀ θ μ : ℝ) (x0 : E)
    (b n₀ n K : ℕ) (hK : 2 * n + b * n₀ ≤ K)
    (w v : ℕ → E × E) (hw0 : w 0 = (x0, x0)) (hv0 : v 0 = w n₀)
    (hw : ∀ k, w (k + 1) = TemporalDiscrepancy.acceleratedUpdate θ₀ μ (w k)
      ((b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
        g (b * k + i) (TemporalDiscrepancy.acceleratedQuery θ₀ (w k))))
    (hv : ∀ k, v (k + 1) = TemporalDiscrepancy.acceleratedUpdate θ μ (v k)
      (g (b * n₀ + k) (TemporalDiscrepancy.acceleratedQuery θ (v k))))
    (seed : (twoPhaseAccelerated θ₀ θ μ x0 b n₀ n).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (twoPhaseAccelerated θ₀ θ μ x0 b n₀ n) (fun _ => K) seed ξ =
      TemporalDiscrepancy.tailAverage (fun k => (v k).1) n n := by
  erw [StochasticGradient.execute_advance]
  simp only [twoPhaseAccelerated, QueryPlan.algorithm]
  simp_rw [hO]
  change QueryPlan.output x0 (StochasticGradient.advance
    (fun t s => QueryPlan.update s (g t (QueryPlan.query x0 s))) K 0
    ⟨2 * n + b * n₀, twoPhasePlan θ₀ θ μ x0 b n₀ n⟩) = _
  rw [advance_timed_plan g x0 _ hK]
  change evaluateFrom g 0 (twoPhasePlan θ₀ θ μ x0 b n₀ n) = _
  simp only [twoPhasePlan, evaluateFrom_bind, evaluateFrom_map, Nat.zero_add]
  rw [← hw0, evaluateFrom_warmup_trajectory g θ₀ μ b n₀ 0 w
    (by simpa only [Nat.zero_add] using hw), ← hv0]
  rw [evaluateFrom_final_trajectory g θ μ (2 * n) (b * n₀) v hv, final_list_tail]

lemma frozen_gradient_identity (G : E → E) (e : ℕ → E) (x : E)
    {b : ℕ} (hb : 0 < b) (start : ℕ) :
    (b : ℝ)⁻¹ • (∑ i ∈ Finset.range b, (G x + e (start + i))) =
      G x + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, e (start + i) := by
  have hn : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [Finset.sum_add_distrib, smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]

end OracleTemplate.NonlinearTemporalDiscrepancy
