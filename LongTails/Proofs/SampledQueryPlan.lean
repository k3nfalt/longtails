import LongTails.Algorithms.SampledQueryPlan
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.QueryPlan

variable {Q R U V Ω : Type*}

lemma sampledEval_bind (g : Q → Ω → R) (ξ : ℕ → Ω) {k m : ℕ}
    (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m) (call : ℕ) :
    sampledEval g ξ (bind plan next) call =
      sampledEval g ξ (next (sampledEval g ξ plan call)) (call + k) := by
  induction plan generalizing call with
  | done value => rfl
  | @ask k q rest ih =>
      simp only [bind, sampledEval]
      rw [ih]
      congr 1
      omega

lemma sampledEval_map (g : Q → Ω → R) (ξ : ℕ → Ω) (f : U → V) {k : ℕ}
    (plan : QueryPlan Q R U k) (call : ℕ) :
    sampledEval g ξ (map f plan) call = f (sampledEval g ξ plan call) := by
  induction plan generalizing call with
  | done value => rfl
  | ask q rest ih => exact ih (g q (ξ call)) (call + 1)

lemma sampledEval_traverse (g : Q → Ω → R) (ξ : ℕ → Ω) {c : ℕ}
    (k : ℕ) (plans : Fin k → QueryPlan Q R U c) (call : ℕ) :
    sampledEval g ξ (traverse k plans) call =
      List.ofFn (fun i : Fin k => sampledEval g ξ (plans i) (call + c * i.val)) := by
  induction k generalizing call with
  | zero => rfl
  | succ k ih =>
      simp only [traverse, sampledEval_bind, sampledEval_map, ih, List.ofFn_succ]
      simp only [Fin.val_zero, mul_zero, add_zero, Fin.val_succ]
      congr 2
      funext i
      congr 1
      simp only [Nat.mul_add, Nat.mul_one]
      omega

lemma advance_sampledPlan_of_le (g : Q → Ω → R) (ξ : ℕ → Ω) (q0 : Q)
    {k K : ℕ} (plan : QueryPlan Q R U k) (h : k ≤ K) (call : ℕ) :
    StochasticGradient.advance (fun j s => update s (g (query q0 s) (ξ j)))
      K call ⟨k, plan⟩ = ⟨0, done (sampledEval g ξ plan call)⟩ := by
  induction plan generalizing K call with
  | done value =>
      induction K generalizing call with
      | zero => rfl
      | succ K ih => exact ih (Nat.zero_le K) (call + 1)
  | @ask k q rest ih =>
      cases K with
      | zero => omega
      | succ K => exact ih (g q (ξ call)) (by omega) (call + 1)

lemma execute_sampledPlan_of_le {S Ω : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    (law : MeasureTheory.ProbabilityMeasure S)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k) (g : Q → Ω → R)
    (seed : S) (ξ : ℕ → Ω) (h : k ≤ K) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, q) ω => g q ω }
      (algorithm law q0 u0 k plan) (fun _ => K) seed ξ =
        sampledEval g ξ (plan seed) 0 := by
  erw [StochasticGradient.execute_advance]
  change output u0 (StochasticGradient.advance
    (fun call s => update s (g (query q0 s) (ξ call))) K 0 ⟨k, plan seed⟩) = _
  rw [advance_sampledPlan_of_le g ξ q0 _ h]
  rfl

end OracleTemplate.QueryPlan
