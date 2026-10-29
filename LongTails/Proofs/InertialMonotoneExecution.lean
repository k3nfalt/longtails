import LongTails.Algorithms.InertialRegularizedExtragradient
import LongTails.Proofs.SampledQueryPlan

open scoped BigOperators

namespace OracleTemplate.InertialMonotone

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma batchPlan_eval (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (b call : ℕ) :
    QueryPlan.sampledEval g ξ (batchPlan x b) call =
      ∑ i : Fin b, g x (ξ (call + i.val)) := by
  induction b generalizing call with
  | zero => simp [batchPlan, QueryPlan.sampledEval]
  | succ b ih =>
    simp only [batchPlan, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih,
      Fin.sum_univ_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega

lemma stepPlan_eval (g : E → Ω → E) (ξ : ℕ → Ω) (μ η r : ℝ)
    (b call : ℕ) (state : E × E) :
    QueryPlan.sampledEval g ξ (stepPlan μ η r b state) call =
      let s1 := ∑ i : Fin b, g state.2 (ξ (call + i.val))
      let y := extrapolated μ η b state.1 state.2 s1
      let s2 := ∑ i : Fin b, g y (ξ (call + b + i.val))
      transported r state.1
        (state.2 - η • ((1 / (b : ℝ)) • s2 + μ • (y - state.1))) := by
  simp only [stepPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map, batchPlan_eval]

lemma runPlan_eval_succ (g : E → Ω → E) (ξ : ℕ → Ω)
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (k call : ℕ) (state : E × E) :
    QueryPlan.sampledEval g ξ (runPlan μ η r b (k + 1) state) call =
      QueryPlan.sampledEval g ξ
        (stepPlan (μ k) (η k) (r k) (b k)
          (QueryPlan.sampledEval g ξ (runPlan μ η r b k state) call))
        (call + calls b k) := by
  exact QueryPlan.sampledEval_bind g ξ _ _ call

lemma stepPlan_eval_trial (g : E → Ω → E) (ξ : ℕ → Ω) (μ η r : ℝ)
    (b call : ℕ) (state : E × E) :
    QueryPlan.sampledEval g ξ (stepPlan μ η r b state) call =
      transported r state.1 (batchTrial g μ η b state
        (fun i => ξ (call + i.val)) (fun i => ξ (call + b + i.val))) := by
  rw [stepPlan_eval]
  rfl

lemma terminalPoint_eq [MeasurableSpace Ω] (L R σ ε : ℝ) (x0 : E)
    (g : E → Ω → E) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (K : ℕ)
    (hK : calls (batchSize σ ε (horizon L R ε)) (horizon L R ε) ≤ K)
    (seed : Unit) (ξ : ℕ → Ω) :
    terminalPoint L R σ ε x0
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, q) ω => g q ω } K (seed, ξ) =
      (QueryPlan.sampledEval g ξ
        (runPlan (regularization L (horizon L R ε)) (stepSize L (horizon L R ε))
          (growth (horizon L R ε)) (batchSize σ ε (horizon L R ε))
          (horizon L R ε) (x0, x0)) 0).2 := by
  unfold terminalPoint inertialExtragradient
  dsimp only
  erw [QueryPlan.execute_sampledPlan_of_le _ _ _ _ _ _ _ _ _ _ hK,
    QueryPlan.sampledEval_map]

lemma runPlan_eval_finiteRun (g : E → Ω → E) (ξ : ℕ → Ω)
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) (k call : ℕ) :
    QueryPlan.sampledEval g ξ (runPlan μ η r b k state) call =
      finiteRun g μ η r b state k (fun i => ξ (call + i.val)) := by
  induction k generalizing call with
  | zero => rfl
  | succ k ih =>
    rw [runPlan_eval_succ, stepPlan_eval_trial, ih]
    simp only [finiteRun, Nat.add_assoc]

end OracleTemplate.InertialMonotone
