import LongTails.Proofs.AffineResidualSaddle
import LongTails.Proofs.AffineSoftmaxQuerySafety

namespace LongTails.Proofs.AffineResidualExecution

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSaddle

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma solverPlan_eval [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (N : ℕ) :
    Program.eval reply (solverPlan C project s τ μ β D initial seeds N) =
      solverState β initial (fun k state seed =>
        Program.eval reply (stepPlan C project s τ μ (stepSize β k) D state seed)) seeds N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [solverPlan, Program.eval_bind, Program.eval_map, ih, solverState]

lemma solverPlan_cost [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (N : ℕ) :
    Program.cost reply (solverPlan C project s τ μ β D initial seeds N) = 2 * N := by
  induction N with
  | zero => simp [solverPlan, Program.cost]
  | succ N ih =>
      simp only [solverPlan, Program.cost_bind, Program.cost_map, stepPlan_cost, ih]
      omega

lemma outputPlan_cost [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (N : ℕ) :
    Program.cost reply (outputPlan C project s τ μ β D initial seeds N) = 2 * N := by
  simp only [outputPlan, Program.cost_map, solverPlan_cost]

lemma outputPlan_eval [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (N : ℕ) :
    Program.eval reply (outputPlan C project s τ μ β D initial seeds N) =
      averageOutput β initial.point N (solverState β initial (fun k state seed =>
        Program.eval reply (stepPlan C project s τ μ (stepSize β k) D state seed)) seeds N).2 := by
  simp only [outputPlan, Program.eval_map, solverPlan_eval]

omit [Fintype ι] in
lemma solverState_prefix (β : ℝ) (initial : State ι E)
    (step : ℕ → State ι E → StepSeed → State ι E × E) (seeds other : ℕ → StepSeed)
    (N : ℕ) (hprefix : ∀ k < N, seeds k = other k) :
    solverState β initial step seeds N = solverState β initial step other N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hh := ih (fun k hk => hprefix k (by omega))
      simp only [solverState, hh, hprefix N (Nat.lt_succ_self N)]

omit [Fintype ι] in
lemma solverState_sum (β : ℝ) (initial : State ι E)
    (step : ℕ → State ι E → StepSeed → State ι E × E) (seeds : ℕ → StepSeed) (N : ℕ) :
    (solverState β initial step seeds N).2 =
      ∑ k ∈ Finset.range N, iterationWeight β k •
        (step k (solverState β initial step seeds k).1 (seeds k)).2 := by
  induction N with
  | zero => simp [solverState]
  | succ N ih => simp only [solverState, Finset.sum_range_succ, ih]

open LongTails.Proofs.AffineSoftmaxQuerySafety

lemma eval_eq_of_queriesWithin {Q R U : Type*} (reply other : Q → R) (allowed : Q → Prop)
    (p : Program Q R U) (hp : QueriesWithin reply allowed p)
    (he : ∀ q, allowed q → reply q = other q) : Program.eval reply p = Program.eval other p := by
  induction p with
  | done u => rfl
  | ask q next ih =>
      change Program.eval reply (next (reply q)) = Program.eval other (next (other q))
      rw [← he q hp.1]
      exact ih (reply q) hp.2

lemma stepPlan_queriesWithin [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (project : E → E) (s : Snapshot ι E) (τ μ η D : ℝ) (state : State ι E) (seed : StepSeed)
    (reply : ι × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ C) (stepPlan C project s τ μ η D state seed) := by
  have hp := (predictor_mem_min hC hne s τ μ η state).1
  simp only [stepPlan, QueriesWithin]
  exact ⟨hp, hp, trivial⟩

lemma solverPlan_queriesWithin [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (project : E → E) (s : Snapshot ι E) (τ μ β D : ℝ) (initial : State ι E)
    (seeds : ℕ → StepSeed) (reply : ι × E → ℝ × E) (N : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ C) (solverPlan C project s τ μ β D initial seeds N) := by
  induction N with
  | zero => trivial
  | succ N ih =>
      apply queriesWithin_bind _ _ _ _ ih
      apply queriesWithin_map
      exact stepPlan_queriesWithin hC hne project s τ μ (stepSize β N) D _ _ reply

lemma outputPlan_queriesWithin [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (project : E → E) (s : Snapshot ι E) (τ μ β D : ℝ) (initial : State ι E)
    (seeds : ℕ → StepSeed) (reply : ι × E → ℝ × E) (N : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ C) (outputPlan C project s τ μ β D initial seeds N) := by
  apply queriesWithin_map
  exact solverPlan_queriesWithin hC hne project s τ μ β D initial seeds reply N

lemma localPlan_cost [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (s : Snapshot ι E) (τ μ L r α : ℝ)
    (seeds : ℕ → StepSeed) (reply : ι × E → ℝ × E) :
    Program.cost reply (localPlan C s τ μ L r α seeds) =
      2 * localSteps (Fintype.card ι) τ μ L r α := by
  exact outputPlan_cost _ _ _ _ _ _ _ _ _ _ _

lemma proxPlan_cost (m : ℕ) [NeZero m] (C : Set E) (center : E) (τ μ L r α : ℝ)
    (seeds : ℕ → StepSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (proxPlan m C center τ μ L r α seeds) =
      m + 2 * localSteps m τ μ L r α := by
  simp only [proxPlan, Program.cost_bind, AffineSoftmaxExecution.cachePlan_cost,
    localPlan_cost, Fintype.card_fin]

lemma localPlan_queriesWithin [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (s : Snapshot ι E) (τ μ L r α : ℝ) (seeds : ℕ → StepSeed) (reply : ι × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ C) (localPlan C s τ μ L r α seeds) :=
  outputPlan_queriesWithin hC hne _ _ _ _ _ _ _ _ _ _

lemma proxPlan_queriesWithin (m : ℕ) [NeZero m] {C : Set E} (hC : IsCompact C)
    (center : E) (hc : center ∈ C) (τ μ L r α : ℝ) (seeds : ℕ → StepSeed)
    (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ C) (proxPlan m C center τ μ L r α seeds) := by
  apply queriesWithin_bind
  · exact cachePlan_queries m center reply hc
  · exact localPlan_queriesWithin hC ⟨center, hc⟩ _ _ _ _ _ _ _ _

end LongTails.Proofs.AffineResidualExecution
