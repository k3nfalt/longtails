import LongTails.Proofs.AffineSoftmaxAmplification

namespace LongTails.Proofs.AffineSoftmaxQuerySafety

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.AffineSoftmaxAcceleration

noncomputable def QueriesWithin {Q R U : Type*} (reply : Q → R) (allowed : Q → Prop) : Program Q R U → Prop
  | .done _ => True
  | .ask q next => allowed q ∧ QueriesWithin reply allowed (next (reply q))

lemma queriesWithin_bind {Q R U V : Type*} (reply : Q → R) (allowed : Q → Prop)
    (p : Program Q R U) (next : U → Program Q R V)
    (hp : QueriesWithin reply allowed p) (hn : QueriesWithin reply allowed (next (Program.eval reply p))) :
    QueriesWithin reply allowed (p.bind next) := by
  induction p with
  | done u => exact hn
  | ask q rest ih => exact ⟨hp.1, ih (reply q) hp.2 hn⟩

lemma queriesWithin_map {Q R U V : Type*} (reply : Q → R) (allowed : Q → Prop)
    (p : Program Q R U) (f : U → V) (hp : QueriesWithin reply allowed p) :
    QueriesWithin reply allowed (p.map f) := queriesWithin_bind reply allowed p _ hp trivial

lemma queriesWithin_query {Q R U : Type*} (reply : Q → R) (allowed : Q → Prop)
    (p : Program Q R U) (fallback : Q) (hf : allowed fallback) (hp : QueriesWithin reply allowed p) :
    allowed (p.query fallback) := by
  cases p with
  | done u => exact hf
  | ask q rest => exact hp.1

lemma queriesWithin_update {Q R U : Type*} (reply : Q → R) (allowed : Q → Prop)
    (p : Program Q R U) (fallback : Q) (hp : QueriesWithin reply allowed p) :
    QueriesWithin reply allowed (p.update (reply (p.query fallback))) := by
  cases p with
  | done u => trivial
  | ask q rest => exact hp.2

lemma queriesWithin_iterate {Q R U : Type*} (reply : Q → R) (allowed : Q → Prop)
    (fallback : Q) (n : ℕ) (p : Program Q R U) (hp : QueriesWithin reply allowed p) :
    QueriesWithin reply allowed ((fun p : Program Q R U => p.update (reply (p.query fallback)))^[n] p) := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (queriesWithin_update reply allowed p fallback hp)

lemma reciprocalPlan_queries {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ : ℝ) (x : E) (indices : List ι) (reply : ι × E → ℝ × E)
    {X : Set E} (hx : x ∈ X) :
    QueriesWithin reply (fun q => q.2 ∈ X) (reciprocalPlan s τ x indices) := by
  induction indices with
  | nil => trivial
  | cons i indices ih => exact ⟨hx, queriesWithin_map reply _ _ _ ih⟩

lemma estimatorPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ : ℝ) (x : E) (i : ι) (indices : List ι) (reply : ι × E → ℝ × E)
    {X : Set E} (hx : x ∈ X) :
    QueriesWithin reply (fun q => q.2 ∈ X) (estimatorPlan s τ x i indices) :=
  ⟨hx, queriesWithin_map reply _ _ _ (reciprocalPlan_queries s τ x indices reply hx)⟩

lemma seededEstimatorPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ : ℝ) (x : E) (seed : StepSeed) (reply : ι × E → ℝ × E)
    {X : Set E} (hx : x ∈ X) :
    QueriesWithin reply (fun q => q.2 ∈ X) (seededEstimatorPlan s τ x seed) :=
  estimatorPlan_queries s τ x _ _ reply hx

lemma componentRepliesPlan_queries {ι E : Type*}
    (x : E) (reply : ι × E → ℝ × E) {X : Set E} (hx : x ∈ X) (n : ℕ) (indices : Fin n → ι) :
    QueriesWithin reply (fun q => q.2 ∈ X) (componentRepliesPlan x n indices) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hx, queriesWithin_map reply _ _ _ (ih _)⟩

lemma cachePlan_queries {E : Type*}
    (m : ℕ) (x : E) (reply : Fin m × E → ℝ × E) {X : Set E} (hx : x ∈ X) :
    QueriesWithin reply (fun q => q.2 ∈ X) (cachePlan m x) :=
  queriesWithin_map reply _ _ _ (componentRepliesPlan_queries x reply hx m id)

lemma solverPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ D μ : ℝ) (project : E → E) (initial : E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X)
    (hp : ∀ x, project x ∈ C) (hi : initial ∈ C) (n : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ X) (solverPlan s τ D μ project initial seeds n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply queriesWithin_bind reply _ _ _ ih
    apply queriesWithin_map
    apply seededEstimatorPlan_queries
    rw [AffineSoftmaxAcceleration.solverPlan_eval]
    exact hCX (AffineSoftmaxAcceleration.solver_query_mem hC hp D _ hi seeds n)

lemma restartPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ μ : ℝ) (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E)
    (initial : E) (seeds : ℕ → ℕ → StepSeed) (reply : ι × E → ℝ × E)
    {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X) (hp : ∀ x, project x ∈ C) (hi : initial ∈ C) (n : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ X) (restartPlan s τ μ D steps project initial seeds n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply queriesWithin_bind reply _ _ _ ih
    apply queriesWithin_map
    apply solverPlan_queries s τ (D n) μ project _ (seeds n) reply hC hCX hp
    rw [AffineSoftmaxRestarts.restartPlan_eval]
    exact AffineSoftmaxRestarts.restartState_mem hC hp D steps _ hi seeds n

open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxSearch

lemma cachedProxPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ L G r μ ε : ℝ) (project : E → E) (seeds : ProxSeed)
    (reply : ι × E → ℝ × E) {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X)
    (hp : ∀ x, project x ∈ C) (hs : s.anchor ∈ C) :
    QueriesWithin reply (fun q => q.2 ∈ X) (cachedProxPlan s τ L G r μ ε project seeds) :=
  restartPlan_queries s τ μ _ _ project s.anchor seeds reply hC hCX hp hs _

lemma multilevelPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ L G r μ δ : ℝ) (project : E → E) (J : ℕ) (seed : MultilevelSeed)
    (reply : ι × E → ℝ × E) {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X)
    (hp : ∀ x, project x ∈ C) (hs : s.anchor ∈ C) :
    QueriesWithin reply (fun q => q.2 ∈ X) (multilevelPlan s τ L G r μ δ project J seed) := by
  apply queriesWithin_bind reply _ _ _ (cachedProxPlan_queries s τ L G r μ _ project _ reply hC hCX hp hs)
  split_ifs
  · apply queriesWithin_bind reply _ _ _ (cachedProxPlan_queries s τ L G r μ _ project _ reply hC hCX hp hs)
    exact queriesWithin_map reply _ _ _ (cachedProxPlan_queries s τ L G r μ _ project _ reply hC hCX hp hs)
  · trivial

lemma cachedProxGradientPlan_queries {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : Snapshot ι E) (τ L G r μ σ β : ℝ) (project : E → E) (seed : MultilevelSeed)
    (reply : ι × E → ℝ × E) {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X)
    (hp : ∀ x, project x ∈ C) (hs : s.anchor ∈ C) :
    QueriesWithin reply (fun q => q.2 ∈ X) (cachedProxGradientPlan s τ L G r μ σ β project seed) :=
  queriesWithin_map reply _ _ _ (multilevelPlan_queries s τ L G r μ _ project _ seed reply hC hCX hp hs)

lemma selectTrialsPlan_queries {Q R E : Type*} (reply : Q → R) (allowed : Q → Prop)
    (trial : ℕ → Program Q R (E × ℝ)) (initial : E × ℝ) (n : ℕ)
    (ht : ∀ j, QueriesWithin reply allowed (trial j)) :
    QueriesWithin reply allowed (selectTrialsPlan trial initial n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply queriesWithin_bind reply allowed _ _ ih
    exact queriesWithin_map reply allowed _ _ (ht n)

lemma boostedCachedPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (s : Snapshot (Fin m) E) (τ L G r μ δ : ℝ) (project : E → E)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E)
    {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X) (hp : ∀ x, project x ∈ C) (hs : s.anchor ∈ C) :
    QueriesWithin reply (fun q => q.2 ∈ X) (boostedCachedPlan m s τ L G r μ δ project seeds b) := by
  apply queriesWithin_map
  apply selectTrialsPlan_queries
  intro j
  apply queriesWithin_bind reply _ _ _ (cachedProxPlan_queries s τ L G r μ δ project (seeds j) reply hC hCX hp hs)
  apply queriesWithin_map
  apply queriesWithin_map
  exact cachePlan_queries m _ reply (hCX (AffineSoftmaxBallSolver.cachedProxPlan_mem hC s τ L G r μ δ project hp hs reply (seeds j)))

lemma probePlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L G r μ : ℝ) (project : E → E)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E)
    {C X : Set E} (hC : Convex ℝ C) (hCX : C ⊆ X) (hp : ∀ x, project x ∈ C) (hc : center ∈ C) :
    QueriesWithin reply (fun q => q.2 ∈ X) (probePlan m center τ L G r μ project seeds b) := by
  apply queriesWithin_bind reply _ _ _ (cachePlan_queries m center reply (hCX hc))
  apply queriesWithin_map
  apply boostedCachedPlan_queries m _ τ L G r μ _ project seeds b reply hC hCX hp
  simpa only [AffineSoftmaxExecution.cachePlan_eval] using hc

lemma bisectPlan_queries {Q R : Type*} (reply : Q → R) (allowed : Q → Prop)
    (probe : ℕ → ℝ → Program Q R ℝ) (hp : ∀ i μ, QueriesWithin reply allowed (probe i μ))
    (r : ℝ) (n index : ℕ) (lower upper : ℝ) :
    QueriesWithin reply allowed (bisectPlan probe r n index lower upper) := by
  induction n generalizing index lower upper with
  | zero => exact queriesWithin_bind reply allowed _ _ (hp _ _) trivial
  | succ n ih =>
    apply queriesWithin_bind reply allowed _ _ (hp _ _)
    split_ifs
    · exact ih _ _ _
    · exact ih _ _ _
    · trivial

lemma gridPlan_queries {Q R : Type*} (reply : Q → R) (allowed : Q → Prop)
    (probe : ℕ → ℝ → Program Q R ℝ) (hp : ∀ i μ, QueriesWithin reply allowed (probe i μ))
    (r floor upper : ℝ) (H n index : ℕ) (previous : ℝ) :
    QueriesWithin reply allowed (gridPlan probe r floor upper H n index previous) := by
  induction n generalizing index previous with
  | zero =>
    apply queriesWithin_bind reply allowed _ _ (hp _ _)
    split_ifs
    · trivial
    · exact bisectPlan_queries reply allowed probe hp r _ _ _ _
    · trivial
  | succ n ih =>
    apply queriesWithin_bind reply allowed _ _ (hp _ _)
    split_ifs
    · trivial
    · exact bisectPlan_queries reply allowed probe hp r _ _ _ _
    · exact ih _ _

open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget
open LongTails.Algorithms.AffineSoftmaxAmplification

lemma regularizationSearchPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (seeds : ℕ → ProbeSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (regularizationSearchPlan m X state τ L G r floor cap H b seeds) := by
  apply gridPlan_queries
  intro i μ
  let center := predictor (max floor μ) state
  let C := X ∩ Metric.closedBall center r
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state
    (hf.trans_le (le_max_left floor μ)) hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr⟩
  exact probePlan_queries m center τ L G r (max floor μ) _ (seeds i) b reply hC Set.inter_subset_left
    (fun z => (OracleTemplate.SaddlePoint.project_spec ⟨center, hcC⟩ hCcompact hC z).1) hcC

lemma finalStepPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G D ε : ℝ) {r μ : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (H : ℕ) (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (finalStepPlan m X state τ L G r D ε μ H seed) := by
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let project := OracleTemplate.SaddlePoint.project C
  let s := Program.eval reply (cachePlan m center)
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr⟩
  have hp : ∀ z, project z ∈ C := fun z =>
    (OracleTemplate.SaddlePoint.project_spec ⟨center, hcC⟩ hCcompact hC z).1
  have hs : s.anchor ∈ C := by simpa only [s, AffineSoftmaxExecution.cachePlan_eval] using hcC
  apply queriesWithin_bind reply _ _ _ (cachePlan_queries m center reply hcenter)
  apply queriesWithin_bind reply _ _ _ (cachedProxPlan_queries s τ L G r μ _ project seed.1 reply hC Set.inter_subset_left hp hs)
  exact queriesWithin_map reply _ _ _ (cachedProxGradientPlan_queries s τ L G r μ _ _ project seed.2 reply hC Set.inter_subset_left hp hs)

lemma outerStepPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G D ε : ℝ) {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (outerStepPlan m X state τ L G r D ε floor cap H b seed) := by
  apply queriesWithin_bind reply _ _ _
    (regularizationSearchPlan_queries m hX hcompact state hA hx hv τ L G hr hf cap H b seed.1 reply)
  have hμ : Program.eval reply (regularizationSearchPlan m X state τ L G r floor cap H b seed.1) ∈ Set.Icc floor cap :=
    AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  exact finalStepPlan_queries m hX hcompact state hA hx hv τ L G D ε hr (hf.trans_le hμ.1) H seed.2 reply

lemma outerRunPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (n : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ X) (outerRunPlan m X initial τ L G r D ε floor cap H b seeds n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply queriesWithin_bind reply _ _ _ ih
    split_ifs
    · trivial
    · have hs := AffineSoftmaxOuterExecution.outerRunPlan_feasible m hX hcompact initial hi τ L G D ε hr hf hfc H b seeds reply n
      exact outerStepPlan_queries m hX hcompact _ hs.1 hs.2.1 hs.2.2 τ L G D ε hr hf hfc H b (seeds n) reply

lemma budgetedOuterPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) := by
  unfold budgetedOuterPlan
  split_ifs
  · exact queriesWithin_map reply _ _ _ (outerRunPlan_queries m hX hcompact initial hi τ L G D ε hr hf hfc H b seeds reply N)
  · trivial

lemma scoredPlan_queries {E : Type*}
    (m : ℕ) (trial : Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E) {X : Set E}
    (hq : QueriesWithin reply (fun q => q.2 ∈ X) trial) (hx : Program.eval reply trial ∈ X) :
    QueriesWithin reply (fun q => q.2 ∈ X) (scoredPlan m trial) := by
  apply queriesWithin_bind reply _ _ _ hq
  apply queriesWithin_map
  exact queriesWithin_map reply _ _ _ (cachePlan_queries m _ reply hx)

lemma repeatedPlan_queries {E : Type*}
    (m : ℕ) (trial : ℕ → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E) {X : Set E}
    (hq : ∀ j, QueriesWithin reply (fun q => q.2 ∈ X) (trial j)) (hx : ∀ j, Program.eval reply (trial j) ∈ X) (n : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ X) (repeatedPlan m trial n) := by
  apply queriesWithin_bind reply _ _ _ (scoredPlan_queries m (trial 0) reply (hq 0) (hx 0))
  apply queriesWithin_map
  exact selectTrialsPlan_queries reply _ _ _ n (fun j => scoredPlan_queries m _ reply (hq (j + 1)) (hx (j + 1)))

lemma amplifiedOuterPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (seeds : ℕ → ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (amplifiedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) := by
  apply repeatedPlan_queries
  · intro j
    exact budgetedOuterPlan_queries m hX hcompact initial hi τ L G D ε hr hf hfc H b N J K (seeds j) reply
  · intro j
    exact AffineSoftmaxBudgetGuarantee.budgetedOuterPlan_mem m hX hcompact initial hi τ L G D ε hr hf hfc H b N J K (seeds j) reply

end LongTails.Proofs.AffineSoftmaxQuerySafety
