import LongTails.Proofs.AffineResidualBudgetGuarantee

namespace LongTails.Proofs.AffineResidualQuerySafety

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch
open LongTails.Algorithms.AffineResidualBudget
open LongTails.Algorithms.CappedProximal
open AffineSoftmaxQuerySafety

lemma queriesWithin_mono {Q R U : Type*} (reply : Q → R) {a b : Q → Prop}
    (h : ∀ q, a q → b q) (p : Program Q R U) (hp : QueriesWithin reply a p) :
    QueriesWithin reply b p := by
  induction p with
  | done u => trivial
  | ask q rest ih => exact ⟨h q hp.1, ih (reply q) hp.2⟩

lemma regularizationSearchPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    {τ L r floor : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor)
    (cap : ℝ) (H b : ℕ) (seeds : ℕ → ProbeSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (regularizationSearchPlan m X state τ L r floor cap H b seeds) := by
  apply gridPlan_queries
  intro i μ
  let center := predictor (max floor μ) state
  let C := X ∩ Metric.closedBall center r
  have hμ := hf.trans_le (le_max_left floor μ)
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr.le⟩
  exact queriesWithin_mono reply (fun _ h => h.1) _
    (AffineResidualSearch.probePlan_queriesWithin m hCcompact hC center hcC hμ hτ hL hr (seeds i) b reply)

lemma finalStepPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L D ε : ℝ) {r μ : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (H : ℕ) (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (finalStepPlan m X state τ L r D ε μ H seed) := by
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr⟩
  apply queriesWithin_bind reply _ _ _ (cachePlan_queries m center reply hcenter)
  apply queriesWithin_bind reply _ _ _
    (queriesWithin_mono reply (fun _ h => h.1) _
      (AffineResidualExecution.localPlan_queriesWithin hCcompact ⟨center, hcC⟩ _ _ _ _ _ _ _ reply))
  apply queriesWithin_map
  exact queriesWithin_mono reply (fun _ h => h.1) _
    (AffineResidualMultilevel.cachedProxGradientPlan_queriesWithin C _ τ μ L r reply hCcompact ⟨center, hcC⟩ _ _ seed.2)

lemma outerStepPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (D ε : ℝ) {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (outerStepPlan m X state τ L r D ε floor cap H b seed) := by
  apply queriesWithin_bind reply _ _ _
    (regularizationSearchPlan_queries m hX hcompact state hA hx hv hτ hL hr hf cap H b seed.1 reply)
  have hμ : Program.eval reply (regularizationSearchPlan m X state τ L r floor cap H b seed.1) ∈ Set.Icc floor cap :=
    AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  exact finalStepPlan_queries m hX hcompact state hA hx hv τ L D ε hr.le (hf.trans_le hμ.1) H seed.2 reply

lemma outerRunPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (D ε : ℝ)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (hH : 0 < H) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (n : ℕ) :
    QueriesWithin reply (fun q => q.2 ∈ X) (outerRunPlan m X initial τ L r D ε floor cap H b seeds n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply queriesWithin_bind reply _ _ _ ih
    split_ifs
    · trivial
    · have hs := AffineResidualOuterExecution.outerRunPlan_feasible m hX hcompact initial hi D ε hτ hL hr hf hfc H b hH seeds reply n
      exact outerStepPlan_queries m hX hcompact _ hs.1 hs.2.1 hs.2.2 D ε hτ hL hr hf hfc H b (seeds n) reply

lemma budgetedOuterPlan_queries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (D ε : ℝ)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (hH : 0 < H) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    QueriesWithin reply (fun q => q.2 ∈ X) (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds) := by
  unfold budgetedOuterPlan
  split_ifs
  · exact queriesWithin_map reply _ _ _ (outerRunPlan_queries m hX hcompact initial hi D ε hτ hL hr hf hfc H b hH seeds reply N)
  · trivial


end LongTails.Proofs.AffineResidualQuerySafety
