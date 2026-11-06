import LongTails.Algorithms.AffineSoftmaxBudget
import LongTails.Proofs.AffineSoftmaxOuterGuarantee
import LongTails.Proofs.AffineSoftmaxSearchCost

namespace LongTails.Proofs.AffineSoftmaxOuterCost

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget

lemma gradient_reference_tolerance {μ floor r H : ℝ} {j J : ℕ}
    (hf : 0 < floor) (hμ : floor ≤ μ) (hr : 0 < r) (hH : 0 < H) (hj : j ≤ J) :
    floor * r ^ 2 / (2 * 100000 * H ^ 3 * (2 + 12 * (J : ℝ))) ≤
      (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * H ^ 3))) ^ 2 / (2 * μ * (2 + 12 * (j : ℝ))) := by
  have hμpos := hf.trans_le hμ
  rw [Real.sq_sqrt (by positivity)]
  have he : (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / (2 * μ * (2 + 12 * (j : ℝ))) =
      μ * r ^ 2 / (2 * 100000 * H ^ 3 * (2 + 12 * (j : ℝ))) := by field_simp
  rw [he]
  apply div_le_div₀ (by positivity)
  · exact mul_le_mul_of_nonneg_right hμ (sq_nonneg r)
  · positivity
  · have hjr : (j : ℝ) ≤ J := by exact_mod_cast hj
    gcongr

lemma budgetedOuterPlan_cost_of_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L G r D ε floor cap : ℝ)
    (H b N J K : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E)
    (hcost : Program.cost reply (outerOutputPlan m X initial τ L G r D ε floor cap H b N seeds) ≤
      referenceRunCost m initial τ L G r floor H b N J seeds) :
    Program.cost reply (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) ≤ K := by
  unfold budgetedOuterPlan
  split_ifs with h
  · exact hcost.trans h
  · exact Nat.zero_le _

lemma finalStepPlan_cost_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : LongTails.Algorithms.CappedProximal.State E) (initial : E)
    {τ L G r floor μ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfm : floor ≤ μ) (D ε : ℝ) (H J : ℕ) (hH : 0 < H)
    (hJ : LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (finalStepPlan m X state τ L G r D ε μ H seed) ≤
      referenceFinalCost m initial τ L G r floor H J seed := by
  let center := LongTails.Algorithms.CappedProximal.predictor μ state
  let project := OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall center r)
  let s := Program.eval reply (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m center)
  let t : Snapshot (Fin m) E := ⟨initial, (fun _ => 0), (fun _ => 0)⟩
  let otherReply := fun _ : Fin m × E => ((0 : ℝ), (0 : E))
  let otherProject := fun _ : E => initial
  let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
  let β := ε / (1000 * D)
  let j := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hμ : 0 < μ := hf.trans_le hfm
  have hsqrt : σ ^ 2 = μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3) := Real.sq_sqrt (by positivity)
  have hj : j ≤ J := by simpa only [j, hsqrt, β] using hJ
  have hp := AffineSoftmaxMultilevelCost.cachedProxPlan_cost_domination s t hτ hL hG hr hf hfm
    (show 0 < floor * r ^ 2 / (100000 * (H : ℝ) ^ 3) by positivity)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfm (sq_nonneg r)) (by positivity : 0 ≤ 100000 * (H : ℝ) ^ 3))
    project otherProject reply otherReply seed.1
  have hg := AffineSoftmaxMultilevelCost.multilevelPlan_cost_domination s t hτ hL hG hr hf hfm
    (show 0 < floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ))) by positivity)
    (gradient_reference_tolerance hf hfm hr hHr hj) project otherProject reply otherReply hj seed.2
  change Program.cost reply (finalStepPlan m X state τ L G r D ε μ H seed) ≤
    m + Program.cost otherReply (cachedProxPlan t τ L G r floor
      (floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)) otherProject seed.1) +
      Program.cost otherReply (multilevelPlan t τ L G r floor
        (floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) otherProject J seed.2)
  simp only [finalStepPlan, Program.cost_bind, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost]
  change m + (Program.cost reply (cachedProxPlan s τ L G r μ (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) project seed.1) +
    Program.cost reply (cachedProxGradientPlan s τ L G r μ σ β project seed.2)) ≤ _
  simp only [cachedProxGradientPlan, Program.cost_map]
  exact Nat.add_le_add_left (Nat.add_le_add hp hg) m |>.trans_eq (Nat.add_assoc _ _ _).symm

lemma outerStepPlan_cost_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : LongTails.Algorithms.CappedProximal.State E) (initial : E)
    {τ L G r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b J : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (outerStepPlan m X state τ L G r D ε floor cap H b seed) ≤
      referenceOuterCost m initial τ L G r floor H b J seed := by
  let μ := Program.eval reply (LongTails.Algorithms.AffineSoftmaxSearch.regularizationSearchPlan
    m X state τ L G r floor cap H b seed.1)
  have hμ : μ ∈ Set.Icc floor cap := by
    dsimp only [μ, LongTails.Algorithms.AffineSoftmaxSearch.regularizationSearchPlan]
    exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  have hs := AffineSoftmaxSearchCost.regularizationSearchPlan_cost_domination m X state initial
    hτ hL hG hr hf hfc H b seed.1 (fun _ => initial) reply (fun _ => (0, 0))
  have ht := finalStepPlan_cost_domination m X state initial hτ hL hG hr hf hμ.1 D ε H J hH
    (hJ μ hμ) seed.2 reply
  simpa only [outerStepPlan, Program.cost_bind, referenceOuterCost, μ] using Nat.add_le_add hs ht

lemma outerRunPlan_cost_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    {τ L G r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b J : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (N : ℕ) :
    Program.cost reply (outerRunPlan m X initial τ L G r D ε floor cap H b seeds N) ≤
      referenceRunCost m initial τ L G r floor H b N J seeds := by
  induction N with
  | zero => simp [outerRunPlan, Program.cost, referenceRunCost]
  | succ n ih =>
    rw [outerRunPlan, Program.cost_bind]
    unfold referenceRunCost at ih ⊢
    rw [Finset.sum_range_succ]
    apply Nat.add_le_add ih
    split_ifs
    · exact Nat.zero_le _
    · exact outerStepPlan_cost_domination m X _ initial hτ hL hG hr hf hfc D ε H b J hH hJ (seeds n) reply

lemma budgetedOuterPlan_cost_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    {τ L G r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b N J K : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) ≤ K := by
  apply budgetedOuterPlan_cost_of_domination
  simpa only [outerOutputPlan, Program.cost_map] using
    outerRunPlan_cost_domination m X initial hτ hL hG hr hf hfc D ε H b J hH hJ seeds reply N

end LongTails.Proofs.AffineSoftmaxOuterCost
