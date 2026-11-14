import LongTails.Proofs.AffineResidualOuterExecution
import LongTails.Proofs.AffineResidualCost
import LongTails.Algorithms.AffineResidualBudget
import LongTails.Proofs.AffineSoftmaxSearchCost

namespace LongTails.Proofs.AffineResidualOuterCost

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineResidualSaddle (localSteps)
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot)
open LongTails.Algorithms.CappedProximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma finalStepPlan_cost (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L r D ε μ : ℝ) (H : ℕ) (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    let center := predictor μ state
    let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
    Program.cost reply (finalStepPlan m X state τ L r D ε μ H seed) =
      m + 2 * localSteps m τ μ L r (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) +
        Program.cost reply (cachedProxGradientPlan (X ∩ Metric.closedBall center r) s τ μ L r
          (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D)) seed.2) := by
  simp only [finalStepPlan, Program.cost_bind, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost,
    AffineSoftmaxExecution.cachePlan_eval, AffineResidualExecution.localPlan_cost, Fintype.card_fin]
  omega

lemma finalStepPlan_cost_bound (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    {τ L r μ : ℝ} (D ε : ℝ) (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hμ : 0 < μ)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) :
    let φ := μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)
    let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
    let β := ε / (1000 * D)
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
    Integrable (fun seed => (Program.cost reply (finalStepPlan m X state τ L r D ε μ H seed) : ℝ))
      (finalLaw : Measure FinalSeed) ∧
    (∫ seed, (Program.cost reply (finalStepPlan m X state τ L r D ε μ H seed) : ℝ)
      ∂(finalLaw : Measure FinalSeed)) ≤
      m + 2 * localSteps m τ μ L r φ + (2 + 3 * (J : ℝ)) * localSteps m τ μ L r δ := by
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
  let β := ε / (1000 * D)
  let φ := μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hg := AffineResidualCost.cachedProxGradientPlan_cost_bound C s (r := r) β hτ hμ hL hσ reply
  let c := fun seed : MultilevelSeed => (Program.cost reply (cachedProxGradientPlan C s τ μ L r σ β seed) : ℝ)
  have hgi : Integrable c (multilevelLaw : Measure MultilevelSeed) := hg.1
  have he (seed : FinalSeed) : (Program.cost reply (finalStepPlan m X state τ L r D ε μ H seed) : ℝ) =
      (m : ℝ) + 2 * localSteps m τ μ L r φ + c seed.2 := by
    rw [finalStepPlan_cost]
    push_cast
    rfl
  dsimp only
  simp_rw [he]
  have hi := (integrable_const ((m : ℝ) + 2 * localSteps m τ μ L r φ)).add
    (hgi.comp_snd (localLaw : Measure LocalSeed))
  refine ⟨hi, ?_⟩
  simp only [finalLaw, ProbabilityMeasure.coe_mk]
  rw [integral_add (integrable_const _) (hgi.comp_snd (localLaw : Measure LocalSeed)),
    integral_const, probReal_univ, smul_eq_mul, one_mul]
  change _ + (∫ seed : FinalSeed, c seed.2
    ∂(localLaw : Measure LocalSeed).prod (multilevelLaw : Measure MultilevelSeed)) ≤ _
  rw [integral_fun_snd c, probReal_univ, one_smul]
  simpa only [Fintype.card_fin] using add_le_add (le_refl ((m : ℝ) + 2 * localSteps m τ μ L r φ)) hg.2

open LongTails.Algorithms.AffineResidualBudget

lemma referenceMultilevelCost_mono (m : ℕ) [NeZero m] {τ μ floor L r q q₀ : ℝ}
    (hτ : 0 < τ) (hf : 0 < floor) (hμ : floor ≤ μ) (hL : 0 ≤ L)
    (hq : 0 < q₀) (hqq : q₀ ≤ q) {j J : ℕ} (hj : j ≤ J) (seed : MultilevelSeed) :
    referenceMultilevelCost m τ μ L r (μ * q) j seed ≤
      referenceMultilevelCost m τ floor L r (floor * q₀) J seed := by
  have hn := AffineResidualCost.localSteps_scaled_mono m (r := r) hτ hf hμ hL hq hqq
  have hlevel n : localSteps m τ μ L r (μ * q / 2 ^ n) ≤
      localSteps m τ floor L r (floor * q₀ / 2 ^ n) := by
    have hh := AffineResidualCost.localSteps_scaled_mono m (r := r) hτ hf hμ hL
      (show 0 < q₀ / 2 ^ n by positivity)
      (div_le_div_of_nonneg_right hqq (by positivity : 0 ≤ (2 : ℝ) ^ n))
    simpa only [mul_div_assoc] using hh
  have h₁ := hlevel (seed.1 + 1)
  have h₂ := hlevel seed.1
  unfold referenceMultilevelCost
  split_ifs <;> omega

lemma finalStepPlan_cost_domination (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    {τ L r floor μ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : 0 < floor) (hfm : floor ≤ μ) (D ε : ℝ) (H J : ℕ) (hH : 0 < H)
    (hJ : LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (finalStepPlan m X state τ L r D ε μ H seed) ≤
      referenceFinalCost m τ L r floor H J seed := by
  let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
  let β := ε / (1000 * D)
  let j := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let q := fun k : ℕ => r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (k : ℝ)))
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hμ : 0 < μ := hf.trans_le hfm
  have hsqrt : σ ^ 2 = μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3) := Real.sq_sqrt (by positivity)
  have hj : j ≤ J := by simpa only [j, hsqrt, β] using hJ
  have hqpos k : 0 < q k := by dsimp [q]; positivity
  have hqle : q J ≤ q j := by
    dsimp [q]
    have hjr : (j : ℝ) ≤ J := by exact_mod_cast hj
    gcongr
  have hδ : σ ^ 2 / (2 * μ * (2 + 12 * (j : ℝ))) = μ * q j := by
    rw [hsqrt]
    dsimp [q]
    field_simp
  have hp := AffineResidualCost.localSteps_scaled_mono m (r := r) hτ hf hfm hL
    (show 0 < r ^ 2 / (100000 * (H : ℝ) ^ 3) by positivity) le_rfl
  simp only [← mul_div_assoc] at hp
  have hg := referenceMultilevelCost_mono m (r := r) hτ hf hfm hL (hqpos J) hqle hj seed.2
  rw [finalStepPlan_cost]
  simp only [cachedProxGradientPlan, Program.cost_map, AffineResidualMultilevel.multilevelPlan_cost,
    Fintype.card_fin]
  change m + 2 * localSteps m τ μ L r (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) +
    referenceMultilevelCost m τ μ L r (σ ^ 2 / (2 * μ * (2 + 12 * (j : ℝ)))) j seed.2 ≤ _
  rw [hδ]
  convert Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hp) m) hg using 1
  simp only [referenceFinalCost, q, mul_div_assoc]


open LongTails.Algorithms.AffineResidualSearch

lemma regularizationSearchPlan_cost_domination (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ) (seeds : ℕ → ProbeSeed)
    (reply : Fin m × E → ℝ × E) :
    Program.cost reply (regularizationSearchPlan m X state τ L r floor cap H b seeds) ≤
      (2 * H + 9) * referenceProbeCost m τ L r floor b := by
  unfold regularizationSearchPlan
  have hbound := AffineSoftmaxSearchCost.searchPlan_cost_le_sum
    (fun i μ => probePlan m (X ∩ Metric.closedBall (predictor (max floor μ) state) r)
      (predictor (max floor μ) state) τ (max floor μ) L r (seeds i) b)
    reply r (hf.le.trans hfc) hfc (fun _ => referenceProbeCost m τ L r floor b) H
  apply (hbound ?_).trans_eq (by simp)
  intro i _ μ _
  rw [AffineResidualSearch.probePlan_cost_exact]
  have hn := AffineResidualCost.localSteps_scaled_mono m (r := r) hτ hf (le_max_left floor μ) hL
    (show 0 < r ^ 2 / 32768 by positivity) le_rfl
  simp only [← mul_div_assoc] at hn
  exact Nat.add_le_add_left (Nat.mul_le_mul_left b (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hn) m)) m

lemma outerStepPlan_cost_domination (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b J : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (outerStepPlan m X state τ L r D ε floor cap H b seed) ≤
      referenceOuterCost m τ L r floor H b J seed := by
  let μ := Program.eval reply (regularizationSearchPlan m X state τ L r floor cap H b seed.1)
  have hμ : μ ∈ Set.Icc floor cap := by
    dsimp only [μ, regularizationSearchPlan]
    exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  have hs := regularizationSearchPlan_cost_domination m X state hτ hL hr hf hfc H b seed.1 reply
  have ht := finalStepPlan_cost_domination m X state hτ hL hr hf hμ.1 D ε H J hH (hJ μ hμ) seed.2 reply
  simpa only [outerStepPlan, Program.cost_bind, referenceOuterCost, μ] using Nat.add_le_add hs ht

lemma outerRunPlan_cost_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b J : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (N : ℕ) :
    Program.cost reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds N) ≤
      referenceRunCost m τ L r floor H b N J seeds := by
  induction N with
  | zero => simp [outerRunPlan, Program.cost, referenceRunCost]
  | succ n ih =>
    rw [outerRunPlan, Program.cost_bind]
    unfold referenceRunCost at ih ⊢
    rw [Finset.sum_range_succ]
    apply Nat.add_le_add ih
    split_ifs
    · exact Nat.zero_le _
    · exact outerStepPlan_cost_domination m X _ hτ hL hr hf hfc D ε H b J hH hJ (seeds n) reply

lemma budgetedOuterPlan_cost_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (D ε : ℝ) (H b N J K : ℕ) (hH : 0 < H)
    (hJ : ∀ μ ∈ Set.Icc floor cap, LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
      (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) ((ε / (1000 * D)) ^ 2) ≤ J)
    (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds) ≤ K := by
  unfold budgetedOuterPlan
  split_ifs with h
  · have hc := outerRunPlan_cost_domination m X initial hτ hL hr hf hfc D ε H b J hH hJ seeds reply N
    apply le_trans _ h
    simpa only [outerOutputPlan, Program.cost_map] using hc
  · exact Nat.zero_le _

end LongTails.Proofs.AffineResidualOuterCost
