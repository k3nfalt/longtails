import LongTails.Proofs.AffineResidualCostParameters
import LongTails.Proofs.AffineSoftmaxCostParameters
import LongTails.Proofs.AffineResidualOuterGuarantee

namespace LongTails.Proofs.AffineResidualBudgetGuarantee

open MeasureTheory
open scoped ENNReal
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualBudget
open LongTails.Algorithms.AffineSoftmaxOuter (compilerFloor compilerCap compilerDepth compilerBoost compilerHorizon compilerScale)
open AffineResidualCostParameters

lemma budgetedOuterPlan_failure_of_mean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L r D ε floor cap : ℝ)
    (H b N J : ℕ) (reply : Fin m × E → ℝ × E) (bad : E → Prop)
    (P : ProbabilityMeasure (ℕ → OuterSeed)) {B : ℝ} (hB : 0 < B) {p : ℝ≥0∞}
    (hi : Integrable (fun seeds => (referenceRunCost m τ L r floor H b N J seeds : ℝ)) (P : Measure _))
    (hmean : (∫ seeds, (referenceRunCost m τ L r floor H b N J seeds : ℝ) ∂(P : Measure _)) ≤ B)
    (hactual : (P : Measure _) {seeds | bad (Program.eval reply
      (outerOutputPlan m X initial τ L r D ε floor cap H b N seeds))} ≤ p) :
    (P : Measure _) {seeds | bad (Program.eval reply
      (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J (Nat.ceil (12 * B)) seeds))} ≤
      p + ENNReal.ofReal (1 / 12 : ℝ) := by
  let c := referenceRunCost m τ L r floor H b N J
  have ht := AffineSoftmaxOuterProbability.nonnegative_tail P (fun seeds => (c seeds : ℝ)) hi
    (fun seeds => Nat.cast_nonneg (c seeds)) (show 0 < 12 * B by positivity) hmean
  have he : B / (12 * B) = (1 / 12 : ℝ) := by field_simp
  rw [he] at ht
  have hc : (P : Measure _) {seeds | ¬ c seeds ≤ Nat.ceil (12 * B)} ≤ ENNReal.ofReal (1 / 12 : ℝ) := by
    apply (measure_mono ?_).trans ht
    intro seeds hs
    have hh : Nat.ceil (12 * B) < c seeds := Nat.lt_of_not_ge hs
    have hhr : (Nat.ceil (12 * B) : ℝ) < c seeds := by exact_mod_cast hh
    exact (Nat.le_ceil (12 * B)).trans_lt hhr
  have hsub : {seeds | bad (Program.eval reply
      (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J (Nat.ceil (12 * B)) seeds))} ⊆
      {seeds | bad (Program.eval reply (outerOutputPlan m X initial τ L r D ε floor cap H b N seeds))} ∪
        {seeds | ¬ c seeds ≤ Nat.ceil (12 * B)} := by
    intro seeds hs
    by_cases h : c seeds ≤ Nat.ceil (12 * B)
    · apply Or.inl
      simpa only [Set.mem_ofPred_eq, budgetedOuterPlan, show referenceRunCost m τ L r floor H b N J seeds ≤ Nat.ceil (12 * B) from h, ite_true] using hs
    · exact Or.inr h
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hactual hc))

lemma referenceRunCost_measurable (m : ℕ) (τ L r floor : ℝ) (H b N J : ℕ) :
    Measurable (referenceRunCost m τ L r floor H b N J) := by
  unfold referenceRunCost
  apply Finset.measurable_sum
  intro k hk
  let g := fun n : ℕ => (2 * H + 9) * referenceProbeCost m τ L r floor b +
    m + 2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ floor L r
      (floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)) +
    (2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ floor L r
      (floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) +
      if n + 1 ≤ J then
        2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ floor L r
          ((floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) / 2 ^ (n + 1)) +
        2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ floor L r
          ((floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) / 2 ^ n) else 0)
  have hg : Measurable g := measurable_of_countable g
  convert hg.comp ((show Measurable (fun seeds : ℕ → OuterSeed => seeds k) from measurable_pi_apply k).snd.snd.fst) using 1
  funext seeds
  simp only [g, Function.comp_apply, referenceOuterCost, referenceFinalCost, referenceMultilevelCost]
  omega

lemma budgetedOuterPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (initial : E) (τ L r D ε floor cap : ℝ) (H b N J K : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds => Program.eval reply
      (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds)) := by
  have ho := (AffineResidualOuterExecution.outerRunPlan_measurable m hX hcompact hne initial
    τ L r D ε floor cap H b N reply).2.1
  have hc := referenceRunCost_measurable m τ L r floor H b N J
  have hs : MeasurableSet {seeds | referenceRunCost m τ L r floor H b N J seeds ≤ K} :=
    measurableSet_le hc measurable_const
  have he seeds : Program.eval reply (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds) =
      if referenceRunCost m τ L r floor H b N J seeds ≤ K then
        (Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds N)).primal else initial := by
    unfold budgetedOuterPlan
    split_ifs <;> simp only [outerOutputPlan, Program.eval_map, Program.eval]
  simp_rw [he]
  exact Measurable.ite hs ho measurable_const

lemma budgetedOuterPlan_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L r D ε floor cap : ℝ)
    (H b N J K : ℕ) (reply : Fin m × E → ℝ × E) :
    (Set.range (fun seeds => Program.eval reply
      (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds))).Finite := by
  have hf := (AffineResidualOuterExecution.outerRunPlan_finite_range m X initial
    τ L r D ε floor cap H b N reply).image (fun state => state.primal)
  apply (hf.union (Set.finite_singleton initial)).subset
  rintro _ ⟨seeds, rfl⟩
  dsimp only
  unfold budgetedOuterPlan
  split_ifs
  · apply Or.inl
    simp only [outerOutputPlan, Program.eval_map]
    exact ⟨_, ⟨seeds, rfl⟩, rfl⟩
  · exact Or.inr rfl

lemma budgetedOuterPlan_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (D ε : ℝ)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (hH : 0 < H) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (budgetedOuterPlan m X initial τ L r D ε floor cap H b N J K seeds) ∈ X := by
  unfold budgetedOuterPlan
  split_ifs
  · simpa only [outerOutputPlan, Program.eval_map] using (AffineResidualOuterExecution.outerRunPlan_feasible m hX hcompact initial hi D ε
      hτ hL hr hf hfc H b hH seeds reply N).2.1
  · exact hi

lemma computed_budgeted_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) {τ L r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) (K : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (budgetedOuterPlan m X initial τ L r D ε (compilerFloor G D r ε)
      (compilerCap G D r ε) (compilerDepth G D r ε) (compilerBoost G D r ε) (compilerHorizon G D r ε)
      (5 * compilerDepth G D r ε) K seeds) ≤ K := by
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hfc := (AffineSoftmaxOuterParameters.compiler_search_conditions hG hr hrD hε hsmall).1
  apply AffineResidualOuterCost.budgetedOuterPlan_cost_le m X initial hτ hL hr hf hfc D ε _ _ _ _ K
    (lt_of_lt_of_le (by norm_num : 0 < 3) (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε))
  intro μ hμ
  exact AffineSoftmaxCostParameters.compiler_multilevel_depth hG hr hrD hε hsmall (hf.le.trans hμ.1) hμ.2

lemma computed_budgeted_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L r D ε : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (initial xs : E) (hi : initial ∈ X) (hxs : xs ∈ X)
    (hmin : IsMinOn (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) X xs) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let H := compilerDepth G D r ε
    let B := 30000000000000 * (H : ℝ) ^ 7 * compilerScale D r *
      (m + localWork m τ (compilerFloor G D r ε) L r)
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | ε < F (Program.eval reply (budgetedOuterPlan m X initial τ L r D ε
        (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε)
        (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) seeds)) - F xs} ≤
      ENNReal.ofReal (3 / 10 : ℝ) := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let H := compilerDepth G D r ε
  let B := 30000000000000 * (H : ℝ) ^ 7 * compilerScale D r *
    (m + localWork m τ (compilerFloor G D r ε) L r)
  let P : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num : 0 < 3)
    (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hHp
  have hD : 0 < D := hr.trans_le hrD
  have ht : 0 < compilerScale D r := zero_lt_one.trans_le (AffineSoftmaxOuterParameters.compilerScale_bounds hr hrD).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hw := localWork_nonneg m hτ hf hL (r := r)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcost := (AffineResidualCostMoments.referenceRunCost_moments m hτ hL hr hf H
    (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) hHp).1
  have hmean := computed_reference_mean m hτ hL hr hrD hε hsmall
  have hactual := AffineResidualOuterGuarantee.outerRunPlan_failure m hX hcompact f hτ hL hG hr hrD hε hsmall
    hdiam hc hg hlip hbound reply hreply initial xs hi hxs hmin
  have ha : (P : Measure _) {seeds | ε < F (Program.eval reply (outerOutputPlan m X initial τ L r D ε
      (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε) (compilerHorizon G D r ε) seeds)) - F xs} ≤
      ENNReal.ofReal (13 / 60 : ℝ) := by
    simpa only [P, ProbabilityMeasure.coe_mk, F, H, outerOutputPlan, Program.eval_map] using hactual
  have hh := budgetedOuterPlan_failure_of_mean m X initial τ L r D ε
    (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H)
    reply (fun z => ε < F z - F xs) P hB hcost hmean ha
  have hn : ENNReal.ofReal (13 / 60 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) = ENNReal.ofReal (3 / 10 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [hn] at hh
  simpa only [P, ProbabilityMeasure.coe_mk, F, H, B] using hh

end LongTails.Proofs.AffineResidualBudgetGuarantee
