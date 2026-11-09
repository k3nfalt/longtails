import LongTails.Proofs.AffineSoftmaxCostMoments

namespace LongTails.Proofs.AffineSoftmaxBudgetGuarantee

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget
open scoped ENNReal

lemma budgetedOuterPlan_failure_of_mean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L G r D ε floor cap : ℝ)
    (H b N J : ℕ) (reply : Fin m × E → ℝ × E) (bad : E → Prop)
    (P : ProbabilityMeasure (ℕ → OuterSeed)) {B : ℝ} (hB : 0 < B) {p : ℝ≥0∞}
    (hi : Integrable (fun seeds => (referenceRunCost m initial τ L G r floor H b N J seeds : ℝ)) (P : Measure _))
    (hmean : (∫ seeds, (referenceRunCost m initial τ L G r floor H b N J seeds : ℝ) ∂(P : Measure _)) ≤ B)
    (hactual : (P : Measure _) {seeds | bad (Program.eval reply
      (outerOutputPlan m X initial τ L G r D ε floor cap H b N seeds))} ≤ p) :
    (P : Measure _) {seeds | bad (Program.eval reply
      (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J (Nat.ceil (6 * B)) seeds))} ≤
      p + ENNReal.ofReal (1 / 6 : ℝ) := by
  let c := referenceRunCost m initial τ L G r floor H b N J
  have ht := AffineSoftmaxOuterProbability.nonnegative_tail P (fun seeds => (c seeds : ℝ)) hi
    (fun seeds => Nat.cast_nonneg (c seeds)) (show 0 < 6 * B by positivity) hmean
  have he : B / (6 * B) = (1 / 6 : ℝ) := by field_simp
  rw [he] at ht
  have hc : (P : Measure _) {seeds | ¬ c seeds ≤ Nat.ceil (6 * B)} ≤ ENNReal.ofReal (1 / 6 : ℝ) := by
    apply (measure_mono ?_).trans ht
    intro seeds hs
    have hh : Nat.ceil (6 * B) < c seeds := Nat.lt_of_not_ge hs
    have hhr : (Nat.ceil (6 * B) : ℝ) < c seeds := by exact_mod_cast hh
    exact (Nat.le_ceil (6 * B)).trans_lt hhr
  have hsub : {seeds | bad (Program.eval reply
      (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J (Nat.ceil (6 * B)) seeds))} ⊆
      {seeds | bad (Program.eval reply (outerOutputPlan m X initial τ L G r D ε floor cap H b N seeds))} ∪
        {seeds | ¬ c seeds ≤ Nat.ceil (6 * B)} := by
    intro seeds hs
    by_cases h : c seeds ≤ Nat.ceil (6 * B)
    · apply Or.inl
      simpa only [Set.mem_ofPred_eq, budgetedOuterPlan, show referenceRunCost m initial τ L G r floor H b N J seeds ≤ Nat.ceil (6 * B) from h, ite_true] using hs
    · exact Or.inr h
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hactual hc))

lemma budgetedOuterPlan_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) ∈ X := by
  unfold budgetedOuterPlan
  split_ifs
  · exact AffineSoftmaxOuterExecution.outerOutputPlan_mem m hX hcompact initial hi τ L G D ε hr hf hfc H b N seeds reply
  · exact hi

lemma budgetedOuterPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N J K : ℕ) (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (fun seeds => Program.eval reply (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds)) := by
  have ho := (AffineSoftmaxOuterExecution.outerRunPlan_param_measurable m hX hcompact initial hi
    τ L G D ε hr hf hfc H b reply hm (fun seeds : ℕ → OuterSeed => seeds) (fun j => measurable_pi_apply j) N).2.1
  have hc := AffineSoftmaxCostMoments.referenceRunCost_measurable m initial τ L G r floor H b N J
  have hs : MeasurableSet {seeds | referenceRunCost m initial τ L G r floor H b N J seeds ≤ K} :=
    measurableSet_le hc measurable_const
  have he seeds : Program.eval reply (budgetedOuterPlan m X initial τ L G r D ε floor cap H b N J K seeds) =
      if referenceRunCost m initial τ L G r floor H b N J seeds ≤ K then
        (Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b seeds N)).primal else initial := by
    unfold budgetedOuterPlan
    split_ifs <;> simp only [outerOutputPlan, Program.eval_map, Program.eval]
  simp_rw [he]
  exact Measurable.ite hs ho measurable_const

lemma computed_budgeted_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) {τ L G r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) (K : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (budgetedOuterPlan m X initial τ L G r D ε (compilerFloor G D r ε)
      (compilerCap G D r ε) (compilerDepth G D r ε) (compilerBoost G D r ε) (compilerHorizon G D r ε)
      (5 * compilerDepth G D r ε) K seeds) ≤ K := by
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hfc := (AffineSoftmaxOuterParameters.compiler_search_conditions hG hr hrD hε hsmall).1
  apply AffineSoftmaxOuterCost.budgetedOuterPlan_cost_le m X initial hτ hL hG hr hf hfc D ε _ _ _ _ K
    (lt_of_lt_of_le (by norm_num : 0 < 3) (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε))
  intro μ hμ
  exact AffineSoftmaxCostParameters.compiler_multilevel_depth hG hr hrD hε hsmall (hf.le.trans hμ.1) hμ.2

lemma computed_budgeted_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (initial xs : E) (hi : initial ∈ X) (hxs : xs ∈ X)
    (hmin : IsMinOn (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) X xs) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let H := compilerDepth G D r ε
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    let B := 50000000000000 * (H : ℝ) ^ 6 *
      ((m : ℝ) * compilerScale D r + D * Real.sqrt ((L + 2 * G ^ 2 / τ) / ε) + V * D ^ 2 / ε ^ 2)
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | ε < F (Program.eval reply (budgetedOuterPlan m X initial τ L G r D ε
        (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε)
        (compilerHorizon G D r ε) (5 * H) (Nat.ceil (6 * B)) seeds)) - F xs} ≤
      ENNReal.ofReal (23 / 60 : ℝ) := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let H := compilerDepth G D r ε
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  let B := 50000000000000 * (H : ℝ) ^ 6 *
    ((m : ℝ) * compilerScale D r + D * Real.sqrt ((L + 2 * G ^ 2 / τ) / ε) + V * D ^ 2 / ε ^ 2)
  let P : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num : 0 < 3)
    (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hHp
  have hD : 0 < D := hr.trans_le hrD
  have ht : 0 < compilerScale D r := zero_lt_one.trans_le (AffineSoftmaxOuterParameters.compilerScale_bounds hr hrD).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hB : 0 < B := by dsimp [B, V]; positivity
  have hcost := (AffineSoftmaxCostMoments.referenceRunCost_moments m initial τ L hG hr hf H
    (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) hHp).1
  have hmean := AffineSoftmaxCostMoments.referenceRunCost_bound m initial hτ hL hG hr hrD hε hsmall
  have hactual := AffineSoftmaxOuterGuarantee.outerRunPlan_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hlocal
    hdiam hc hg hlip hbound reply hm hreply initial xs hi hxs hmin
  have ha : (P : Measure _) {seeds | ε < F (Program.eval reply (outerOutputPlan m X initial τ L G r D ε
      (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε) (compilerHorizon G D r ε) seeds)) - F xs} ≤
      ENNReal.ofReal (13 / 60 : ℝ) := by
    simpa only [P, ProbabilityMeasure.coe_mk, F, H, outerOutputPlan, Program.eval_map] using hactual
  have hh := budgetedOuterPlan_failure_of_mean m X initial τ L G r D ε
    (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H)
    reply (fun z => ε < F z - F xs) P hB hcost hmean ha
  have hn : ENNReal.ofReal (13 / 60 : ℝ) + ENNReal.ofReal (1 / 6 : ℝ) = ENNReal.ofReal (23 / 60 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [hn] at hh
  simpa only [P, ProbabilityMeasure.coe_mk, F, H, B, V] using hh

end LongTails.Proofs.AffineSoftmaxBudgetGuarantee
