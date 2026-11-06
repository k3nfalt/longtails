import LongTails.Algorithms.AffineSoftmaxAmplification
import LongTails.Proofs.AffineSoftmaxBudgetGuarantee

namespace LongTails.Proofs.AffineSoftmaxAmplification

open MeasureTheory
open scoped ENNReal
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxAmplification
open LongTails.Algorithms.AffineSoftmaxSearch

lemma maximumValue_le_smoothValue {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    maximumValue v ≤ LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ v := by
  apply csSup_le (Set.range_nonempty v)
  rintro _ ⟨i, rfl⟩
  exact SmoothFiniteMaximumGeometry.smoothValue_lower v hτ i

lemma smoothValue_le_maximumValue {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ v ≤ maximumValue v + τ * Real.log (Fintype.card ι) := by
  apply SmoothFiniteMaximumGeometry.smoothValue_upper v hτ
  intro i
  exact le_csSup (Set.finite_range v).bddAbove (Set.mem_range_self i)

lemma maximum_gap_le_smooth_gap {ι E : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) {τ : ℝ} (hτ : 0 < τ) (x xs xstar : E)
    (hmin : LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xs) ≤
      LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xstar)) :
    maximumValue (fun i => f i x) - maximumValue (fun i => f i xstar) ≤
      LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i x) -
        LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xs) + τ * Real.log (Fintype.card ι) := by
  have hl := maximumValue_le_smoothValue (fun i => f i x) hτ
  have hu := smoothValue_le_maximumValue (fun i => f i xstar) hτ
  linarith

lemma maximumScorePlan_eval {E : Type*}
    (m : ℕ) (x : E) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (maximumScorePlan m x) = maximumValue (fun i => (reply (i, x)).1) := by
  simp only [maximumScorePlan, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]

lemma maximumScorePlan_cost {E : Type*}
    (m : ℕ) (x : E) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (maximumScorePlan m x) = m := by
  simp only [maximumScorePlan, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost]

lemma scoredPlan_cost {E : Type*}
    (m : ℕ) (trial : Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (scoredPlan m trial) = Program.cost reply trial + m := by
  simp only [scoredPlan, Program.cost_bind, Program.cost_map, maximumScorePlan_cost]

lemma repeatedPlan_cost_le {E : Type*}
    (m : ℕ) (trial : ℕ → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E)
    (n K : ℕ) (hc : ∀ j ≤ n, Program.cost reply (trial j) ≤ K) :
    Program.cost reply (repeatedPlan m trial n) ≤ (n + 1) * (K + m) := by
  simp only [repeatedPlan, Program.cost_bind, Program.cost_map, AffineSoftmaxSearch.selectTrialsPlan_cost, scoredPlan_cost]
  have hsum : (∑ j ∈ Finset.range n, (Program.cost reply (trial (j + 1)) + m)) ≤ n * (K + m) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, (K + m) := Finset.sum_le_sum (fun j hj => Nat.add_le_add_right (hc (j + 1) (by have := Finset.mem_range.mp hj; omega)) m)
      _ = _ := by simp
  have hh := Nat.add_le_add (Nat.add_le_add_right (hc 0 (Nat.zero_le n)) m) hsum
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using hh

lemma scoredPlan_eval {E : Type*}
    (m : ℕ) (trial : Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (scoredPlan m trial) =
      (Program.eval reply trial, maximumValue (fun i => (reply (i, Program.eval reply trial)).1)) := by
  simp only [scoredPlan, Program.eval_bind, Program.eval_map, maximumScorePlan_eval]

lemma repeatedPlan_mem {E : Type*}
    (m : ℕ) (trial : ℕ → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E)
    (n : ℕ) (X : Set E) (ht : ∀ j, Program.eval reply (trial j) ∈ X) :
    Program.eval reply (repeatedPlan m trial n) ∈ X := by
  simp only [repeatedPlan, Program.eval_bind, Program.eval_map]
  apply AffineSoftmaxSearch.selectTrialsPlan_eval_property _ _ reply (fun z => z.1 ∈ X)
  · simpa only [scoredPlan_eval] using ht 0
  · intro j
    simpa only [scoredPlan_eval] using ht (j + 1)

lemma repeatedPlan_score_le {E : Type*}
    (m : ℕ) (trial : ℕ → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E)
    (n j : ℕ) (hj : j ≤ n) :
    maximumValue (fun i => (reply (i, Program.eval reply (repeatedPlan m trial n))).1) ≤
      maximumValue (fun i => (reply (i, Program.eval reply (trial j))).1) := by
  let score := fun x => maximumValue (fun i => (reply (i, x)).1)
  let start := Program.eval reply (scoredPlan m (trial 0))
  let next := fun k => scoredPlan m (trial (k + 1))
  have he : (Program.eval reply (selectTrialsPlan next start n)).2 =
      score (Program.eval reply (selectTrialsPlan next start n)).1 := by
    apply AffineSoftmaxSearch.selectTrialsPlan_eval_property next start reply (fun z => z.2 = score z.1)
    · simp only [start, scoredPlan_eval, score]
    · intro k
      simp only [next, scoredPlan_eval, score]
  simp only [repeatedPlan, Program.eval_bind, Program.eval_map]
  change score (Program.eval reply (selectTrialsPlan next start n)).1 ≤ score (Program.eval reply (trial j))
  rw [← he]
  by_cases hz : j = 0
  · subst j
    simpa only [start, scoredPlan_eval, score] using
      AffineSoftmaxSearch.selectTrialsPlan_score_le_initial next start reply n
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hz
    have hindex : j - 1 < n := by omega
    have heq : j - 1 + 1 = j := by omega
    simpa only [next, scoredPlan_eval, score, heq] using
      AffineSoftmaxSearch.selectTrialsPlan_score_le_trial next start reply n (j - 1) hindex

lemma maximumScorePlan_measurable {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    (m : ℕ) (x : Z → E) (hx : Measurable x) (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (fun z => Program.eval reply (maximumScorePlan m (x z))) := by
  simp only [maximumScorePlan_eval]
  change Measurable (fun z => ⨆ i, (reply (i, x z)).1)
  exact Measurable.iSup (fun i => (hm.comp (measurable_const.prodMk hx)).fst)

lemma scoredPlan_measurable {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    (m : ℕ) (trial : Z → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E)
    (hm : Measurable reply) (ht : Measurable (fun z => Program.eval reply (trial z))) :
    Measurable (fun z => Program.eval reply (scoredPlan m (trial z))) := by
  have hs := maximumScorePlan_measurable m _ ht reply hm
  simpa only [scoredPlan, Program.eval_bind, Program.eval_map] using ht.prodMk hs

lemma repeatedPlan_measurable {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    (m : ℕ) (trial : Z → ℕ → Program (Fin m × E) (ℝ × E) E) (reply : Fin m × E → ℝ × E)
    (hm : Measurable reply) (ht : ∀ j, Measurable (fun z => Program.eval reply (trial z j))) (n : ℕ) :
    Measurable (fun z => Program.eval reply (repeatedPlan m (trial z) n)) := by
  have hs := AffineSoftmaxSearch.selectTrialsPlan_measurable
    (fun z j => scoredPlan m (trial z (j + 1)))
    (fun z => Program.eval reply (scoredPlan m (trial z 0))) reply
    (scoredPlan_measurable m _ reply hm (ht 0))
    (fun j => scoredPlan_measurable m _ reply hm (ht (j + 1))) n
  simpa only [repeatedPlan, Program.eval_bind, Program.eval_map] using hs.fst

lemma smoothed_to_maximum_failure {ι E Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (P : Measure Ω) (f : ι → E → ℝ) {τ ε : ℝ} (hτ : 0 < τ) (xs xstar : E) (out : Ω → E)
    (hmin : LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xs) ≤
      LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xstar)) {p : ℝ≥0∞}
    (hp : P {ω | ε < LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i (out ω)) -
      LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i xs)} ≤ p) :
    P {ω | ε + τ * Real.log (Fintype.card ι) <
      maximumValue (fun i => f i (out ω)) - maximumValue (fun i => f i xstar)} ≤ p := by
  apply (measure_mono ?_).trans hp
  intro ω hω
  have hh := maximum_gap_le_smooth_gap f hτ (out ω) xs xstar hmin
  dsimp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

lemma repeatedPlan_failure {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) (trial : Ω → Program (Fin m × E) (ℝ × E) E)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (ht : Measurable (fun ω => Program.eval reply (trial ω))) (n : ℕ) (baseline ε : ℝ) (p : ℝ≥0∞)
    (hp : (P : Measure Ω) {ω | ε < maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline} ≤ p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {seeds | ε < maximumValue (fun i => (reply (i, Program.eval reply (repeatedPlan m (fun j => trial (seeds j)) n))).1) - baseline} ≤
      p ^ (n + 1) := by
  let score := fun ω => maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline
  have hs : Measurable score := by
    have hh := (maximumScorePlan_measurable m _ ht reply hm).sub_const baseline
    simpa only [maximumScorePlan_eval] using hh
  apply AffineSoftmaxSearch.independent_selection_failure P score hs _ (n + 1) ε p
  · intro seeds j hj
    exact sub_le_sub_right (repeatedPlan_score_le m (fun j => trial (seeds j)) reply n j (by omega)) baseline
  · exact hp

lemma maximum_reply_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (f : Fin m → E → ℝ) (reply : Fin m × E → ℝ × E) {X : Set E}
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x)) (x : E) (hx : x ∈ X) :
    maximumValue (fun i => (reply (i, x)).1) = maximumValue (fun i => f i x) := by
  congr 1
  funext i
  rw [hreply i x hx]

lemma repeatedPlan_original_failure {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) (f : Fin m → E → ℝ) (trial : Ω → Program (Fin m × E) (ℝ × E) E)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) {X : Set E}
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (ht : Measurable (fun ω => Program.eval reply (trial ω))) (hx : ∀ ω, Program.eval reply (trial ω) ∈ X)
    (n : ℕ) (baseline ε : ℝ) (p : ℝ≥0∞)
    (hp : (P : Measure Ω) {ω | ε < maximumValue (fun i => f i (Program.eval reply (trial ω))) - baseline} ≤ p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {seeds | ε < maximumValue (fun i => f i (Program.eval reply (repeatedPlan m (fun j => trial (seeds j)) n))) - baseline} ≤
      p ^ (n + 1) := by
  have he ω := maximum_reply_eq m f reply hreply _ (hx ω)
  have hprob : (P : Measure Ω) {ω | ε < maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline} ≤ p := by
    simpa only [he] using hp
  have hh := repeatedPlan_failure P m trial reply hm ht n baseline ε p hprob
  have hout (seeds : ℕ → Ω) := maximum_reply_eq m f reply hreply _
    (repeatedPlan_mem m (fun j => trial (seeds j)) reply n X (fun j => hx (seeds j)))
  simpa only [hout] using hh

lemma amplifiedOuterPlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) {τ L G r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) (K : ℕ)
    (seeds : ℕ → ℕ → LongTails.Algorithms.AffineSoftmaxOuter.OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (amplifiedOuterPlan m X initial τ L G r D ε
      (LongTails.Algorithms.AffineSoftmaxOuter.compilerFloor G D r ε)
      (LongTails.Algorithms.AffineSoftmaxOuter.compilerCap G D r ε)
      (LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G D r ε)
      (LongTails.Algorithms.AffineSoftmaxOuter.compilerBoost G D r ε)
      (LongTails.Algorithms.AffineSoftmaxOuter.compilerHorizon G D r ε)
      (5 * LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G D r ε) K seeds) ≤ 6 * (K + m) := by
  apply repeatedPlan_cost_le
  intro j _
  exact AffineSoftmaxBudgetGuarantee.computed_budgeted_cost m X initial hτ hL hG hr hrD hε hsmall K (seeds j) reply

open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget

lemma amplifiedOuterPlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (initial xs xstar : E) (hi : initial ∈ X) (hxs : xs ∈ X) (hxstar : xstar ∈ X)
    (hmin : IsMinOn (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) X xs) :
    let H := compilerDepth G D r ε
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    let B := 50000000000000 * (H : ℝ) ^ 6 *
      ((m : ℝ) * compilerScale D r + D * Real.sqrt ((L + 2 * G ^ 2 / τ) / ε) + V * D ^ 2 / ε ^ 2)
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed))))
      {seeds | ε + τ * Real.log m < maximumValue (fun i => f i (Program.eval reply
        (amplifiedOuterPlan m X initial τ L G r D ε (compilerFloor G D r ε) (compilerCap G D r ε) H
          (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (6 * B)) seeds))) -
        maximumValue (fun i => f i xstar)} ≤ (1 / 64 : ℝ≥0∞) := by
  let H := compilerDepth G D r ε
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  let B := 50000000000000 * (H : ℝ) ^ 6 *
    ((m : ℝ) * compilerScale D r + D * Real.sqrt ((L + 2 * G ^ 2 / τ) / ε) + V * D ^ 2 / ε ^ 2)
  let P : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  let trial := fun seeds => budgetedOuterPlan m X initial τ L G r D ε
    (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε)
    (compilerHorizon G D r ε) (5 * H) (Nat.ceil (6 * B)) seeds
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hfc := (AffineSoftmaxOuterParameters.compiler_search_conditions hG hr hrD hε hsmall).1
  have ht : Measurable (fun seeds => Program.eval reply (trial seeds)) :=
    AffineSoftmaxBudgetGuarantee.budgetedOuterPlan_measurable m hX hcompact initial hi τ L G D ε hr hf hfc
      H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (6 * B)) reply hm
  have hx seeds : Program.eval reply (trial seeds) ∈ X :=
    AffineSoftmaxBudgetGuarantee.budgetedOuterPlan_mem m hX hcompact initial hi τ L G D ε hr.le hf hfc
      H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (6 * B)) seeds reply
  have hs := AffineSoftmaxBudgetGuarantee.computed_budgeted_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hlocal
    hdiam hc hg hlip hbound reply hm hreply initial xs hi hxs hmin
  have hmax := smoothed_to_maximum_failure (P : Measure _) f hτ xs xstar
    (fun seeds => Program.eval reply (trial seeds)) (hmin hxstar) hs
  have hp : (P : Measure _) {seeds | ε + τ * Real.log m < maximumValue (fun i => f i (Program.eval reply (trial seeds))) -
      maximumValue (fun i => f i xstar)} ≤ (1 / 2 : ℝ≥0∞) := by
    have hb : ENNReal.ofReal (23 / 60 : ℝ) ≤ (1 / 2 : ℝ≥0∞) := by
      calc
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)
        _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    apply le_trans _ hb
    simpa only [Fintype.card_fin] using hmax
  have hh := repeatedPlan_original_failure P m f trial reply hm hreply ht hx 5
    (maximumValue (fun i => f i xstar)) (ε + τ * Real.log m) (1 / 2) hp
  have hp6 : (1 / 2 : ℝ≥0∞) ^ 6 = 1 / 64 := by
    rw [one_div, ← ENNReal.inv_pow]
    norm_num
  norm_num only [show (5 : ℕ) + 1 = 6 from rfl, hp6] at hh
  simpa only [P, ProbabilityMeasure.coe_mk, trial, amplifiedOuterPlan, H, B, V] using hh

end LongTails.Proofs.AffineSoftmaxAmplification
