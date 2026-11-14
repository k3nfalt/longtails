import LongTails.Proofs.AffineResidualQuerySafety

namespace LongTails.Proofs.AffineResidualAmplification

open MeasureTheory
open scoped ENNReal
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxAmplification
open AffineSoftmaxAmplification

lemma repeatedPlan_failure {E Ω : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) (trial : Ω → Program (Fin m × E) (ℝ × E) E)
    (reply : Fin m × E → ℝ × E)
    (ht : Measurable (fun ω => Program.eval reply (trial ω)))
    (hfinite : (Set.range (fun ω => Program.eval reply (trial ω))).Finite) (n : ℕ) (baseline ε : ℝ) (p : ℝ≥0∞)
    (hp : (P : Measure Ω) {ω | ε < maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline} ≤ p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {seeds | ε < maximumValue (fun i => (reply (i, Program.eval reply (repeatedPlan m (fun j => trial (seeds j)) n))).1) - baseline} ≤
      p ^ (n + 1) := by
  let score := fun ω => maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline
  have hs : Measurable score := by
    exact AffineResidualOuterExecution.measurable_dependent_finite
      (fun ω => Program.eval reply (trial ω))
      (fun x _ => maximumValue (fun i => (reply (i, x)).1) - baseline)
      ht hfinite (fun _ => measurable_const)
  apply AffineSoftmaxSearch.independent_selection_failure P score hs _ (n + 1) ε p
  · intro seeds j hj
    exact sub_le_sub_right (repeatedPlan_score_le m (fun j => trial (seeds j)) reply n j (by omega)) baseline
  · exact hp

lemma repeatedPlan_original_failure {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [MeasurableSingletonClass E] [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) (f : Fin m → E → ℝ) (trial : Ω → Program (Fin m × E) (ℝ × E) E)
    (reply : Fin m × E → ℝ × E) {X : Set E}
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (ht : Measurable (fun ω => Program.eval reply (trial ω)))
    (hfinite : (Set.range (fun ω => Program.eval reply (trial ω))).Finite) (hx : ∀ ω, Program.eval reply (trial ω) ∈ X)
    (n : ℕ) (baseline ε : ℝ) (p : ℝ≥0∞)
    (hp : (P : Measure Ω) {ω | ε < maximumValue (fun i => f i (Program.eval reply (trial ω))) - baseline} ≤ p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {seeds | ε < maximumValue (fun i => f i (Program.eval reply (repeatedPlan m (fun j => trial (seeds j)) n))) - baseline} ≤
      p ^ (n + 1) := by
  have he ω := maximum_reply_eq m f reply hreply _ (hx ω)
  have hprob : (P : Measure Ω) {ω | ε < maximumValue (fun i => (reply (i, Program.eval reply (trial ω))).1) - baseline} ≤ p := by
    simpa only [he] using hp
  have hh := repeatedPlan_failure P m trial reply ht hfinite n baseline ε p hprob
  have hout (seeds : ℕ → Ω) := maximum_reply_eq m f reply hreply _
    (repeatedPlan_mem m (fun j => trial (seeds j)) reply n X (fun j => hx (seeds j)))
  simpa only [hout] using hh


open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualBudget
open LongTails.Algorithms.AffineSoftmaxOuter (compilerDepth compilerFloor compilerCap compilerBoost compilerHorizon compilerScale)

lemma repeatedOuterPlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (initial xs xstar : E) (hi : initial ∈ X) (hxs : xs ∈ X) (hxstar : xstar ∈ X)
    (hmin : IsMinOn (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) X xs) (n : ℕ) :
    let H := compilerDepth G D r ε
    let B := 30000000000000 * (H : ℝ) ^ 7 * compilerScale D r *
      (m + AffineResidualCostParameters.localWork m τ (compilerFloor G D r ε) L r)
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed))))
      {seeds | ε + τ * Real.log m < maximumValue (fun i => f i (Program.eval reply
        (repeatedPlan m (fun j => budgetedOuterPlan m X initial τ L r D ε (compilerFloor G D r ε) (compilerCap G D r ε) H
          (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) (seeds j)) n))) -
        maximumValue (fun i => f i xstar)} ≤ (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
  let H := compilerDepth G D r ε
  let B := 30000000000000 * (H : ℝ) ^ 7 * compilerScale D r *
    (m + AffineResidualCostParameters.localWork m τ (compilerFloor G D r ε) L r)
  let P : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  let trial := fun seeds => budgetedOuterPlan m X initial τ L r D ε
    (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε)
    (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) seeds
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε (G := G)
  have hfc := (AffineSoftmaxOuterParameters.compiler_search_conditions hG hr hrD hε hsmall).1
  have hH : 0 < H := lt_of_lt_of_le (by norm_num : 0 < 3)
    (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε)
  have hfinite := AffineResidualBudgetGuarantee.budgetedOuterPlan_finite_range m X initial τ L r D ε
    (compilerFloor G D r ε) (compilerCap G D r ε) H (compilerBoost G D r ε)
    (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) reply
  have ht : Measurable (fun seeds => Program.eval reply (trial seeds)) :=
    AffineResidualBudgetGuarantee.budgetedOuterPlan_measurable m hX hcompact ⟨initial, hi⟩ initial τ L r D ε (compilerFloor G D r ε) (compilerCap G D r ε)
      H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) reply
  have hx seeds : Program.eval reply (trial seeds) ∈ X :=
    AffineResidualBudgetGuarantee.budgetedOuterPlan_mem m hX hcompact initial hi D ε hτ hL hr hf hfc
      H (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) (Nat.ceil (12 * B)) hH seeds reply
  have hs := AffineResidualBudgetGuarantee.computed_budgeted_failure m hX hcompact f hτ hL hG hr hrD hε hsmall
    hdiam hc hg hlip hbound reply hreply initial xs hi hxs hmin
  have hmax := smoothed_to_maximum_failure (P : Measure _) f hτ xs xstar
    (fun seeds => Program.eval reply (trial seeds)) (hmin hxstar) hs
  have hp : (P : Measure _) {seeds | ε + τ * Real.log m < maximumValue (fun i => f i (Program.eval reply (trial seeds))) -
      maximumValue (fun i => f i xstar)} ≤ (1 / 2 : ℝ≥0∞) := by
    have hb : ENNReal.ofReal (3 / 10 : ℝ) ≤ (1 / 2 : ℝ≥0∞) := by
      calc
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)
        _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    apply le_trans _ hb
    simpa only [Fintype.card_fin] using hmax
  have hh := repeatedPlan_original_failure P m f trial reply hreply ht hfinite hx n
    (maximumValue (fun i => f i xstar)) (ε + τ * Real.log m) (1 / 2) hp
  simpa only [P, ProbabilityMeasure.coe_mk, trial, H, B] using hh


end LongTails.Proofs.AffineResidualAmplification
