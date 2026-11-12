import LongTails.Proofs.AffineResidualOuterStopping
import LongTails.Proofs.AffineSoftmaxOuterProbability
import LongTails.Proofs.AffineSoftmaxOuterParameters

namespace LongTails.Proofs.AffineResidualOuterGuarantee

open MeasureTheory
open AffineResidualOuterProcess
open AffineResidualOuterDrift
open AffineSoftmaxOuterProcess (StateSpace state lift displacement potential potential_nonneg)
open AffineSoftmaxOuterParameters
open LongTails.Algorithms.AffineSoftmaxOuter (compilerFloor compilerCap compilerDepth compilerBoost compilerHorizon compilerScale)
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch

lemma repairedSelect_standard_certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (L : ℝ) {τ G r D ε : ℝ} (hτ : 0 < τ) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) :
    let F := fun z => smoothValue τ (fun i => f i z)
    AffineSoftmaxSearchCoupling.Certificate (displacement F (compilerFloor G D r ε) s) r
      (compilerFloor G D r ε) (compilerCap G D r ε)
      (repairedSelect m F τ L r (compilerFloor G D r ε) (compilerCap G D r ε)
        (compilerDepth G D r ε) (compilerBoost G D r ε) reply s seeds) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFg z (hz : z ∈ X) : HasGradientAt F (gradient F z) z := by
    have h := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)
    rw [h.gradient]
    exact h
  have hFc : ContinuousOn F X := fun z hz => (hFg z hz).continuousAt.continuousWithinAt
  have hFb z (hz : z ∈ X) : ‖gradient F z‖ ≤ G :=
    SmoothFiniteMaximumGeometry.smoothValue_gradient_bound f hτ.ne' (fun i => hg i z hz) (fun i => hbound i z hz)
  have hp := compiler_search_conditions hG hr hrD hε hsmall
  exact repairedSelect_certificate m hcompact hF hFc hFg τ L hG.le hr (compilerFloor_pos hr hrD hε)
    hp.1 hFb (compilerDepth G D r ε) (compilerBoost G D r ε) hp.2.1 hp.2.2.1 hp.2.2.2 reply s
    (hdiam _ s.property.2.2 _ s.property.2.1) seeds

lemma computed_search_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z)) (s : StateSpace X) :
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | ¬ AffineSoftmaxSearchCoupling.Certificate
        (displacement (fun z => smoothValue τ (fun i => f i z)) (compilerFloor G D r ε) s)
        r (compilerFloor G D r ε) (compilerCap G D r ε)
        (actualSelect m τ L r (compilerFloor G D r ε) (compilerCap G D r ε)
          (compilerDepth G D r ε) (compilerBoost G D r ε) reply s seeds)} ≤
      ENNReal.ofReal (1 / (12 * (compilerHorizon G D r ε : ℝ))) := by
  have hp := compiler_search_conditions hG hr hrD hε hsmall
  have h := actualSelect_certificate_failure m hX hcompact f s hτ hL hG hr
    (compilerFloor_pos hr hrD hε) hp.1 (hdiam _ s.property.2.2 _ s.property.2.1)
    hc hg hlip hbound reply hreply (compilerDepth G D r ε) (compilerBoost G D r ε) hp.2.1 hp.2.2.1 hp.2.2.2
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  exact AffineSoftmaxOuterExecution.search_boost_count_failure (compilerHorizon G D r ε) (compilerDepth G D r ε)
    (compilerHorizon_pos hr hrD) (compilerDepth_ge_three G D r ε)

lemma certified_path_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : ∀ s, Measurable (select s)) (hfinite : ∀ s, (Set.range (select s)).Finite)
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate
      (displacement (fun z => smoothValue τ (fun i => f i z)) (compilerFloor G D r ε) s)
      r (compilerFloor G D r ε) (compilerCap G D r ε) (select s seeds))
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (initial xs : E) (hi : initial ∈ X) (hxs : xs ∈ X)
    (hmin : IsMinOn (fun z => smoothValue τ (fun i => f i z)) X xs) :
    let step := transition m hX hcompact D ε hτ hL hr select hs (compilerDepth G D r ε)
      (by have h := compilerDepth_ge_three G D r ε; omega) reply
    let initialState := lift (⟨0, initial, initial⟩ : LongTails.Algorithms.CappedProximal.State E) ⟨le_rfl, hi, hi⟩
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | ε < smoothValue τ (fun i => f i (state (AffineSoftmaxSearchCoupling.path step initialState seeds
          (compilerHorizon G D r ε))).primal) - smoothValue τ (fun i => f i xs)} ≤ ENNReal.ofReal (2 / 15 : ℝ) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let floor := compilerFloor G D r ε
  let cap := compilerCap G D r ε
  let H := compilerDepth G D r ε
  let N := compilerHorizon G D r ε
  let t := compilerScale D r
  let step := transition m hX hcompact D ε hτ hL hr select hs H
    (by have h := compilerDepth_ge_three G D r ε; change 0 < compilerDepth G D r ε; omega) reply
  let initialState := lift (⟨0, initial, initial⟩ : LongTails.Algorithms.CappedProximal.State E) ⟨le_rfl, hi, hi⟩
  let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hD : 0 < D := hr.trans_le hrD
  have hf : 0 < floor := compilerFloor_pos hr hrD hε
  have ht := compilerScale_bounds hr hrD
  have hMscale := compilerFloor_threshold_ge_one hr hrD hε (G := G)
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hlower s seeds : floor ≤ select s seeds := (hcert s seeds).1.1
  have hHpos : 0 < H := by have h := compilerDepth_ge_three G D r ε; dsimp [H]; omega
  have hstep := transition_measurable_finite m hX hcompact D ε hτ hL hr select hs hfinite hms H hHpos reply
  have hstepf := transition_finite_range m hX hcompact D ε hτ hL hr select hs hfinite H hHpos reply
  have hmstates k : Measurable (states k) := path_measurable_finite step hstepf hstep initialState k
  have hfinstates k : (Set.range (states k)).Finite := path_finite_range step hstepf initialState k
  have hcond s := transition_expected_drift m hX hcompact f hτ hL hr hD hε hf H
    (compilerDepth_ge_three G D r ε) ht.1 ht.2.2 (show floor = ε * (H : ℝ) ^ 2 / (t * r ^ 2) from rfl)
    hdiam hc hg hlip hbound select hs hms hfinite hcert reply hreply xs hxs s
  have hcontrol := path_energy_control m hX hcompact hτ hL hD hε hr hMscale select hs hms hfinite hlower H hHpos reply
    initial xs hi (hdiam initial hi xs hxs) hcond N
  let P := fun seeds => potential F xs (states N seeds)
  let M := fun seeds => ∑ k ∈ Finset.range N, movement F floor D ε select (states k seeds) (seeds k).1
  have hpi : Integrable P (Q : Measure (ℕ → OuterSeed)) :=
    AffineResidualOuterExecution.integrable_observable_finite _ (potential F xs) (hmstates N) (hfinstates N) _
  let obs := fun (s : StateSpace X) μ => if 100 * D ^ 2 / ε ≤ (state s).weight then 0 else
    μ * ((state s).weight + LongTails.Algorithms.CappedProximal.nextWeight μ (state s).weight) / 16 *
      (displacement F floor s μ) ^ 2
  have hsfin s : (Set.range (fun seed : OuterSeed => select s seed.1)).Finite :=
    (hfinite s).subset (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.1, rfl⟩)
  have hcm s : Measurable (fun seed : OuterSeed => movement F floor D ε select s seed.1) := by
    have hh := AffineResidualOuterExecution.measurable_dependent_finite
      (fun seed : OuterSeed => select s seed.1) (fun μ _ => obs s μ)
      ((hms s).comp measurable_fst) (hsfin s) (fun _ => measurable_const)
    simpa only [obs, movement] using hh
  have hcint s : Integrable (fun seed : OuterSeed => movement F floor D ε select s seed.1)
      (outerLaw : Measure OuterSeed) := by
    have hh := AffineResidualOuterExecution.integrable_observable_finite
      (fun seed : OuterSeed => select s seed.1) (obs s) ((hms s).comp measurable_fst) (hsfin s)
      (outerLaw : Measure OuterSeed)
    simpa only [obs, movement] using hh
  have hci k : Integrable (fun seeds => movement F floor D ε select (states k seeds) (seeds k).1)
      (Q : Measure (ℕ → OuterSeed)) :=
    integrable_prefix_finite (outerLaw : Measure OuterSeed) k (states k) (hmstates k) (hfinstates k)
      (fun ξ ξ' h => AffineSoftmaxSearchCoupling.path_prefix step initialState ξ ξ' k h)
      (fun s seed => movement F floor D ε select s seed.1) hcm hcint
  have hmi : Integrable M (Q : Measure (ℕ → OuterSeed)) := integrable_finsetSum _ (fun k _ => hci k)
  have henergy : (∫ seeds, P seeds ∂(Q : Measure (ℕ → OuterSeed))) +
      (∫ seeds, M seeds ∂(Q : Measure (ℕ → OuterSeed))) ≤ 5 * D ^ 2 := by
    dsimp only [M]
    rw [integral_finsetSum _ (fun k _ => hci k)]
    change (∫ seeds, P seeds ∂(Q : Measure (ℕ → OuterSeed))) +
      ∑ k ∈ Finset.range N, (∫ seeds, movement F floor D ε select (states k seeds) (seeds k).1
        ∂(Q : Measure (ℕ → OuterSeed))) ≤ 4 * D ^ 2 at hcontrol
    nlinarith [sq_nonneg D]
  have hstop seeds (hmove : M seeds ≤ 60 * D ^ 2) : 100 * D ^ 2 / ε ≤ (state (states N seeds)).weight :=
    AffineResidualOuterStopping.stopping_of_movement m hX hcompact F hτ hL hr hD hε hf
      (compiler_search_conditions hG hr hrD hε hsmall).1 H (compilerDepth_ge_three G D r ε) ht.1 ht.2.2
      (compilerFloor_threshold hr hrD hε).le hMscale (compiler_log_weight_bound hG hr hrD hε hsmall)
      select hs hcert reply initial hi seeds N (compilerHorizon_bounds hr hrD).1 hmove
  exact AffineSoftmaxOuterProbability.energy_accuracy_failure Q P M
    (fun seeds => (state (states N seeds)).weight) (fun seeds => F (state (states N seeds)).primal - F xs)
    hD hε hpi hmi (fun seeds => potential_nonneg hmin _) (fun seeds =>
      Finset.sum_nonneg (fun k _ => movement_nonneg F floor D ε select hs _ _)) henergy hstop
    (fun seeds => by
      change _ ≤ (states N seeds).val.1 * (F (states N seeds).val.2.1 - F xs) + ‖(states N seeds).val.2.2 - xs‖ ^ 2
      exact le_add_of_nonneg_right (sq_nonneg _))

lemma outerRunPlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (hmin : IsMinOn (fun z => smoothValue τ (fun i => f i z)) X xs) :
    let F := fun z => smoothValue τ (fun i => f i z)
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | ε < F (OracleTemplate.ComponentEnvelope.Program.eval reply
          (outerRunPlan m X initial τ L r D ε (compilerFloor G D r ε) (compilerCap G D r ε)
            (compilerDepth G D r ε) (compilerBoost G D r ε) seeds (compilerHorizon G D r ε))).primal - F xs} ≤
      ENNReal.ofReal (13 / 60 : ℝ) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let floor := compilerFloor G D r ε
  let cap := compilerCap G D r ε
  let H := compilerDepth G D r ε
  let b := compilerBoost G D r ε
  let N := compilerHorizon G D r ε
  let actual := actualSelect (X := X) m τ L r floor cap H b reply
  let ideal := repairedSelect (X := X) m F τ L r floor cap H b reply
  have hf : 0 < floor := compilerFloor_pos hr hrD hε
  have hfc : floor ≤ cap := (compiler_search_conditions hG hr hrD hε hsmall).1
  have hactualpos s seeds : 0 < actual s seeds := hf.trans_le
    (actualSelect_mem m τ L r hf.le hfc H b reply s seeds).1
  have hcert s seeds : AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (ideal s seeds) :=
    repairedSelect_standard_certificate m hX hcompact f L hτ hG hr hrD hε hsmall hdiam hc hg hbound reply s seeds
  have hidealpos s seeds : 0 < ideal s seeds := hf.trans_le (hcert s seeds).1.1
  have hHpos : 0 < H := by have h := compilerDepth_ge_three G D r ε; dsimp [H]; omega
  have hidealm s : Measurable (ideal s) := repairedSelect_measurable m F τ L r floor cap H b reply s
  have hidealf s : (Set.range (ideal s)).Finite := repairedSelect_finite_range m F τ L r floor cap H b reply s
  let initialState := lift (⟨0, initial, initial⟩ : LongTails.Algorithms.CappedProximal.State E) ⟨le_rfl, hi, hi⟩
  let actualPath := fun seeds => AffineSoftmaxSearchCoupling.path
    (transition m hX hcompact D ε hτ hL hr actual hactualpos H hHpos reply) initialState seeds N
  let idealPath := fun seeds => AffineSoftmaxSearchCoupling.path
    (transition m hX hcompact D ε hτ hL hr ideal hidealpos H hHpos reply) initialState seeds N
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hideal := certified_path_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hdiam hc hg hlip hbound
    ideal hidealpos hidealm hidealf hcert reply hreply initial xs hi hxs hmin
  let bad := fun s seeds => ¬ AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (actual s seeds)
  have hbadm s : MeasurableSet {seeds | bad s seeds} :=
    actual_bad_measurable m F τ L r floor cap H b reply s
  have he s seeds (h : ¬ bad s seeds) : actual s seeds = ideal s seeds := by
    have hc : AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (actual s seeds) := not_not.mp h
    exact (AffineSoftmaxSearchCoupling.repair_eq_candidate _ r floor cap H (actual s seeds) hc).symm
  have hp s : (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))) {seeds | bad s seeds} ≤
      ENNReal.ofReal (1 / (12 * (N : ℝ))) :=
    computed_search_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hdiam hc hg hlip hbound reply hreply s
  have hcoup := selector_coupling_failure m hX hcompact D ε hτ hL hr actual ideal hactualpos hidealpos hidealm hidealf H hHpos
    reply bad hbadm he (by positivity : 0 ≤ 1 / (12 * (N : ℝ))) hp initialState N
  have hNr : (0 : ℝ) < N := by exact_mod_cast compilerHorizon_pos hr hrD (G := G) (ε := ε)
  have hscale : (N : ℝ) * (1 / (12 * (N : ℝ))) = 1 / 12 := by field_simp
  rw [hscale] at hcoup
  have hactual := AffineSoftmaxOuterProbability.coupled_failure Q actualPath idealPath
    (fun s => ε < F (state s).primal - F xs) hideal hcoup
  have hadd : ENNReal.ofReal (2 / 15 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) = ENNReal.ofReal (13 / 60 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [hadd] at hactual
  apply le_trans (measure_mono ?_) hactual
  intro seeds hbad
  have heval := actual_path_eval m hX hcompact initial hi D ε hτ hL hr hf hfc H b hHpos reply seeds N
  change state (actualPath seeds) = _ at heval
  change ε < F (state (actualPath seeds)).primal - F xs
  rw [heval]
  exact hbad

end LongTails.Proofs.AffineResidualOuterGuarantee
