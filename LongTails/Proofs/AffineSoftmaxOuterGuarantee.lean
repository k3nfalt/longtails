import LongTails.Proofs.AffineSoftmaxOuterProbability
import LongTails.Proofs.AffineSoftmaxOuterParameters

namespace LongTails.Proofs.AffineSoftmaxOuterGuarantee

open MeasureTheory
open LongTails.Proofs.AffineSoftmaxOuterProcess
open LongTails.Proofs.AffineSoftmaxOuterDrift
open LongTails.Proofs.AffineSoftmaxOuterParameters
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxSearch

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
      (repairedSelect m F τ L G r (compilerFloor G D r ε) (compilerCap G D r ε)
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
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z)) (s : StateSpace X) :
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | ¬ AffineSoftmaxSearchCoupling.Certificate
        (displacement (fun z => smoothValue τ (fun i => f i z)) (compilerFloor G D r ε) s)
        r (compilerFloor G D r ε) (compilerCap G D r ε)
        (actualSelect m τ L G r (compilerFloor G D r ε) (compilerCap G D r ε)
          (compilerDepth G D r ε) (compilerBoost G D r ε) reply s seeds)} ≤
      ENNReal.ofReal (1 / (12 * (compilerHorizon G D r ε : ℝ))) := by
  have hp := compiler_search_conditions hG hr hrD hε hsmall
  have h := actualSelect_certificate_failure m hX hcompact f s hτ hL hG hr
    (compilerFloor_pos hr hrD hε) hp.1 hlocal (hdiam _ s.property.2.2 _ s.property.2.1)
    hc hg hlip hbound reply hm hreply (compilerDepth G D r ε) (compilerBoost G D r ε) hp.2.1 hp.2.2.1 hp.2.2.2
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  exact AffineSoftmaxOuterExecution.search_boost_count_failure (compilerHorizon G D r ε) (compilerDepth G D r ε)
    (compilerHorizon_pos hr hrD) (compilerDepth_ge_three G D r ε)

lemma certified_path_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G)
    (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : Measurable (Function.uncurry select))
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate
      (displacement (fun z => smoothValue τ (fun i => f i z)) (compilerFloor G D r ε) s)
      r (compilerFloor G D r ε) (compilerCap G D r ε) (select s seeds))
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (initial xs : E) (hi : initial ∈ X) (hxs : xs ∈ X)
    (hmin : IsMinOn (fun z => smoothValue τ (fun i => f i z)) X xs) :
    let step := transition m hX hcompact τ L G r D ε hr.le select hs (compilerDepth G D r ε) reply
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
  let step := transition m hX hcompact τ L G r D ε hr.le select hs H reply
  let initialState := lift (⟨0, initial, initial⟩ : LongTails.Algorithms.CappedProximal.State E) ⟨le_rfl, hi, hi⟩
  let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hD : 0 < D := hr.trans_le hrD
  have hf : 0 < floor := compilerFloor_pos hr hrD hε
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFc : ContinuousOn F X := by
    intro z hz
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)).continuousAt.continuousWithinAt
  have ht := compilerScale_bounds hr hrD
  have hMscale := compilerFloor_threshold_ge_one hr hrD hε (G := G)
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hlower s seeds : floor ≤ select s seeds := (hcert s seeds).1.1
  have hupper s seeds : select s seeds ≤ cap := (hcert s seeds).1.2
  have hd s seeds : displacement F floor s (select s seeds) ≤ r :=
    (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert s seeds)).1.le
  have hstep : Measurable (Function.uncurry step) := transition_measurable m hX hcompact ⟨initial, hi⟩
    τ L G D ε hr select hs hms H reply hm
  have hmstates k : Measurable (states k) := AffineSoftmaxSearchCoupling.path_measurable step hstep initialState k
  have hwb k seeds : (states k seeds).val.1 ≤ 3 * (100 * D ^ 2 / ε) :=
    path_weight_bound m hX hcompact τ L G r D ε hr.le select hs hlower hM hMscale H reply initialState
      (by change 0 ≤ _; positivity) seeds k
  have hcond s := transition_expected_drift m hX hcompact f hτ hL hG hr hD hε hf H
    (compilerDepth_ge_three G D r ε) ht.1 ht.2.2 (show floor = ε * (H : ℝ) ^ 2 / (t * r ^ 2) from rfl)
    hMscale hlocal hdiam hc hg hlip hbound select hs hms hcert reply hm hreply xs hxs s
  have hcontrol := path_energy_control m hcompact hF hFc τ L G hD hε hr hf hMscale select hs hms hlower hupper hd H reply hm
    initial xs hi (hdiam initial hi xs hxs) hcond N
  let P := fun seeds => potential F xs (states N seeds)
  let M := fun seeds => ∑ k ∈ Finset.range N, movement F floor D ε select (states k seeds) (seeds k).1
  have hpi : Integrable P (Q : Measure (ℕ → OuterSeed)) := potential_integrable Q hcompact hFc xs (states N) (hmstates N) (hwb N)
  have hmm := movement_measurable hcompact ⟨initial, hi⟩ hF hFc hf D ε select hms
  have hci k : Integrable (fun seeds => movement F floor D ε select (states k seeds) (seeds k).1)
      (Q : Measure (ℕ → OuterSeed)) := by
    have hh := hmm.comp ((hmstates k).prodMk (measurable_pi_apply k).fst)
    exact Integrable.of_bound hh.aestronglyMeasurable _ (Filter.Eventually.of_forall fun seeds => by
      rw [Real.norm_eq_abs, abs_of_nonneg (movement_nonneg F floor D ε select hs _ _)]
      exact movement_bound F hM hMscale select hs hlower hupper hd _ _)
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
    AffineSoftmaxOuterStopping.stopping_of_movement m hX hcompact F τ L G hr hD hε hf
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
    (hmin : IsMinOn (fun z => smoothValue τ (fun i => f i z)) X xs) :
    let F := fun z => smoothValue τ (fun i => f i z)
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | ε < F (OracleTemplate.ComponentEnvelope.Program.eval reply
          (outerRunPlan m X initial τ L G r D ε (compilerFloor G D r ε) (compilerCap G D r ε)
            (compilerDepth G D r ε) (compilerBoost G D r ε) seeds (compilerHorizon G D r ε))).primal - F xs} ≤
      ENNReal.ofReal (13 / 60 : ℝ) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let floor := compilerFloor G D r ε
  let cap := compilerCap G D r ε
  let H := compilerDepth G D r ε
  let b := compilerBoost G D r ε
  let N := compilerHorizon G D r ε
  let actual := actualSelect (X := X) m τ L G r floor cap H b reply
  let ideal := repairedSelect (X := X) m F τ L G r floor cap H b reply
  have hf : 0 < floor := compilerFloor_pos hr hrD hε
  have hfc : floor ≤ cap := (compiler_search_conditions hG hr hrD hε hsmall).1
  have hactualpos s seeds : 0 < actual s seeds := hf.trans_le
    (actualSelect_mem m τ L G r hf.le hfc H b reply s seeds).1
  have hcert s seeds : AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (ideal s seeds) :=
    repairedSelect_standard_certificate m hX hcompact f L hτ hG hr hrD hε hsmall hdiam hc hg hbound reply s seeds
  have hidealpos s seeds : 0 < ideal s seeds := hf.trans_le (hcert s seeds).1.1
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFc : ContinuousOn F X := by
    intro z hz
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)).continuousAt.continuousWithinAt
  have hidealm : Measurable (Function.uncurry ideal) := repairedSelect_measurable m hcompact ⟨initial, hi⟩ hF hFc
    τ L G hr hf cap H b reply hm
  let initialState := lift (⟨0, initial, initial⟩ : LongTails.Algorithms.CappedProximal.State E) ⟨le_rfl, hi, hi⟩
  let actualPath := fun seeds => AffineSoftmaxSearchCoupling.path
    (transition m hX hcompact τ L G r D ε hr.le actual hactualpos H reply) initialState seeds N
  let idealPath := fun seeds => AffineSoftmaxSearchCoupling.path
    (transition m hX hcompact τ L G r D ε hr.le ideal hidealpos H reply) initialState seeds N
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)), inferInstance⟩
  have hideal := certified_path_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hlocal hdiam hc hg hlip hbound
    ideal hidealpos hidealm hcert reply hm hreply initial xs hi hxs hmin
  let bad := fun s seeds => ¬ AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (actual s seeds)
  have hbadm : MeasurableSet {z : StateSpace X × (ℕ → ProbeSeed) | bad z.1 z.2} :=
    actual_bad_measurable m hcompact ⟨initial, hi⟩ hF hFc τ L G hr hf cap H b reply hm
  have he s seeds (h : ¬ bad s seeds) : actual s seeds = ideal s seeds := by
    have hc : AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (actual s seeds) := not_not.mp h
    exact (AffineSoftmaxSearchCoupling.repair_eq_candidate _ r floor cap H (actual s seeds) hc).symm
  have hp s : (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))) {seeds | bad s seeds} ≤
      ENNReal.ofReal (1 / (12 * (N : ℝ))) :=
    computed_search_failure m hX hcompact f hτ hL hG hr hrD hε hsmall hlocal hdiam hc hg hlip hbound reply hm hreply s
  have hcoup := selector_coupling_failure m hX hcompact ⟨initial, hi⟩ τ L G D ε hr actual ideal hactualpos hidealpos hidealm H
    reply hm bad hbadm he (by positivity : 0 ≤ 1 / (12 * (N : ℝ))) hp initialState N
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
  have heval := actual_path_eval m hX hcompact initial hi τ L G D ε hr.le hf hfc H b reply seeds N
  change state (actualPath seeds) = _ at heval
  change ε < F (state (actualPath seeds)).primal - F xs
  rw [heval]
  exact hbad

end LongTails.Proofs.AffineSoftmaxOuterGuarantee
