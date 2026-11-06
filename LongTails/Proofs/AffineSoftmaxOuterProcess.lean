import LongTails.Proofs.AffineSoftmaxSearchCoupling
import LongTails.Proofs.AffineSoftmaxOuterBounds

namespace LongTails.Proofs.AffineSoftmaxOuterProcess

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxSearch

abbrev StateSpace {E : Type*} (X : Set E) :=
  {z : ℝ × E × E // 0 ≤ z.1 ∧ z.2.1 ∈ X ∧ z.2.2 ∈ X}

def state {E : Type*} {X : Set E} (s : StateSpace X) : State E :=
  ⟨s.val.1, s.val.2.1, s.val.2.2⟩

def lift {E : Type*} {X : Set E} (s : State E)
    (hs : 0 ≤ s.weight ∧ s.primal ∈ X ∧ s.dual ∈ X) : StateSpace X :=
  ⟨(s.weight, s.primal, s.dual), hs⟩

noncomputable def transition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) : StateSpace X := by
  classical
  exact if 100 * D ^ 2 / ε ≤ s.val.1 then s else
    lift (Program.eval reply (finalStepPlan m X (state s) τ L G r D ε (select s seed.1) H seed.2))
      (let h := AffineSoftmaxOuterExecution.finalStepPlan_feasible m hX hcompact (state s)
        s.property.1 s.property.2.1 s.property.2.2 τ L G D ε hr (hselect s seed.1) H seed.2 reply
       ⟨s.property.1.trans h.1.le, h.2⟩)

lemma transition_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (τ L G D ε : ℝ) {r : ℝ} (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (hmselect : Measurable (Function.uncurry select)) (H : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (Function.uncurry (transition m hX hcompact τ L G r D ε hr.le select hselect H reply)) := by
  classical
  let Z := StateSpace X × OuterSeed
  have hA : Measurable (fun z : Z => z.1.val.1) := measurable_subtype_coe.fst.comp measurable_fst
  have hx : Measurable (fun z : Z => z.1.val.2.1) := measurable_subtype_coe.snd.fst.comp measurable_fst
  have hv : Measurable (fun z : Z => z.1.val.2.2) := measurable_subtype_coe.snd.snd.comp measurable_fst
  have hμ : Measurable (fun z : Z => select z.1 z.2.1) :=
    hmselect.comp (measurable_fst.prodMk measurable_snd.fst)
  have hout := AffineSoftmaxOuterExecution.finalStepPlan_param_measurable m hX hcompact hne
    (fun z : Z => state z.1) (fun z => z.1.property.1) (fun z => z.1.property.2.1)
    (fun z => z.1.property.2.2) hA hx hv τ L G D ε hr (fun z => select z.1 z.2.1)
    hμ (fun z => hselect z.1 z.2.1) H reply hm (fun z => z.2.2) measurable_snd.snd
  have hstop : MeasurableSet {z : Z | 100 * D ^ 2 / ε ≤ z.1.val.1} :=
    measurableSet_le measurable_const hA
  apply Measurable.subtype_mk
  change Measurable (fun z : Z =>
    (transition m hX hcompact τ L G r D ε hr.le select hselect H reply z.1 z.2).val)
  have he (z : Z) : (transition m hX hcompact τ L G r D ε hr.le select hselect H reply z.1 z.2).val =
      if 100 * D ^ 2 / ε ≤ z.1.val.1 then z.1.val else
      let out := Program.eval reply (finalStepPlan m X (state z.1) τ L G r D ε (select z.1 z.2.1) H z.2.2)
      (out.weight, out.primal, out.dual) := by
    by_cases h : 100 * D ^ 2 / ε ≤ z.1.val.1
    · simp [transition, h]
    · simp [transition, h, lift]
  simp_rw [he]
  exact Measurable.ite hstop (measurable_subtype_coe.comp measurable_fst)
    (hout.1.prodMk (hout.2.1.prodMk hout.2.2))

lemma state_transition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    state (transition m hX hcompact τ L G r D ε hr select hselect H reply s seed) =
      if 100 * D ^ 2 / ε ≤ (state s).weight then state s else
      Program.eval reply (finalStepPlan m X (state s) τ L G r D ε (select s seed.1) H seed.2) := by
  classical
  by_cases h : 100 * D ^ 2 / ε ≤ s.val.1
  · simp [transition, state, h]
  · simp [transition, state, lift, h]

noncomputable def actualSelect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (τ L G r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  Program.eval reply (regularizationSearchPlan m X (state s) τ L G r floor cap H b seeds)

lemma actualSelect_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (τ L G r : ℝ) {floor cap : ℝ} (hf : 0 ≤ floor) (hfc : floor ≤ cap)
    (H b : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) :
    actualSelect m τ L G r floor cap H b reply s seeds ∈ Set.Icc floor cap := by
  exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.trans hfc) hfc H

lemma actualSelect_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (Function.uncurry (actualSelect (X := X) m τ L G r floor cap H b reply)) := by
  let Z := StateSpace X × (ℕ → ProbeSeed)
  exact AffineSoftmaxOuterExecution.regularizationSearchPlan_param_measurable m hX hcompact
    (fun z : Z => state z.1) (fun z => z.1.property.1) (fun z => z.1.property.2.1)
    (fun z => z.1.property.2.2) (measurable_subtype_coe.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.snd.comp measurable_fst) τ L G hr hf cap H b reply hm
    (fun z => z.2) (fun i a j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp measurable_snd))))

lemma actual_path_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ) {r floor cap : ℝ}
    (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (seeds : ℕ → OuterSeed) (n : ℕ) :
    let select := actualSelect (X := X) m τ L G r floor cap H b reply
    let step := transition m hX hcompact τ L G r D ε hr select
      (fun s seeds => hf.trans_le (actualSelect_mem m τ L G r hf.le hfc H b reply s seeds).1) H reply
    state (AffineSoftmaxSearchCoupling.path step (lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩) seeds n) =
      Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b seeds n) := by
  classical
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [AffineSoftmaxSearchCoupling.path, state_transition, actualSelect]
    rw [ih]
    simp only [outerRunPlan, Program.eval_bind, outerStepPlan]
    split_ifs <;> simp only [Program.eval_bind, Program.eval]

lemma state_injective {E : Type*} {X : Set E} : Function.Injective (state (X := X)) := by
  intro s t he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg State.weight he
  · apply Prod.ext
    · exact congrArg State.primal he
    · exact congrArg State.dual he

lemma transition_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select other : StateSpace X → (ℕ → ProbeSeed) → ℝ)
    (hs : ∀ s seeds, 0 < select s seeds) (ho : ∀ s seeds, 0 < other s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed)
    (he : select s seed.1 = other s seed.1) :
    transition m hX hcompact τ L G r D ε hr select hs H reply s seed =
      transition m hX hcompact τ L G r D ε hr other ho H reply s seed := by
  apply state_injective
  simp only [state_transition, he]

lemma selector_coupling_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (τ L G D ε : ℝ) {r : ℝ} (hr : 0 < r)
    (select other : StateSpace X → (ℕ → ProbeSeed) → ℝ)
    (hs : ∀ s seeds, 0 < select s seeds) (ho : ∀ s seeds, 0 < other s seeds)
    (hmo : Measurable (Function.uncurry other)) (H : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (bad : StateSpace X → (ℕ → ProbeSeed) → Prop)
    (hbad : MeasurableSet {z : StateSpace X × (ℕ → ProbeSeed) | bad z.1 z.2})
    (he : ∀ s seeds, ¬ bad s seeds → select s seeds = other s seeds)
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ s, (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | bad s seeds} ≤ ENNReal.ofReal p)
    (initial : StateSpace X) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | AffineSoftmaxSearchCoupling.path
        (transition m hX hcompact τ L G r D ε hr.le select hs H reply) initial seeds n ≠
        AffineSoftmaxSearchCoupling.path
        (transition m hX hcompact τ L G r D ε hr.le other ho H reply) initial seeds n} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  apply AffineSoftmaxSearchCoupling.coupling_failure_bound outerLaw _ _
    (transition_measurable m hX hcompact hne τ L G D ε hr other ho hmo H reply hm)
    (fun s seed => bad s seed.1)
    (hbad.preimage (measurable_fst.prodMk measurable_snd.fst))
    (fun s seed h => transition_congr m hX hcompact τ L G r D ε hr.le select other hs ho H reply s seed (he s seed.1 h)) hp
    _ initial n
  intro s
  change ((Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))).prod
    (finalLaw : Measure FinalSeed)) {seed | bad s seed.1} ≤ ENNReal.ofReal p
  rw [show {seed : OuterSeed | bad s seed.1} = {seeds | bad s seeds} ×ˢ Set.univ by ext seed; simp]
  simpa only [Measure.prod_prod, measure_univ, mul_one] using hb s

noncomputable def displacement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (F : E → ℝ) (floor : ℝ) (s : StateSpace X) (μ : ℝ) : ℝ :=
  ‖AffineSoftmaxRegularization.exactProx X F (max floor μ) (predictor (max floor μ) (state s)) -
    predictor (max floor μ) (state s)‖

noncomputable def repairedSelect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (F : E → ℝ) (τ L G r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  AffineSoftmaxSearchCoupling.repair (displacement F floor s) r floor cap H
    (actualSelect m τ L G r floor cap H b reply s seeds)

lemma repairedSelect_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hcompact : IsCompact X) (hne : X.Nonempty)
    {F : E → ℝ} (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (Function.uncurry (repairedSelect (X := X) m F τ L G r floor cap H b reply)) := by
  let Z := StateSpace X × (ℕ → ProbeSeed)
  have hd := AffineSoftmaxSearchCoupling.predictor_displacement_joint_measurable hcompact hne hF hFc hf
    (fun z : Z => state z.1) (measurable_subtype_coe.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.snd.comp measurable_fst)
  exact AffineSoftmaxSearchCoupling.repair_measurable (fun z : Z => displacement F floor z.1) hd
    (fun z => actualSelect m τ L G r floor cap H b reply z.1 z.2)
    (actualSelect_measurable m hF.1 hcompact τ L G hr hf cap H b reply hm) r floor cap H

lemma repairedSelect_certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (m : ℕ) [NeZero m] {X : Set E} (hcompact : IsCompact X)
    {F : E → ℝ} {g : E → E} (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X)
    (hg : ∀ x ∈ X, HasGradientAt F (g x) x) (τ L : ℝ) {G r floor cap D : ℝ}
    (hG : 0 ≤ G) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (hbound : ∀ x ∈ X, ‖g x‖ ≤ G) (H b : ℕ)
    (hcap : 2 * G / r ≤ cap) (hend : cap / 2 ^ H ≤ floor)
    (hwidth : (2 * D + G / floor) / 2 ^ (H + 7) < r / 64)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (hdiam : ‖(state s).dual - (state s).primal‖ ≤ D)
    (seeds : ℕ → ProbeSeed) :
    AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap
      (repairedSelect m F τ L G r floor cap H b reply s seeds) := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hdiam
  apply AffineSoftmaxSearchCoupling.repair_certificate (displacement F floor s) H
    hr hf hfc (by positivity : 0 ≤ 2 * D + G / floor) _ hend _ hwidth
  · dsimp only [displacement]
    rw [max_eq_right hfc]
    apply (AffineSoftmaxPredictor.proximal_predictor_displacement_bound hcompact hF hFc hg hG hbound
      (state s) s.property.1 s.property.2.1 s.property.2.2 (hf.trans_le hfc)).trans
    apply (div_le_iff₀ (hf.trans_le hfc)).2
    have hh := (div_le_iff₀ hr).1 hcap
    nlinarith
  · intro x hx y hy
    dsimp only [displacement]
    rw [max_eq_right hx.1, max_eq_right hy.1]
    exact AffineSoftmaxPredictor.proximal_predictor_modulus hcompact hF hFc hg hG hf hbound
      (state s) s.property.1 s.property.2.1 s.property.2.2 hdiam hx hy

lemma conditional_prefix_integrable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ) (X : (ℕ → Ω) → Y) (hX : Measurable X)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (Φ : Y → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hi : Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ : ℕ → Ω => ∫ ω, Φ (X ξ) ω ∂p) (Measure.infinitePi fun _ : ℕ => p) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  let P := Measure.infinitePi fun _ : ℕ => p
  let X' := X ∘ OracleTemplate.TwoSidedPL.extendPrefix ω0 k
  have hX' : Measurable X' := hX.comp (OracleTemplate.TwoSidedPL.measurable_extendPrefix ω0 k)
  have hf := OracleTemplate.TwoSidedPL.factor_prefix ω0 k X hdep
  let π : (ℕ → Ω) → (Fin k → Ω) := fun ξ i => ξ i
  have hπ : Measurable π := by fun_prop
  have hpair : Measurable (fun ξ : ℕ → Ω => (π ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ω) × Ω → ℝ := fun z => Φ (X' z.1) z.2
  have hH : Measurable H := hΦ.comp ((hX'.comp measurable_fst).prodMk measurable_snd)
  have hmap := OracleTemplate.SampledConvex.map_prefix_pair p k
  have hHi : Integrable H ((P.map π).prod p) := by
    rw [← hmap]
    apply (integrable_map_measure hH.aestronglyMeasurable hpair.aemeasurable).2
    refine hi.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact congrArg (fun y => Φ y (ξ k)) (hf ξ)
  have hinner : Measurable (fun u => ∫ ω, H (u, ω) ∂p) :=
    hH.stronglyMeasurable.integral_prod_right'.measurable
  have hh := (integrable_map_measure hinner.aestronglyMeasurable hπ.aemeasurable).1 hHi.integral_prod_left
  refine hh.congr (Filter.Eventually.of_forall fun ξ => ?_)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => congrArg (fun y => Φ y ω) (hf ξ).symm

lemma path_energy_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (step : S → Ω → S) (hmstep : Measurable (Function.uncurry step))
    (potential : S → ℝ) (hmp : Measurable potential) (cost : S → Ω → ℝ)
    (hmc : Measurable (Function.uncurry cost))
    (hcond : ∀ s, (∫ ω, potential (step s ω) + cost s ω ∂(Q : Measure Ω)) ≤ potential s)
    (initial : S)
    (hpi : ∀ k, Integrable (fun seeds => potential (AffineSoftmaxSearchCoupling.path step initial seeds k))
      (Measure.infinitePi fun _ : ℕ => (Q : Measure Ω)))
    (hci : ∀ k, Integrable (fun seeds => cost (AffineSoftmaxSearchCoupling.path step initial seeds k) (seeds k))
      (Measure.infinitePi fun _ : ℕ => (Q : Measure Ω))) (n : ℕ) :
    (∫ seeds, potential (AffineSoftmaxSearchCoupling.path step initial seeds n)
      ∂(Measure.infinitePi fun _ : ℕ => (Q : Measure Ω))) +
      ∑ k ∈ Finset.range n, (∫ seeds, cost (AffineSoftmaxSearchCoupling.path step initial seeds k) (seeds k)
        ∂(Measure.infinitePi fun _ : ℕ => (Q : Measure Ω))) ≤ potential initial := by
  let P := Measure.infinitePi fun _ : ℕ => (Q : Measure Ω)
  have hΦ : Measurable (fun z : S × Ω => potential (step z.1 z.2) + cost z.1 z.2) :=
    (hmp.comp hmstep).add hmc
  induction n with
  | zero => simp [AffineSoftmaxSearchCoupling.path]
  | succ n ih =>
    have hi : Integrable (fun seeds => potential (step (AffineSoftmaxSearchCoupling.path step initial seeds n) (seeds n)) +
        cost (AffineSoftmaxSearchCoupling.path step initial seeds n) (seeds n)) P := (hpi (n + 1)).add (hci n)
    have hmX := AffineSoftmaxSearchCoupling.path_measurable step hmstep initial n
    have hdep := AffineSoftmaxSearchCoupling.path_prefix step initial
    have hinner := conditional_prefix_integrable (Q : Measure Ω) n _ hmX
      (fun seeds other h => hdep seeds other n h) (fun s ω => potential (step s ω) + cost s ω) hΦ hi
    have he := OracleTemplate.TwoSidedPL.integral_prefix_dep (Q : Measure Ω) n _ hmX
      (fun seeds other h => hdep seeds other n h) (fun s ω => potential (step s ω) + cost s ω) hΦ hi
    have hs : (∫ seeds, potential (AffineSoftmaxSearchCoupling.path step initial seeds (n + 1)) ∂P) +
        (∫ seeds, cost (AffineSoftmaxSearchCoupling.path step initial seeds n) (seeds n) ∂P) ≤
        ∫ seeds, potential (AffineSoftmaxSearchCoupling.path step initial seeds n) ∂P := by
      rw [← integral_add (hpi (n + 1)) (hci n)]
      change (∫ seeds, potential (step (AffineSoftmaxSearchCoupling.path step initial seeds n) (seeds n)) +
        cost (AffineSoftmaxSearchCoupling.path step initial seeds n) (seeds n) ∂P) ≤ _
      rw [he]
      exact integral_mono hinner (hpi n) (fun seeds => hcond _)
    rw [Finset.sum_range_succ]
    change _ + _ ≤ _ at ih
    dsimp only [P] at hs
    linarith

lemma actualSelect_certificate_failure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (f : Fin m → E → ℝ) (s : StateSpace X)
    {τ L G r floor cap D : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ‖(state s).dual - (state s).primal‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ X → y ∈ X → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ X → ‖gradient (f i) x‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (H b : ℕ) (hcap : 2 * G / r ≤ cap) (hend : cap / 2 ^ H ≤ floor)
    (hwidth : (2 * D + G / floor) / 2 ^ (H + 7) < r / 64) :
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | ¬ AffineSoftmaxSearchCoupling.Certificate
        (displacement (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) floor s)
        r floor cap (actualSelect m τ L G r floor cap H b reply s seeds)} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ b) := by
  have h := AffineSoftmaxSearchExecution.regularizationSearchPlan_failure m hX hcompact f (state s)
    s.property.1 s.property.2.1 s.property.2.2 hτ hL hG hr hf hfc hlocal hdiam
    hc hg hlip hbound reply hm hreply H b hcap hend hwidth
  apply le_trans (measure_mono ?_) h
  intro seeds hbad hgood
  apply hbad
  simpa only [AffineSoftmaxSearchCoupling.Certificate, displacement, actualSelect,
    max_eq_right hgood.1.1] using hgood

lemma actual_bad_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hcompact : IsCompact X) (hne : X.Nonempty)
    {F : E → ℝ} (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    MeasurableSet {z : StateSpace X × (ℕ → ProbeSeed) | ¬ AffineSoftmaxSearchCoupling.Certificate
      (displacement F floor z.1) r floor cap (actualSelect m τ L G r floor cap H b reply z.1 z.2)} := by
  let Z := StateSpace X × (ℕ → ProbeSeed)
  have hd := AffineSoftmaxSearchCoupling.predictor_displacement_joint_measurable hcompact hne hF hFc hf
    (fun z : Z => state z.1) (measurable_subtype_coe.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.snd.comp measurable_fst)
  exact (AffineSoftmaxSearchCoupling.certificate_measurable (fun z : Z => displacement F floor z.1) hd
    (fun z => actualSelect m τ L G r floor cap H b reply z.1 z.2)
    (actualSelect_measurable m hF.1 hcompact τ L G hr hf cap H b reply hm) r floor cap).compl

lemma finalStepPlan_expected_drift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (s : StateSpace X)
    {τ L G r D ε μ t : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hD : 0 < D) (hε : 0 < ε) (hμ : 0 < μ) (H : ℕ) (hH : 3 ≤ H)
    (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hweightcap : (state s).weight ≤ 100 * D ^ 2 / ε) (hcap : L * r ^ 2 ≤ τ)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (xs u : E) (hxs : xs ∈ X) (hu : u ∈ X) (hdiam : ‖(state s).dual - xs‖ ≤ D)
    (hmin : IsMinOn (RecursiveEnvelopeGeometry.regularized
      (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) μ (predictor μ (state s))) X u)
    (hur : ‖u - predictor μ (state s)‖ ≤ r)
    (hvalid : μ ≤ 2 * (ε * (H : ℝ) ^ 2 / (t * r ^ 2)) ∨ 3 * r / 4 ≤ ‖predictor μ (state s) - u‖) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let a := nextWeight μ (state s).weight
    let T := (state s).weight + a
    (∫ seed : FinalSeed,
      let out := Program.eval reply (finalStepPlan m X (state s) τ L G r D ε μ H seed)
      T * (F out.primal - F xs) + ‖out.dual - xs‖ ^ 2 - ε / 100 * T +
        μ * T / 16 * ‖predictor μ (state s) - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤
      (state s).weight * (F (state s).primal - F xs) + ‖(state s).dual - xs‖ ^ 2 - ε / 100 * (state s).weight := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let a := nextWeight μ (state s).weight
  let T := (state s).weight + a
  let out := fun seed : FinalSeed => Program.eval reply (finalStepPlan m X (state s) τ L G r D ε μ H seed)
  let pot := fun seed : FinalSeed => T * (F (out seed).primal - F xs) + ‖(out seed).dual - xs‖ ^ 2
  have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : 0 < H := by omega
  have hraw := AffineSoftmaxOuterMoments.finalStepPlan_expected_energy m hX hcompact f (state s)
    s.property.1 s.property.2.1 s.property.2.2 hτ hL hG hr hD hε hμ H hHpos hcap
    hc hg hlip hbound reply hm hreply xs u hxs hu hdiam hmin hur
  have hout := AffineSoftmaxOuterExecution.finalStepPlan_param_measurable m hX hcompact ⟨xs, hxs⟩
    (fun _ : FinalSeed => state s) (fun _ => s.property.1) (fun _ => s.property.2.1) (fun _ => s.property.2.2)
    measurable_const measurable_const measurable_const τ L G D ε hr (fun _ => μ) measurable_const
    (fun _ => hμ) H reply hm id measurable_id
  have hfeas seed := AffineSoftmaxOuterExecution.finalStepPlan_feasible m hX hcompact (state s)
    s.property.1 s.property.2.1 s.property.2.2 τ L G D ε hr.le hμ H seed reply
  have hFc : ContinuousOn F X := by
    intro z hz
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)).continuousAt.continuousWithinAt
  have hfi := ConstrainedStochasticAcceleration.integrable_compact_image finalLaw hcompact
    (fun z => F z - F xs) (hFc.sub continuousOn_const) (fun seed => (out seed).primal)
    hout.2.1 (fun seed => (hfeas seed).2.1)
  have hvi := ConstrainedStochasticAcceleration.integrable_compact_image finalLaw hcompact
    (fun z => ‖z - xs‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    (fun seed => (out seed).dual) hout.2.2 (fun seed => (hfeas seed).2.2)
  have hpi : Integrable pot (finalLaw : Measure FinalSeed) := (hfi.const_mul T).add hvi
  have ha := CappedProximalGeometry.accelerated_weight_properties hμ s.property.1
  have herr := AffineSoftmaxOuterBounds.final_error_bound hμ s.property.1 ha.1 hr hHreal hε ht hscale ha.2 hweightcap hvalid
  have hsqrt : (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) ^ 2 =
      μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3) := Real.sq_sqrt (by positivity)
  dsimp only at hraw
  rw [hsqrt] at hraw
  have hbias : a * D * (ε / (1000 * D)) = a * ε / 1000 := by field_simp
  change (∫ seed, pot seed + μ * T / 8 * ‖predictor μ (state s) - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤ _ at hraw
  rw [integral_add hpi (integrable_const _), integral_const, probReal_univ, one_smul] at hraw
  change (∫ seed, pot seed - ε / 100 * T + μ * T / 16 * ‖predictor μ (state s) - u‖ ^ 2
    ∂(finalLaw : Measure FinalSeed)) ≤ _
  have hpis : Integrable (fun seed => pot seed - ε / 100 * T) (finalLaw : Measure FinalSeed) :=
    hpi.sub (integrable_const _)
  rw [integral_add hpis (integrable_const _),
    integral_sub hpi (integrable_const (ε / 100 * T)), integral_const, integral_const, probReal_univ, one_smul, one_smul]
  dsimp only [a, T] at hbias ⊢
  rw [hbias] at hraw
  dsimp only [a, T, F, state, nextWeight] at hraw herr ⊢
  nlinarith only [hraw, herr]

lemma finalStepPlan_weight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (s : State E) (τ L G r D ε μ : ℝ)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (seed : FinalSeed) :
    (Program.eval reply (finalStepPlan m X s τ L G r D ε μ H seed)).weight = s.weight + nextWeight μ s.weight := by
  simp only [finalStepPlan, Program.eval_bind, Program.eval_map]

lemma transition_weight_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    {floor : ℝ} (hlower : ∀ s seeds, floor ≤ select s seeds)
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed)
    (hA : (state s).weight ≤ 3 * (100 * D ^ 2 / ε)) :
    (state (transition m hX hcompact τ L G r D ε hr select hselect H reply s seed)).weight ≤
      3 * (100 * D ^ 2 / ε) := by
  classical
  rw [state_transition]
  by_cases hstop : 100 * D ^ 2 / ε ≤ (state s).weight
  · simpa only [hstop, ite_true] using hA
  · simp only [hstop, ite_false, finalStepPlan_weight]
    have ha := CappedProximalGeometry.accelerated_weight_properties (hselect s seed.1) s.property.1
    have hs : 1 ≤ select s seed.1 * (100 * D ^ 2 / ε) :=
      hscale.trans (mul_le_mul_of_nonneg_right (hlower s seed.1) hM.le)
    exact (AffineSoftmaxOuterBounds.weight_overshoot (le_of_lt (lt_of_not_ge hstop)) ha.1 hM hs ha.2).le

lemma path_weight_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    {floor : ℝ} (hlower : ∀ s seeds, floor ≤ select s seeds)
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (H : ℕ) (reply : Fin m × E → ℝ × E) (initial : StateSpace X)
    (hi : (state initial).weight ≤ 3 * (100 * D ^ 2 / ε)) (seeds : ℕ → OuterSeed) (n : ℕ) :
    (state (AffineSoftmaxSearchCoupling.path
      (transition m hX hcompact τ L G r D ε hr select hselect H reply) initial seeds n)).weight ≤
      3 * (100 * D ^ 2 / ε) := by
  induction n with
  | zero => exact hi
  | succ n ih => exact transition_weight_bound m hX hcompact τ L G r D ε hr select hselect hlower hM hscale H reply _ _ ih

def potential {E : Type*} [NormedAddCommGroup E] {X : Set E} (F : E → ℝ) (xs : E)
    (s : StateSpace X) : ℝ := s.val.1 * (F s.val.2.1 - F xs) + ‖s.val.2.2 - xs‖ ^ 2

lemma potential_measurable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {X : Set E} {F : E → ℝ} (hF : ContinuousOn F X) (xs : E) : Measurable (potential (X := X) F xs) := by
  have hx : Measurable (fun s : StateSpace X => (⟨s.val.2.1, s.property.2.1⟩ : X)) :=
    measurable_subtype_coe.snd.fst.subtype_mk
  exact measurable_subtype_coe.fst.mul ((hF.domRestrict.measurable.comp hx).sub_const (F xs)) |>.add
    ((measurable_subtype_coe.snd.snd.sub_const xs).norm.pow_const 2)

lemma potential_nonneg {E : Type*} [NormedAddCommGroup E] {X : Set E} {F : E → ℝ} {xs : E}
    (hmin : IsMinOn F X xs) (s : StateSpace X) : 0 ≤ potential F xs s := by
  have hgap : 0 ≤ F s.val.2.1 - F xs := sub_nonneg.mpr (hmin s.property.2.1)
  exact add_nonneg (mul_nonneg s.property.1 hgap) (sq_nonneg _)

lemma potential_integrable {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω) {X : Set E} (hcompact : IsCompact X)
    {F : E → ℝ} (hF : ContinuousOn F X) (xs : E) (states : Ω → StateSpace X) (hm : Measurable states)
    {B : ℝ} (hb : ∀ ω, (states ω).val.1 ≤ B) :
    Integrable (fun ω => potential F xs (states ω)) (Q : Measure Ω) := by
  have hw : Measurable (fun ω => (states ω).val.1) := measurable_subtype_coe.fst.comp hm
  have hx : Measurable (fun ω => (states ω).val.2.1) := measurable_subtype_coe.snd.fst.comp hm
  have hv : Measurable (fun ω => (states ω).val.2.2) := measurable_subtype_coe.snd.snd.comp hm
  have hfi := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun z => F z - F xs) (hF.sub continuousOn_const) _ hx (fun ω => (states ω).property.2.1)
  have hvi := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun z => ‖z - xs‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    _ hv (fun ω => (states ω).property.2.2)
  exact (hfi.bdd_mul hw.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (states ω).property.1] using hb ω)).add hvi

end LongTails.Proofs.AffineSoftmaxOuterProcess
