import LongTails.Proofs.AffineSoftmaxOuterProcess

namespace LongTails.Proofs.AffineSoftmaxOuterDrift

open MeasureTheory
open LongTails.Proofs.AffineSoftmaxOuterProcess
open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxSearch

noncomputable def movement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (F : E → ℝ) (floor D ε : ℝ)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  if 100 * D ^ 2 / ε ≤ (state s).weight then 0 else
    let μ := select s seeds
    μ * ((state s).weight + nextWeight μ (state s).weight) / 16 * (displacement F floor s μ) ^ 2

lemma movement_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {X : Set E} (hcompact : IsCompact X) (hne : X.Nonempty) {F : E → ℝ}
    (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X) {floor : ℝ} (hf : 0 < floor) (D ε : ℝ)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : Measurable (Function.uncurry select)) :
    Measurable (Function.uncurry (movement F floor D ε select)) := by
  let Z := StateSpace X × (ℕ → ProbeSeed)
  have hA : Measurable (fun z : Z => (state z.1).weight) := measurable_subtype_coe.fst.comp measurable_fst
  have hd := AffineSoftmaxSearchCoupling.predictor_displacement_joint_measurable hcompact hne hF hFc hf
    (fun z : Z => state z.1) hA (measurable_subtype_coe.snd.fst.comp measurable_fst)
    (measurable_subtype_coe.snd.snd.comp measurable_fst)
  have hmap : Measurable (fun z : Z => (z, select z.1 z.2)) := measurable_id.prodMk hs
  have hh := hd.comp hmap
  have hdisp : Measurable (fun z : Z => displacement F floor z.1 (select z.1 z.2)) := by
    simpa only [Function.comp_def, displacement] using hh
  have ha := AffineSoftmaxPredictor.nextWeight_measurable
    (fun z : Z => select z.1 z.2) (fun z => (state z.1).weight) hs hA
  exact Measurable.ite (measurableSet_le measurable_const hA) measurable_const
    (((hs.mul (hA.add ha)).div_const 16).mul (hdisp.pow_const 2))

lemma movement_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (F : E → ℝ) (floor D ε : ℝ)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (s : StateSpace X) (seeds : ℕ → ProbeSeed) : 0 ≤ movement F floor D ε select s seeds := by
  unfold movement
  split_ifs
  · exact le_rfl
  · have ha : 0 < nextWeight (select s seeds) (state s).weight :=
      (CappedProximalGeometry.accelerated_weight_properties (hs s seeds) s.property.1).1
    have hA : 0 ≤ (state s).weight := s.property.1
    have hμ := hs s seeds
    dsimp only
    positivity

lemma movement_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (F : E → ℝ) {floor cap D ε r : ℝ}
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hlower : ∀ s seeds, floor ≤ select s seeds) (hupper : ∀ s seeds, select s seeds ≤ cap)
    (hd : ∀ s seeds, displacement F floor s (select s seeds) ≤ r)
    (s : StateSpace X) (seeds : ℕ → ProbeSeed) :
    movement F floor D ε select s seeds ≤ cap * (3 * (100 * D ^ 2 / ε)) / 16 * r ^ 2 := by
  have hcap : 0 ≤ cap := (hs s seeds).le.trans (hupper s seeds)
  unfold movement
  split_ifs with hstop
  · positivity
  · have ha := CappedProximalGeometry.accelerated_weight_properties (hs s seeds) s.property.1
    have hμM : 1 ≤ select s seeds * (100 * D ^ 2 / ε) :=
      hscale.trans (mul_le_mul_of_nonneg_right (hlower s seeds) hM.le)
    have hT := AffineSoftmaxOuterBounds.weight_overshoot (le_of_lt (lt_of_not_ge hstop)) ha.1 hM hμM ha.2
    have hdnonneg : 0 ≤ displacement F floor s (select s seeds) := norm_nonneg _
    have hTnonneg : 0 ≤ (state s).weight + nextWeight (select s seeds) (state s).weight := by
      have hA : 0 ≤ (state s).weight := s.property.1
      have hp : 0 < nextWeight (select s seeds) (state s).weight := ha.1
      linarith
    dsimp only
    gcongr
    · exact hupper s seeds
    · exact hT.le
    · exact hd s seeds

lemma transition_weight_max {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    {floor : ℝ} (hlower : ∀ s seeds, floor ≤ select s seeds)
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    (state (transition m hX hcompact τ L G r D ε hr select hs H reply s seed)).weight ≤
      max (state s).weight (3 * (100 * D ^ 2 / ε)) := by
  classical
  by_cases hA : (state s).weight ≤ 3 * (100 * D ^ 2 / ε)
  · exact (transition_weight_bound m hX hcompact τ L G r D ε hr select hs hlower hM hscale H reply s seed hA).trans
      (le_max_right _ _)
  · have hstop : 100 * D ^ 2 / ε ≤ (state s).weight := by linarith
    rw [state_transition, ite_eq_left hstop]
    exact le_max_left _ _

lemma transition_energy_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hcompact : IsCompact X) {F : E → ℝ}
    (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X) (τ L G D ε : ℝ) {r floor cap : ℝ}
    (hr : 0 < r) (hf : 0 < floor) (hM : 0 < 100 * D ^ 2 / ε)
    (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : Measurable (Function.uncurry select))
    (hlower : ∀ s seeds, floor ≤ select s seeds) (hupper : ∀ s seeds, select s seeds ≤ cap)
    (hd : ∀ s seeds, displacement F floor s (select s seeds) ≤ r)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (hm : Measurable reply) (xs : E) (s : StateSpace X) :
    Integrable (fun seed : OuterSeed =>
      let out := transition m hF.1 hcompact τ L G r D ε hr.le select hs H reply s seed
      potential F xs out - ε / 100 * (state out).weight + movement F floor D ε select s seed.1)
      (outerLaw : Measure OuterSeed) := by
  have hne : X.Nonempty := ⟨s.val.2.1, s.property.2.1⟩
  let step := transition m hF.1 hcompact τ L G r D ε hr.le select hs H reply
  have hstep : Measurable (step s) := (transition_measurable m hF.1 hcompact hne τ L G D ε hr
    select hs hms H reply hm).comp (measurable_const.prodMk measurable_id)
  have hw seed : (step s seed).val.1 ≤ max (state s).weight (3 * (100 * D ^ 2 / ε)) :=
    transition_weight_max m hF.1 hcompact τ L G r D ε hr.le select hs hlower hM hscale H reply s seed
  have hp := potential_integrable outerLaw hcompact hFc xs (step s) hstep hw
  have hwm : Measurable (fun seed => (step s seed).val.1) := measurable_subtype_coe.fst.comp hstep
  have hwi : Integrable (fun seed => (step s seed).val.1) (outerLaw : Measure OuterSeed) :=
    Integrable.of_bound hwm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun seed => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (step s seed).property.1] using hw seed)
  have hmm : Measurable (fun seed : OuterSeed => movement F floor D ε select s seed.1) :=
    (movement_measurable hcompact hne hF hFc hf D ε select hms).comp (measurable_const.prodMk measurable_fst)
  have hmi : Integrable (fun seed : OuterSeed => movement F floor D ε select s seed.1) (outerLaw : Measure OuterSeed) :=
    Integrable.of_bound hmm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun seed => by
      rw [Real.norm_eq_abs, abs_of_nonneg (movement_nonneg F floor D ε select hs s seed.1)]
      exact movement_bound F hM hscale select hs hlower hupper hd s seed.1)
  exact (hp.sub (hwi.const_mul (ε / 100))).add hmi

lemma transition_expected_drift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε floor cap t : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hD : 0 < D) (hε : 0 < ε)
    (hf : 0 < floor) (H : ℕ) (hH : 3 ≤ H) (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hfloor : floor = ε * (H : ℝ) ^ 2 / (t * r ^ 2))
    (hMscale : 1 ≤ floor * (100 * D ^ 2 / ε)) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : Measurable (Function.uncurry select))
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate
      (displacement (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) floor s)
      r floor cap (select s seeds))
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (xs : E) (hxs : xs ∈ X) (s : StateSpace X) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let step := transition m hX hcompact τ L G r D ε hr.le select hs H reply
    (∫ seed : OuterSeed, potential F xs (step s seed) - ε / 100 * (state (step s seed)).weight +
      movement F floor D ε select s seed.1 ∂(outerLaw : Measure OuterSeed)) ≤
      potential F xs s - ε / 100 * (state s).weight := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let step := transition m hX hcompact τ L G r D ε hr.le select hs H reply
  let Φ := fun seed : OuterSeed => potential F xs (step s seed) - ε / 100 * (state (step s seed)).weight +
    movement F floor D ε select s seed.1
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFc : ContinuousOn F X := by
    intro z hz
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)).continuousAt.continuousWithinAt
  have hlower s seeds : floor ≤ select s seeds := (hcert s seeds).1.1
  have hupper s seeds : select s seeds ≤ cap := (hcert s seeds).1.2
  have hd s seeds : displacement F floor s (select s seeds) < r :=
    (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert s seeds)).1
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hi : Integrable Φ (outerLaw : Measure OuterSeed) := transition_energy_integrable m hcompact hF hFc
    τ L G D ε hr hf hM hMscale select hs hms hlower hupper (fun s seeds => (hd s seeds).le) H reply hm xs s
  have hsection (seeds : ℕ → ProbeSeed) :
      (∫ seed : FinalSeed, Φ (seeds, seed) ∂(finalLaw : Measure FinalSeed)) ≤
        potential F xs s - ε / 100 * (state s).weight := by
    by_cases hstop : 100 * D ^ 2 / ε ≤ (state s).weight
    · have he (seed : FinalSeed) : step s (seeds, seed) = s := by
        apply state_injective
        simp only [step, state_transition, hstop, ite_true]
      simp only [Φ, he, movement, hstop, ite_true, add_zero, integral_const, probReal_univ, one_smul]
      exact le_rfl
    · let μ := select s seeds
      let u := AffineSoftmaxRegularization.exactProx X F μ (predictor μ (state s))
      have hμ : 0 < μ := hs s seeds
      have hu := AffineSoftmaxRegularization.exactProx_spec hcompact ⟨xs, hxs⟩ hFc μ (predictor μ (state s))
      have hedisp : displacement F floor s μ = ‖u - predictor μ (state s)‖ := by
        dsimp only [displacement]
        rw [max_eq_right (hlower s seeds)]
      have hur : ‖u - predictor μ (state s)‖ ≤ r := by rw [← hedisp]; exact (hd s seeds).le
      have hvalid : μ ≤ 2 * (ε * (H : ℝ) ^ 2 / (t * r ^ 2)) ∨ 3 * r / 4 ≤ ‖predictor μ (state s) - u‖ := by
        have hv := (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert s seeds)).2
        rcases hv with hv | hv
        · exact Or.inl (by simpa only [hfloor] using hv)
        · apply Or.inr
          change 3 * r / 4 ≤ displacement F floor s μ at hv
          rw [hedisp] at hv
          simpa only [norm_sub_rev] using hv
      have hraw := finalStepPlan_expected_drift m hX hcompact f s hτ hL hG hr hD hε hμ H hH ht hscale
        (le_of_lt (lt_of_not_ge hstop)) hlocal hc hg hlip hbound reply hm hreply xs u hxs hu.1
        (hdiam _ s.property.2.2 xs hxs) hu.2 hur hvalid
      have he (seed : FinalSeed) : state (step s (seeds, seed)) =
          OracleTemplate.ComponentEnvelope.Program.eval reply
            (finalStepPlan m X (state s) τ L G r D ε μ H seed) := by
        simp only [step, state_transition, hstop, ite_false]
        rfl
      have hΦeq (seed : FinalSeed) : Φ (seeds, seed) =
          let out := OracleTemplate.ComponentEnvelope.Program.eval reply (finalStepPlan m X (state s) τ L G r D ε μ H seed)
          ((state s).weight + nextWeight μ (state s).weight) * (F out.primal - F xs) + ‖out.dual - xs‖ ^ 2 -
            ε / 100 * ((state s).weight + nextWeight μ (state s).weight) +
            μ * ((state s).weight + nextWeight μ (state s).weight) / 16 * ‖predictor μ (state s) - u‖ ^ 2 := by
        change (state (step s (seeds, seed))).weight * (F (state (step s (seeds, seed))).primal - F xs) +
          ‖(state (step s (seeds, seed))).dual - xs‖ ^ 2 - ε / 100 * (state (step s (seeds, seed))).weight +
          movement F floor D ε select s seeds = _
        rw [he, finalStepPlan_weight]
        simp only [movement, hstop, ite_false]
        rw [hedisp, norm_sub_rev u (predictor μ (state s))]
      simp_rw [hΦeq]
      exact hraw
  change (∫ seed, Φ seed ∂(outerLaw : Measure OuterSeed)) ≤ _
  change (∫ seed, Φ seed ∂(Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))).prod
    (finalLaw : Measure FinalSeed)) ≤ _
  rw [integral_prod Φ hi]
  calc
    _ ≤ ∫ _seeds : ℕ → ProbeSeed, potential F xs s - ε / 100 * (state s).weight
        ∂(Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))) :=
      integral_mono hi.integral_prod_left (integrable_const _) hsection
    _ = _ := by simp [F]

lemma path_energy_control {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hcompact : IsCompact X) {F : E → ℝ}
    (hF : ConvexOn ℝ X F) (hFc : ContinuousOn F X) (τ L G : ℝ) {D ε r floor cap : ℝ}
    (hD : 0 < D) (hε : 0 < ε) (hr : 0 < r) (hf : 0 < floor)
    (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : Measurable (Function.uncurry select))
    (hlower : ∀ s seeds, floor ≤ select s seeds) (hupper : ∀ s seeds, select s seeds ≤ cap)
    (hd : ∀ s seeds, displacement F floor s (select s seeds) ≤ r)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (initial xs : E) (hi : initial ∈ X) (hinit : ‖initial - xs‖ ≤ D)
    (hcond : ∀ s : StateSpace X,
      (∫ seed : OuterSeed,
        let out := transition m hF.1 hcompact τ L G r D ε hr.le select hs H reply s seed
        potential F xs out - ε / 100 * (state out).weight + movement F floor D ε select s seed.1
          ∂(outerLaw : Measure OuterSeed)) ≤ potential F xs s - ε / 100 * (state s).weight) (n : ℕ) :
    let step := transition m hF.1 hcompact τ L G r D ε hr.le select hs H reply
    let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
    let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
    (∫ seeds, potential F xs (states n seeds) ∂(Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed))) +
      ∑ k ∈ Finset.range n, (∫ seeds, movement F floor D ε select (states k seeds) (seeds k).1
        ∂(Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed))) ≤ 4 * D ^ 2 := by
  let step := transition m hF.1 hcompact τ L G r D ε hr.le select hs H reply
  let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
  let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed), inferInstance⟩
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hstep : Measurable (Function.uncurry step) := transition_measurable m hF.1 hcompact ⟨initial, hi⟩
    τ L G D ε hr select hs hms H reply hm
  have hmstates k : Measurable (states k) := AffineSoftmaxSearchCoupling.path_measurable step hstep initialState k
  have hwb k seeds : (states k seeds).val.1 ≤ 3 * (100 * D ^ 2 / ε) :=
    path_weight_bound m hF.1 hcompact τ L G r D ε hr.le select hs hlower hM hscale H reply initialState
      (by change 0 ≤ _; positivity) seeds k
  have hpi k := potential_integrable Q hcompact hFc xs (states k) (hmstates k) (hwb k)
  have hwi k : Integrable (fun seeds => (states k seeds).val.1) (Q : Measure (ℕ → OuterSeed)) :=
    Integrable.of_bound (measurable_subtype_coe.fst.comp (hmstates k)).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun seeds => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (states k seeds).property.1] using hwb k seeds)
  have hmm := movement_measurable hcompact ⟨initial, hi⟩ hF hFc hf D ε select hms
  have hmstage : Measurable (fun z : StateSpace X × OuterSeed => movement F floor D ε select z.1 z.2.1) :=
    hmm.comp (measurable_fst.prodMk measurable_snd.fst)
  have hci k : Integrable (fun seeds => movement F floor D ε select (states k seeds) (seeds k).1)
      (Q : Measure (ℕ → OuterSeed)) := by
    have hh : Measurable (fun seeds => movement F floor D ε select (states k seeds) (seeds k).1) :=
      hmm.comp ((hmstates k).prodMk (measurable_pi_apply k).fst)
    exact Integrable.of_bound hh.aestronglyMeasurable _ (Filter.Eventually.of_forall fun seeds => by
      rw [Real.norm_eq_abs, abs_of_nonneg (movement_nonneg F floor D ε select hs _ _)]
      exact movement_bound F hM hscale select hs hlower hupper hd _ _)
  have hpc : Measurable (fun s : StateSpace X => potential F xs s - ε / 100 * (state s).weight) :=
    (potential_measurable hFc xs).sub (measurable_subtype_coe.fst.const_mul (ε / 100))
  have hb := path_energy_bound outerLaw step hstep
    (fun s => potential F xs s - ε / 100 * (state s).weight) hpc
    (fun s seed => movement F floor D ε select s seed.1) hmstage hcond initialState
    (fun k => (hpi k).sub ((hwi k).const_mul (ε / 100))) hci n
  have hwmean : (∫ seeds, (states n seeds).val.1 ∂(Q : Measure (ℕ → OuterSeed))) ≤ 3 * (100 * D ^ 2 / ε) := by
    calc
      _ ≤ ∫ _seeds, 3 * (100 * D ^ 2 / ε) ∂(Q : Measure (ℕ → OuterSeed)) :=
        integral_mono (hwi n) (integrable_const _) (hwb n)
      _ = _ := by simp
  have hscaled := mul_le_mul_of_nonneg_left hwmean (show 0 ≤ ε / 100 by positivity)
  have heq : ε / 100 * (3 * (100 * D ^ 2 / ε)) = 3 * D ^ 2 := by field_simp
  rw [heq] at hscaled
  have hnorm : ‖initial - xs‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (initial - xs)]
  have hinitpot : potential F xs initialState - ε / 100 * (state initialState).weight = ‖initial - xs‖ ^ 2 := by
    simp [initialState, lift, potential, state]
  rw [hinitpot] at hb
  change (∫ seeds, potential F xs (states n seeds) - ε / 100 * (states n seeds).val.1 ∂(Q : Measure (ℕ → OuterSeed))) +
    ∑ k ∈ Finset.range n, (∫ seeds, movement F floor D ε select (states k seeds) (seeds k).1
      ∂(Q : Measure (ℕ → OuterSeed))) ≤ ‖initial - xs‖ ^ 2 at hb
  rw [integral_sub (hpi n) ((hwi n).const_mul (ε / 100)), integral_const_mul] at hb
  change (∫ seeds, potential F xs (states n seeds) ∂(Q : Measure (ℕ → OuterSeed))) +
    ∑ k ∈ Finset.range n, (∫ seeds, movement F floor D ε select (states k seeds) (seeds k).1
      ∂(Q : Measure (ℕ → OuterSeed))) ≤ _
  linarith

end LongTails.Proofs.AffineSoftmaxOuterDrift
