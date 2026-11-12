import LongTails.Proofs.AffineResidualOuterProcess
import LongTails.Proofs.AffineResidualOuterMoments

namespace LongTails.Proofs.AffineResidualOuterDrift

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch
open AffineResidualOuterProcess
open AffineResidualOuterMoments
open AffineSoftmaxOuterProcess (StateSpace state lift potential displacement)

noncomputable def movement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (F : E → ℝ) (floor D ε : ℝ)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  if 100 * D ^ 2 / ε ≤ (state s).weight then 0 else
    let μ := select s seeds
    μ * ((state s).weight + nextWeight μ (state s).weight) / 16 * (displacement F floor s μ) ^ 2

lemma finalStepPlan_weight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (s : State E) (τ L r D ε μ : ℝ)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (seed : FinalSeed) :
    (Program.eval reply (finalStepPlan m X s τ L r D ε μ H seed)).weight = s.weight + nextWeight μ s.weight := by
  simp only [finalStepPlan, Program.eval_bind, Program.eval_map]

lemma transition_expected_drift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) {τ L G r D ε floor cap t : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hD : 0 < D) (hε : 0 < ε)
    (hf : 0 < floor) (H : ℕ) (hH : 3 ≤ H) (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hfloor : floor = ε * (H : ℝ) ^ 2 / (t * r ^ 2))
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : ∀ s, Measurable (select s)) (hfinite : ∀ s, (Set.range (select s)).Finite)
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate
      (displacement (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) floor s)
      r floor cap (select s seeds))
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (xs : E) (hxs : xs ∈ X) (s : StateSpace X) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let step := transition m hX hcompact D ε hτ hL hr select hs H (by omega) reply
    (∫ seed : OuterSeed, potential F xs (step s seed) - ε / 100 * (state (step s seed)).weight +
      movement F floor D ε select s seed.1 ∂(outerLaw : Measure OuterSeed)) ≤
      potential F xs s - ε / 100 * (state s).weight := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let step := transition m hX hcompact D ε hτ hL hr select hs H (by omega) reply
  let Φ := fun seed : OuterSeed => potential F xs (step s seed) - ε / 100 * (state (step s seed)).weight +
    movement F floor D ε select s seed.1
  have hFc : ContinuousOn F X := by
    intro z hz
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)).continuousAt.continuousWithinAt
  have hlower s seeds : floor ≤ select s seeds := (hcert s seeds).1.1
  have hd s seeds : displacement F floor s (select s seeds) < r :=
    (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert s seeds)).1
  have hstepm := transition_measurable_finite m hX hcompact D ε hτ hL hr select hs hfinite hms H (by omega) reply s
  have hstepf := transition_finite_range m hX hcompact D ε hτ hL hr select hs hfinite H (by omega) reply s
  have henergy : Integrable (fun seed => potential F xs (step s seed) -
      ε / 100 * (state (step s seed)).weight) (outerLaw : Measure OuterSeed) :=
    AffineResidualOuterExecution.integrable_observable_finite _
      (fun q => potential F xs q - ε / 100 * (state q).weight) hstepm hstepf _
  let observe := fun μ => if 100 * D ^ 2 / ε ≤ (state s).weight then 0 else
    μ * ((state s).weight + nextWeight μ (state s).weight) / 16 * (displacement F floor s μ) ^ 2
  have hselectf : (Set.range (fun seed : OuterSeed => select s seed.1)).Finite :=
    (hfinite s).subset (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.1, rfl⟩)
  have hmov : Integrable (fun seed : OuterSeed => movement F floor D ε select s seed.1)
      (outerLaw : Measure OuterSeed) := by
    have hh := AffineResidualOuterExecution.integrable_observable_finite
      (fun seed : OuterSeed => select s seed.1) observe ((hms s).comp measurable_fst) hselectf
      (outerLaw : Measure OuterSeed)
    simpa only [observe, movement] using hh
  have hi : Integrable Φ (outerLaw : Measure OuterSeed) := henergy.add hmov
  have hsection (seeds : ℕ → ProbeSeed) :
      (∫ seed : FinalSeed, Φ (seeds, seed) ∂(finalLaw : Measure FinalSeed)) ≤
        potential F xs s - ε / 100 * (state s).weight := by
    by_cases hstop : 100 * D ^ 2 / ε ≤ (state s).weight
    · have he (seed : FinalSeed) : step s (seeds, seed) = s := by
        apply AffineSoftmaxOuterProcess.state_injective
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
      have hraw := finalStepPlan_expected_drift m hX hcompact f s hτ hL hr hD hε hμ H hH ht hscale
        (le_of_lt (lt_of_not_ge hstop)) hc hg hlip hbound reply hreply xs u hxs hu.1
        (hdiam _ s.property.2.2 xs hxs) hu.2 hur hvalid
      have he (seed : FinalSeed) : state (step s (seeds, seed)) =
          OracleTemplate.ComponentEnvelope.Program.eval reply
            (finalStepPlan m X (state s) τ L r D ε μ H seed) := by
        simp only [step, state_transition, hstop, ite_false]
        rfl
      have hΦeq (seed : FinalSeed) : Φ (seeds, seed) =
          let out := OracleTemplate.ComponentEnvelope.Program.eval reply (finalStepPlan m X (state s) τ L r D ε μ H seed)
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

lemma transition_weight_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    {floor : ℝ} (hlower : ∀ s seeds, floor ≤ select s seeds)
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed)
    (hA : (state s).weight ≤ 3 * (100 * D ^ 2 / ε)) :
    (state (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s seed)).weight ≤
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
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    {floor : ℝ} (hlower : ∀ s seeds, floor ≤ select s seeds)
    (hM : 0 < 100 * D ^ 2 / ε) (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (initial : StateSpace X)
    (hi : (state initial).weight ≤ 3 * (100 * D ^ 2 / ε)) (seeds : ℕ → OuterSeed) (n : ℕ) :
    (state (AffineSoftmaxSearchCoupling.path
      (transition m hX hcompact D ε hτ hL hr select hselect H hH reply) initial seeds n)).weight ≤
      3 * (100 * D ^ 2 / ε) := by
  induction n with
  | zero => exact hi
  | succ n ih => exact transition_weight_bound m hX hcompact D ε hτ hL hr select hselect hlower hM hscale H hH reply _ _ ih

lemma path_energy_control {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) {F : E → ℝ}
    {τ L D ε r floor : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L)
    (hD : 0 < D) (hε : 0 < ε) (hr : 0 < r)
    (hscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hms : ∀ s, Measurable (select s)) (hfinite : ∀ s, (Set.range (select s)).Finite)
    (hlower : ∀ s seeds, floor ≤ select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E)
    (initial xs : E) (hi : initial ∈ X) (hinit : ‖initial - xs‖ ≤ D)
    (hcond : ∀ s : StateSpace X,
      (∫ seed : OuterSeed,
        let out := transition m hX hcompact D ε hτ hL hr select hs H hH reply s seed
        potential F xs out - ε / 100 * (state out).weight + movement F floor D ε select s seed.1
          ∂(outerLaw : Measure OuterSeed)) ≤ potential F xs s - ε / 100 * (state s).weight) (n : ℕ) :
    let step := transition m hX hcompact D ε hτ hL hr select hs H hH reply
    let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
    let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
    (∫ seeds, potential F xs (states n seeds) ∂(Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed))) +
      ∑ k ∈ Finset.range n, (∫ seeds, movement F floor D ε select (states k seeds) (seeds k).1
        ∂(Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed))) ≤ 4 * D ^ 2 := by
  let step := transition m hX hcompact D ε hτ hL hr select hs H hH reply
  let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
  let states := fun k seeds => AffineSoftmaxSearchCoupling.path step initialState seeds k
  let Q : ProbabilityMeasure (ℕ → OuterSeed) := ⟨Measure.infinitePi fun _ : ℕ => (outerLaw : Measure OuterSeed), inferInstance⟩
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hstep := transition_measurable_finite m hX hcompact D ε hτ hL hr select hs hfinite hms H hH reply
  have hstepf := transition_finite_range m hX hcompact D ε hτ hL hr select hs hfinite H hH reply
  have hmstates k : Measurable (states k) := path_measurable_finite step hstepf hstep initialState k
  have hfinstates k : (Set.range (states k)).Finite := path_finite_range step hstepf initialState k
  have hwb k seeds : (states k seeds).val.1 ≤ 3 * (100 * D ^ 2 / ε) :=
    path_weight_bound m hX hcompact D ε hτ hL hr select hs hlower hM hscale H hH reply initialState
      (by change 0 ≤ _; positivity) seeds k
  have hpi k : Integrable (fun seeds => potential F xs (states k seeds)) (Q : Measure (ℕ → OuterSeed)) :=
    AffineResidualOuterExecution.integrable_observable_finite _ (potential F xs) (hmstates k) (hfinstates k) _
  have hwi k : Integrable (fun seeds => (states k seeds).val.1) (Q : Measure (ℕ → OuterSeed)) :=
    AffineResidualOuterExecution.integrable_observable_finite _ (fun s : StateSpace X => s.val.1)
      (hmstates k) (hfinstates k) _
  let obs := fun (s : StateSpace X) μ => if 100 * D ^ 2 / ε ≤ (state s).weight then 0 else
    μ * ((state s).weight + nextWeight μ (state s).weight) / 16 * (displacement F floor s μ) ^ 2
  have hsfin s : (Set.range (fun seed : OuterSeed => select s seed.1)).Finite :=
    (hfinite s).subset (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.1, rfl⟩)
  have hcm s : Measurable (fun seed : OuterSeed => movement F floor D ε select s seed.1) := by
    have hh := AffineResidualOuterExecution.measurable_dependent_finite
      (fun seed : OuterSeed => select s seed.1) (fun μ _ => obs s μ)
      ((hms s).comp measurable_fst) (hsfin s) (fun _ => measurable_const)
    simpa only [obs, movement] using hh
  have hci s : Integrable (fun seed : OuterSeed => movement F floor D ε select s seed.1)
      (outerLaw : Measure OuterSeed) := by
    have hh := AffineResidualOuterExecution.integrable_observable_finite
      (fun seed : OuterSeed => select s seed.1) (obs s) ((hms s).comp measurable_fst) (hsfin s)
      (outerLaw : Measure OuterSeed)
    simpa only [obs, movement] using hh
  have hb := path_expected_energy (outerLaw : Measure OuterSeed) step hstepf hstep initialState n
    (fun s => potential F xs s - ε / 100 * (state s).weight)
    (fun s seed => movement F floor D ε select s seed.1) hcm hci 0
    (fun s => by simpa only [add_zero] using hcond s)
  simp only [mul_zero, add_zero] at hb
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

end LongTails.Proofs.AffineResidualOuterDrift
