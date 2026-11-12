import LongTails.Proofs.AffineResidualOuterExecution
import LongTails.Proofs.TwoSidedPLSampling
import LongTails.Proofs.AffineSoftmaxOuterProcess

namespace LongTails.Proofs.AffineResidualOuterProcess

open MeasureTheory
open AffineResidualOuterExecution

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]

lemma integral_prefix_finite (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (X : (ℕ → Ω) → Y) (hX : Measurable X) (hf : (Set.range X).Finite)
    (hd : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (Φ : Y → Ω → ℝ) (hm : ∀ y, Measurable (Φ y))
    (hi : Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) (Measure.infinitePi fun _ : ℕ => p)) :
    ∫ ξ, Φ (X ξ) (ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫ ξ, (∫ ω, Φ (X ξ) ω ∂p) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  let : Countable (Set.range X) := hf.countable.to_subtype
  let X' := fun ξ => (⟨X ξ, ⟨ξ, rfl⟩⟩ : Set.range X)
  have hX' : Measurable X' := hX.subtype_mk
  have hd' : ∀ ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X' ξ = X' ξ' := by
    intro ξ ξ' h
    exact Subtype.ext (hd ξ ξ' h)
  have hm' : Measurable (fun z : Set.range X × Ω => Φ z.1 z.2) :=
    measurable_from_prod_countable_right (fun y => hm y)
  exact OracleTemplate.TwoSidedPL.integral_prefix_dep p k X' hX' hd'
    (fun y => Φ y) hm' hi

lemma integrable_prefix_finite (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (X : (ℕ → Ω) → Y) (hX : Measurable X) (hf : (Set.range X).Finite)
    (hd : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (Φ : Y → Ω → ℝ) (hm : ∀ y, Measurable (Φ y)) (hi : ∀ y, Integrable (Φ y) p) :
    Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) (Measure.infinitePi fun _ : ℕ => p) := by
  classical
  let : Fintype (Set.range X) := hf.fintype
  let X' := fun ξ => (⟨X ξ, ⟨ξ, rfl⟩⟩ : Set.range X)
  have hX' : Measurable X' := hX.subtype_mk
  have hd' : ∀ ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X' ξ = X' ξ' := by
    intro ξ ξ' h
    exact Subtype.ext (hd ξ ξ' h)
  have hm' : Measurable (fun z : Set.range X × Ω => ‖Φ z.1 z.2‖) :=
    measurable_from_prod_countable_right (fun y => (hm y).norm)
  have hb (y : Set.range X) : (∫ ω, ‖Φ y ω‖ ∂p) ≤ ∑ z : Set.range X, ∫ ω, ‖Φ z ω‖ ∂p :=
    Finset.single_le_sum (f := fun z : Set.range X => ∫ ω, ‖Φ z ω‖ ∂p)
      (fun z _ => integral_nonneg (fun ω => norm_nonneg _)) (Finset.mem_univ y)
  have hn := (OracleTemplate.TwoSidedPL.integrable_prefix_dep p k X' hX' hd'
    (fun y ω => ‖Φ y ω‖) hm' (fun _ _ => norm_nonneg _) (fun y => (hi y).norm) hb).1
  have hmeas : Measurable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) :=
    measurable_dependent_finite X (fun y ξ => Φ y (ξ k)) hX hf
      (fun y => (hm y).comp (measurable_pi_apply k))
  exact (integrable_norm_iff hmeas.aestronglyMeasurable).mp hn

open AffineSoftmaxSearchCoupling (path)

omit [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSingletonClass Y] in
lemma path_finite_range (step : Y → Ω → Y) (hf : ∀ y, (Set.range (step y)).Finite)
    (initial : Y) (n : ℕ) : (Set.range (fun seeds : ℕ → Ω => path step initial seeds n)).Finite := by
  induction n with
  | zero => exact Set.finite_range_const
  | succ n ih =>
      apply finite_range_dependent (fun seeds => path step initial seeds n)
        (fun y seeds => step y (seeds n)) ih
      intro y
      exact (hf y).subset (by rintro _ ⟨seeds, rfl⟩; exact ⟨seeds n, rfl⟩)

lemma path_measurable_finite (step : Y → Ω → Y) (hf : ∀ y, (Set.range (step y)).Finite)
    (hm : ∀ y, Measurable (step y)) (initial : Y) (n : ℕ) :
    Measurable (fun seeds : ℕ → Ω => path step initial seeds n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact measurable_dependent_finite (fun seeds => path step initial seeds n)
        (fun y seeds => step y (seeds n)) ih (path_finite_range step hf initial n)
        (fun y => (hm y).comp (measurable_pi_apply n))

lemma path_integral_step (p : Measure Ω) [IsProbabilityMeasure p]
    (step : Y → Ω → Y) (hf : ∀ y, (Set.range (step y)).Finite)
    (hm : ∀ y, Measurable (step y)) (initial : Y) (n : ℕ)
    (Φ : Y → Ω → ℝ) (hΦ : ∀ y, Measurable (Φ y)) (hi : ∀ y, Integrable (Φ y) p) :
    ∫ seeds, Φ (path step initial seeds n) (seeds n) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫ seeds, (∫ ω, Φ (path step initial seeds n) ω ∂p) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  have hX := path_measurable_finite step hf hm initial n
  have hfin := path_finite_range step hf initial n
  have hd := fun ξ ξ' h => AffineSoftmaxSearchCoupling.path_prefix step initial ξ ξ' n h
  exact integral_prefix_finite p n _ hX hfin hd Φ hΦ
    (integrable_prefix_finite p n _ hX hfin hd Φ hΦ hi)

lemma path_expected_drift (p : Measure Ω) [IsProbabilityMeasure p]
    (step : Y → Ω → Y) (hf : ∀ y, (Set.range (step y)).Finite)
    (hm : ∀ y, Measurable (step y)) (initial : Y) (n : ℕ)
    (V : Y → ℝ) (cost : Y → Ω → ℝ) (hc : ∀ y, Measurable (cost y))
    (hci : ∀ y, Integrable (cost y) p) (error : ℝ)
    (hdrift : ∀ y, ∫ ω, V (step y ω) + cost y ω ∂p ≤ V y + error) :
    (∫ seeds, V (path step initial seeds (n + 1)) ∂(Measure.infinitePi fun _ : ℕ => p)) +
      (∫ seeds, cost (path step initial seeds n) (seeds n) ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
      (∫ seeds, V (path step initial seeds n) ∂(Measure.infinitePi fun _ : ℕ => p)) + error := by
  let P := Measure.infinitePi fun _ : ℕ => p
  have hX := path_measurable_finite step hf hm initial n
  have hfin := path_finite_range step hf initial n
  have hd := fun ξ ξ' h => AffineSoftmaxSearchCoupling.path_prefix step initial ξ ξ' n h
  have hVi j : Integrable (fun seeds => V (path step initial seeds j)) P :=
    integrable_observable_finite _ V (path_measurable_finite step hf hm initial j)
      (path_finite_range step hf initial j) P
  have hcost := integrable_prefix_finite p n _ hX hfin hd cost hc hci
  have hVm y : Measurable (fun ω => V (step y ω)) :=
    measurable_dependent_finite (step y) (fun z _ => V z) (hm y) (hf y)
      (fun _ => measurable_const)
  have hVs y : Integrable (fun ω => V (step y ω)) p :=
    integrable_observable_finite (step y) V (hm y) (hf y) p
  rw [← integral_add (hVi (n + 1)) hcost]
  change (∫ seeds, V (step (path step initial seeds n) (seeds n)) +
    cost (path step initial seeds n) (seeds n) ∂P) ≤ _
  rw [path_integral_step p step hf hm initial n (fun y ω => V (step y ω) + cost y ω)
    (fun y => (hVm y).add (hc y)) (fun y => (hVs y).add (hci y))]
  have hleft : Integrable (fun seeds => ∫ ω, V (step (path step initial seeds n) ω) +
      cost (path step initial seeds n) ω ∂p) P :=
    integrable_observable_finite _ (fun y => ∫ ω, V (step y ω) + cost y ω ∂p) hX hfin P
  calc
    _ ≤ ∫ seeds, V (path step initial seeds n) + error ∂P :=
      integral_mono hleft ((hVi n).add (integrable_const _)) (fun seeds => hdrift _)
    _ = _ := by rw [integral_add (hVi n) (integrable_const _)]; simp [P]

lemma path_expected_energy (p : Measure Ω) [IsProbabilityMeasure p]
    (step : Y → Ω → Y) (hf : ∀ y, (Set.range (step y)).Finite)
    (hm : ∀ y, Measurable (step y)) (initial : Y) (n : ℕ)
    (V : Y → ℝ) (cost : Y → Ω → ℝ) (hc : ∀ y, Measurable (cost y))
    (hci : ∀ y, Integrable (cost y) p) (error : ℝ)
    (hdrift : ∀ y, ∫ ω, V (step y ω) + cost y ω ∂p ≤ V y + error) :
    (∫ seeds, V (path step initial seeds n) ∂(Measure.infinitePi fun _ : ℕ => p)) +
      (∑ i ∈ Finset.range n, ∫ seeds, cost (path step initial seeds i) (seeds i)
        ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ V initial + n * error := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
      have hs := path_expected_drift p step hf hm initial n V cost hc hci error hdrift
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      linarith

omit [MeasurableSpace Ω] in
lemma repair_finite_range (d : ℝ → ℝ) (r floor cap : ℝ) (H : ℕ)
    (candidate : Ω → ℝ) (hf : (Set.range candidate).Finite) :
    (Set.range (fun ω => AffineSoftmaxSearchCoupling.repair d r floor cap H (candidate ω))).Finite := by
  exact (hf.image (AffineSoftmaxSearchCoupling.repair d r floor cap H)).subset
    (by rintro _ ⟨ω, rfl⟩; exact ⟨candidate ω, ⟨ω, rfl⟩, rfl⟩)

lemma repair_measurable_finite (d : ℝ → ℝ) (r floor cap : ℝ) (H : ℕ)
    (candidate : Ω → ℝ) (hf : (Set.range candidate).Finite) (hm : Measurable candidate) :
    Measurable (fun ω => AffineSoftmaxSearchCoupling.repair d r floor cap H (candidate ω)) :=
  measurable_dependent_finite candidate
    (fun μ _ => AffineSoftmaxSearchCoupling.repair d r floor cap H μ) hm hf
    (fun _ => measurable_const)

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch
open AffineSoftmaxOuterProcess (StateSpace state lift)

noncomputable def transition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E)
    (s : StateSpace X) (seed : OuterSeed) : StateSpace X := by
  classical
  exact if 100 * D ^ 2 / ε ≤ s.val.1 then s else
    lift (Program.eval reply (finalStepPlan m X (state s) τ L r D ε (select s seed.1) H seed.2))
      (let h := finalStepPlan_feasible m hX hcompact (state s) s.property.1 s.property.2.1
          s.property.2.2 D ε hτ hL hr (hselect s seed.1) H hH seed.2 reply
       ⟨s.property.1.trans h.1.le, h.2⟩)

lemma state_transition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E)
    (s : StateSpace X) (seed : OuterSeed) :
    state (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s seed) =
      if 100 * D ^ 2 / ε ≤ (state s).weight then state s else
        Program.eval reply (finalStepPlan m X (state s) τ L r D ε (select s seed.1) H seed.2) := by
  classical
  by_cases h : 100 * D ^ 2 / ε ≤ s.val.1
  · simp [transition, state, h]
  · simp [transition, state, lift, h]

lemma transition_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (hfinite : ∀ s, (Set.range (select s)).Finite)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    (Set.range (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s)).Finite := by
  have hinj : Function.Injective (state (X := X)) := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun q : State E => (q.weight, q.primal, q.dual)) h
  apply Set.Finite.of_finite_image (f := state) _ hinj.injOn
  rw [← Set.range_comp]
  simp only [Function.comp_def, state_transition]
  by_cases hs : 100 * D ^ 2 / ε ≤ (state s).weight
  · simp only [hs, ite_true]
    exact Set.finite_range_const
  · simp only [hs, ite_false]
    apply finite_range_dependent (fun seed : OuterSeed => select s seed.1)
      (fun μ seed => Program.eval reply (finalStepPlan m X (state s) τ L r D ε μ H seed.2))
    · exact (hfinite s).subset (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.1, rfl⟩)
    · intro μ
      exact (finalStepPlan_finite_range m X (state s) τ L r D ε μ H reply).subset
        (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.2, rfl⟩)

lemma transition_measurable_finite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hselect : ∀ s seeds, 0 < select s seeds)
    (hfinite : ∀ s, (Set.range (select s)).Finite) (hm : ∀ s, Measurable (select s))
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    Measurable (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s) := by
  apply Measurable.subtype_mk
  change Measurable (fun seed =>
    ((state (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s seed)).weight,
     (state (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s seed)).primal,
     (state (transition m hX hcompact D ε hτ hL hr select hselect H hH reply s seed)).dual))
  simp_rw [state_transition]
  by_cases hs : 100 * D ^ 2 / ε ≤ (state s).weight
  · simp only [hs, ite_true]
    exact measurable_const
  · simp only [hs, ite_false]
    apply measurable_dependent_finite (fun seed : OuterSeed => select s seed.1)
      (fun μ seed => let out := Program.eval reply (finalStepPlan m X (state s) τ L r D ε μ H seed.2)
        (out.weight, out.primal, out.dual)) ((hm s).comp measurable_fst)
    · exact (hfinite s).subset (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.1, rfl⟩)
    · intro μ
      have hh := finalStepPlan_measurable m hX hcompact ⟨s.val.2.1, s.property.2.1⟩
        (state s) τ L r D ε μ H reply
      exact (hh.1.prodMk (hh.2.1.prodMk hh.2.2)).comp measurable_snd

lemma visited_failure_finite (Q : ProbabilityMeasure Ω) (X : ℕ → (ℕ → Ω) → Y)
    (hm : ∀ k, Measurable (X k)) (hf : ∀ k, (Set.range (X k)).Finite)
    (hd : ∀ k ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X k ξ = X k ξ')
    (bad : ℕ → Y → Ω → Prop) (hbmeas : ∀ k y, MeasurableSet {ω | bad k y ω})
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ k y, (Q : Measure Ω) {ω | bad k y ω} ≤ ENNReal.ofReal p) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {ξ | ∃ k < n, bad k (X k ξ) (ξ k)} ≤ ENNReal.ofReal ((n : ℝ) * p) := by
  classical
  let S : Set Y := ⋃ k, Set.range (X k)
  have hS : S.Countable := Set.countable_iUnion (fun k => (hf k).countable)
  let : Countable S := hS.to_subtype
  let X' := fun k ξ => (⟨X k ξ, Set.mem_iUnion.mpr ⟨k, ⟨ξ, rfl⟩⟩⟩ : S)
  have hm' k : Measurable (X' k) := (hm k).subtype_mk
  have hd' : ∀ k ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X' k ξ = X' k ξ' := by
    intro k ξ ξ' h
    exact Subtype.ext (hd k ξ ξ' h)
  have hbad k : MeasurableSet {z : S × Ω | bad k z.1 z.2} := by
    have hi : Measurable (fun z : S × Ω => if bad k z.1 z.2 then (1 : ℝ) else 0) :=
      measurable_from_prod_countable_right (fun y =>
        Measurable.ite (hbmeas k y) measurable_const measurable_const)
    have he := measurableSet_eq_fun hi (measurable_const (a := (1 : ℝ)))
    simpa only [ite_eq_left_iff, zero_ne_one, imp_false, not_not] using he
  exact AffineSoftmaxSearchProbability.visited_failure_bound Q X' hm' hd'
    (fun k y ω => bad k y ω) hbad hp (fun k y => hb k y) n

lemma coupling_failure_finite (Q : ProbabilityMeasure Ω) (actual repaired : Y → Ω → Y)
    (hm : ∀ y, Measurable (repaired y)) (hf : ∀ y, (Set.range (repaired y)).Finite)
    (bad : Y → Ω → Prop) (hbad : ∀ y, MeasurableSet {ω | bad y ω})
    (heq : ∀ y ω, ¬ bad y ω → actual y ω = repaired y ω)
    {p : ℝ} (hp : 0 ≤ p) (hb : ∀ y, (Q : Measure Ω) {ω | bad y ω} ≤ ENNReal.ofReal p)
    (initial : Y) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {seeds | path actual initial seeds n ≠ path repaired initial seeds n} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  have h := visited_failure_finite Q (fun k seeds => path repaired initial seeds k)
    (path_measurable_finite repaired hf hm initial) (path_finite_range repaired hf initial)
    (fun k ξ ξ' h => AffineSoftmaxSearchCoupling.path_prefix repaired initial ξ ξ' k h)
    (fun _ y ω => bad y ω) (fun _ => hbad) hp (fun _ => hb) n
  apply le_trans (measure_mono ?_) h
  intro seeds hne
  by_contra hn
  apply hne
  apply AffineSoftmaxSearchCoupling.paths_equal_of_no_failure actual repaired bad heq initial seeds n
  intro k hk hkbad
  exact hn ⟨k, hk, hkbad⟩

open AffineSoftmaxOuterProcess (displacement)

noncomputable def actualSelect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  Program.eval reply (regularizationSearchPlan m X (state s) τ L r floor cap H b seeds)

lemma actualSelect_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (τ L r : ℝ) {floor cap : ℝ} (hf : 0 ≤ floor) (hfc : floor ≤ cap)
    (H b : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) :
    actualSelect m τ L r floor cap H b reply s seeds ∈ Set.Icc floor cap :=
  AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.trans hfc) hfc H

lemma actualSelect_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    (Set.range (actualSelect m τ L r floor cap H b reply s)).Finite := by
  unfold actualSelect regularizationSearchPlan
  exact AffineResidualSearchTrace.searchPlan_finite_range
    (fun (seeds : ℕ → ProbeSeed) i μ => probePlan m
      (X ∩ Metric.closedBall (predictor (max floor μ) (state s)) r)
      (predictor (max floor μ) (state s)) τ (max floor μ) L r (seeds i) b)
    reply r floor cap H

lemma actualSelect_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E}
    (τ L r floor cap : ℝ) (H b : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    Measurable (actualSelect m τ L r floor cap H b reply s) :=
  AffineResidualSearchTrace.regularizationSearchPlan_measurable m X (state s)
    τ L r floor cap H b reply

noncomputable def repairedSelect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (F : E → ℝ) (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seeds : ℕ → ProbeSeed) : ℝ :=
  AffineSoftmaxSearchCoupling.repair (displacement F floor s) r floor cap H
    (actualSelect m τ L r floor cap H b reply s seeds)

lemma repairedSelect_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (F : E → ℝ) (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    (Set.range (repairedSelect m F τ L r floor cap H b reply s)).Finite :=
  repair_finite_range _ _ _ _ _ _ (actualSelect_finite_range m τ L r floor cap H b reply s)

lemma repairedSelect_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E}
    (F : E → ℝ) (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    Measurable (repairedSelect m F τ L r floor cap H b reply s) :=
  repair_measurable_finite _ _ _ _ _ _ (actualSelect_finite_range m τ L r floor cap H b reply s)
    (actualSelect_measurable m τ L r floor cap H b reply s)

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
      (repairedSelect m F τ L r floor cap H b reply s seeds) := by
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

lemma actualSelect_certificate_failure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (f : Fin m → E → ℝ) (s : StateSpace X)
    {τ L G r floor cap D : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap)
    (hdiam : ‖(state s).dual - (state s).primal‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ X → y ∈ X → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ X → ‖gradient (f i) x‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (H b : ℕ) (hcap : 2 * G / r ≤ cap) (hend : cap / 2 ^ H ≤ floor)
    (hwidth : (2 * D + G / floor) / 2 ^ (H + 7) < r / 64) :
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | ¬ AffineSoftmaxSearchCoupling.Certificate
        (displacement (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) floor s)
        r floor cap (actualSelect m τ L r floor cap H b reply s seeds)} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ b) := by
  have h := AffineResidualSearchTrace.regularizationSearchPlan_failure m hX hcompact f (state s)
    s.property.1 s.property.2.1 s.property.2.2 hτ hL hG hr hf hfc hdiam
    hc hg hlip hbound reply hreply H b hcap hend hwidth
  apply le_trans (measure_mono ?_) h
  intro seeds hbad hgood
  apply hbad
  simpa only [AffineSoftmaxSearchCoupling.Certificate, displacement, actualSelect,
    max_eq_right hgood.1.1] using hgood

lemma actual_bad_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (F : E → ℝ) (τ L r floor cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (s : StateSpace X) :
    MeasurableSet {seeds | ¬ AffineSoftmaxSearchCoupling.Certificate (displacement F floor s)
      r floor cap (actualSelect m τ L r floor cap H b reply s seeds)} := by
  classical
  let indicator := fun μ => if ¬ AffineSoftmaxSearchCoupling.Certificate
    (displacement F floor s) r floor cap μ then (1 : ℝ) else 0
  have hm : Measurable (fun seeds => indicator (actualSelect m τ L r floor cap H b reply s seeds)) :=
    measurable_dependent_finite _ (fun μ _ => indicator μ)
      (actualSelect_measurable m τ L r floor cap H b reply s)
      (actualSelect_finite_range m τ L r floor cap H b reply s) (fun _ => measurable_const)
  have he := measurableSet_eq_fun hm (measurable_const (a := (1 : ℝ)))
  simpa only [indicator, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using he

lemma actual_path_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (D ε : ℝ) {τ L r floor cap : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ) (hH : 0 < H)
    (reply : Fin m × E → ℝ × E) (seeds : ℕ → OuterSeed) (n : ℕ) :
    let select := actualSelect (X := X) m τ L r floor cap H b reply
    let step := transition m hX hcompact D ε hτ hL hr select
      (fun s seeds => hf.trans_le (actualSelect_mem m τ L r hf.le hfc H b reply s seeds).1) H hH reply
    state (AffineSoftmaxSearchCoupling.path step (lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩) seeds n) =
      Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n) := by
  classical
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [AffineSoftmaxSearchCoupling.path, state_transition, actualSelect]
    rw [ih]
    simp only [outerRunPlan, Program.eval_bind, outerStepPlan]
    split_ifs <;> simp only [Program.eval_bind, Program.eval]

lemma transition_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select other : StateSpace X → (ℕ → ProbeSeed) → ℝ)
    (hs : ∀ s seeds, 0 < select s seeds) (ho : ∀ s seeds, 0 < other s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed)
    (he : select s seed.1 = other s seed.1) :
    transition m hX hcompact D ε hτ hL hr select hs H hH reply s seed =
      transition m hX hcompact D ε hτ hL hr other ho H hH reply s seed := by
  apply AffineSoftmaxOuterProcess.state_injective
  simp only [state_transition, he]

lemma selector_coupling_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select other : StateSpace X → (ℕ → ProbeSeed) → ℝ)
    (hs : ∀ s seeds, 0 < select s seeds) (ho : ∀ s seeds, 0 < other s seeds)
    (hmo : ∀ s, Measurable (other s)) (hfinite : ∀ s, (Set.range (other s)).Finite)
    (H : ℕ) (hH : 0 < H)
    (reply : Fin m × E → ℝ × E)
    (bad : StateSpace X → (ℕ → ProbeSeed) → Prop)
    (hbad : ∀ s, MeasurableSet {seeds | bad s seeds})
    (he : ∀ s seeds, ¬ bad s seeds → select s seeds = other s seeds)
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ s, (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | bad s seeds} ≤ ENNReal.ofReal p)
    (initial : StateSpace X) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))
      {seeds | AffineSoftmaxSearchCoupling.path
        (transition m hX hcompact D ε hτ hL hr select hs H hH reply) initial seeds n ≠
        AffineSoftmaxSearchCoupling.path
        (transition m hX hcompact D ε hτ hL hr other ho H hH reply) initial seeds n} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  apply coupling_failure_finite outerLaw _ _
    (transition_measurable_finite m hX hcompact D ε hτ hL hr other ho hfinite hmo H hH reply)
    (transition_finite_range m hX hcompact D ε hτ hL hr other ho hfinite H hH reply)
    (fun s seed => bad s seed.1)
    (fun s => (hbad s).preimage measurable_fst)
    (fun s seed h => transition_congr m hX hcompact D ε hτ hL hr select other hs ho H hH reply s seed (he s seed.1 h)) hp
    _ initial n
  intro s
  change ((Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))).prod
    (finalLaw : Measure FinalSeed)) {seed | bad s seed.1} ≤ ENNReal.ofReal p
  rw [show {seed : OuterSeed | bad s seed.1} = {seeds | bad s seeds} ×ˢ Set.univ by ext seed; simp]
  simpa only [Measure.prod_prod, measure_univ, mul_one] using hb s

end LongTails.Proofs.AffineResidualOuterProcess
