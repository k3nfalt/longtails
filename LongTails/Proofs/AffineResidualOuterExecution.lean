import LongTails.Algorithms.AffineResidualOuter
import LongTails.Proofs.AffineResidualSearchTrace
import LongTails.Proofs.AffineResidualMultilevel

namespace LongTails.Proofs.AffineResidualOuterExecution

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineResidualSaddle (localPlan)
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot)
open LongTails.Algorithms.CappedProximal

lemma finite_range_dependent {A B C : Type*} (f : A → B) (g : B → A → C)
    (hf : (Set.range f).Finite) (hg : ∀ b, (Set.range (g b)).Finite) :
    (Set.range (fun a => g (f a) a)).Finite := by
  apply (hf.biUnion (fun b _ => hg b)).subset
  rintro _ ⟨a, rfl⟩
  exact Set.mem_iUnion.mpr ⟨f a, Set.mem_iUnion.mpr ⟨⟨a, rfl⟩, ⟨a, rfl⟩⟩⟩

lemma measurable_dependent_finite {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass B] [MeasurableSpace C] (f : A → B) (g : B → A → C)
    (hf : Measurable f) (hfinite : (Set.range f).Finite) (hg : ∀ b, Measurable (g b)) :
    Measurable (fun a => g (f a) a) := by
  let : Countable (Set.range f) := hfinite.countable.to_subtype
  have hm : Measurable (fun z : Set.range f × A => g z.1 z.2) :=
    measurable_from_prod_countable_right (fun b => hg b)
  exact hm.comp ((hf.subtype_mk (h := fun a => ⟨a, rfl⟩)).prodMk measurable_id)

lemma integrable_observable_finite {A B Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass B] [NormedAddCommGroup Y] (f : A → B) (observe : B → Y)
    (hf : Measurable f) (hfinite : (Set.range f).Finite) (P : Measure A) [IsFiniteMeasure P] :
    Integrable (fun a => observe (f a)) P := by
  let : Finite (Set.range f) := hfinite.to_subtype
  let f' := fun a => (⟨f a, ⟨a, rfl⟩⟩ : Set.range f)
  have hm : Measurable f' := hf.subtype_mk
  have hi : Integrable (fun b : Set.range f => observe b) (P.map f') := Integrable.of_finite
  exact (integrable_map_measure StronglyMeasurable.of_discrete.aestronglyMeasurable hm.aemeasurable).1 hi

lemma finalStepPlan_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L r D ε μ : ℝ) (H : ℕ) (reply : Fin m × E → ℝ × E) :
    (Set.range (fun seed => Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed))).Finite := by
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let x := fun seed : LocalSeed => Program.eval reply
    (localPlan C s τ μ L r (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) seed)
  let g := fun seed : MultilevelSeed => Program.eval reply (cachedProxGradientPlan C s τ μ L r
    (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D)) seed)
  have hx : (Set.range x).Finite := AffineResidualLocal.localPlan_observable_finite_range C s τ μ L r _ reply id
  have hg : (Set.range g).Finite := AffineResidualMultilevel.cachedProxGradientPlan_finite_range C s τ μ L r reply _ _
  apply ((hx.prod hg).image (fun z : E × E => (⟨state.weight + nextWeight μ state.weight,
    z.1, OracleTemplate.SaddlePoint.project X (state.dual - (nextWeight μ state.weight / 2) • z.2)⟩ : State E))).subset
  rintro _ ⟨seed, rfl⟩
  refine ⟨(x seed.1, g seed.2), ⟨⟨seed.1, rfl⟩, ⟨seed.2, rfl⟩⟩, ?_⟩
  simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
  rfl

lemma outerStepPlan_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L r D ε floor cap : ℝ) (H b : ℕ) (reply : Fin m × E → ℝ × E) :
    (Set.range (fun seed => Program.eval reply (outerStepPlan m X state τ L r D ε floor cap H b seed))).Finite := by
  simp only [outerStepPlan, Program.eval_bind]
  apply finite_range_dependent
    (fun seed : OuterSeed => Program.eval reply (regularizationSearchPlan m X state τ L r floor cap H b seed.1))
    (fun μ seed => Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed.2))
  · unfold regularizationSearchPlan
    exact AffineResidualSearchTrace.searchPlan_finite_range
      (fun (seed : OuterSeed) i μ => probePlan m (X ∩ Metric.closedBall (predictor (max floor μ) state) r)
        (predictor (max floor μ) state) τ (max floor μ) L r (seed.1 i) b) reply r floor cap H
  · intro μ
    exact (finalStepPlan_finite_range m X state τ L r D ε μ H reply).subset
      (by rintro _ ⟨seed, rfl⟩; exact ⟨seed.2, rfl⟩)

lemma outerRunPlan_finite_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    (τ L r D ε floor cap : ℝ) (H b n : ℕ) (reply : Fin m × E → ℝ × E) :
    (Set.range (fun seeds => Program.eval reply
      (outerRunPlan m X initial τ L r D ε floor cap H b seeds n))).Finite := by
  induction n with
  | zero => exact Set.finite_range_const
  | succ n ih =>
      simp only [outerRunPlan, Program.eval_bind]
      apply finite_range_dependent
        (fun seeds : ℕ → OuterSeed => Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n))
        (fun state seeds => Program.eval reply (if 100 * D ^ 2 / ε ≤ state.weight then Program.done state
          else outerStepPlan m X state τ L r D ε floor cap H b (seeds n))) ih
      intro state
      by_cases hs : 100 * D ^ 2 / ε ≤ state.weight
      · simp only [hs, ite_true, Program.eval]
        exact Set.finite_range_const
      · simp only [hs, ite_false]
        exact (outerStepPlan_finite_range m X state τ L r D ε floor cap H b reply).subset
          (by rintro _ ⟨seeds, rfl⟩; exact ⟨seeds n, rfl⟩)

lemma finalStepPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (D ε : ℝ) {τ L r μ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hμ : 0 < μ)
    (H : ℕ) (hH : 0 < H) (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    let out := Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed)
    state.weight < out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  let a := nextWeight μ state.weight
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let x := Program.eval reply (localPlan C s τ μ L r (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) seed.1)
  let g := Program.eval reply (cachedProxGradientPlan C s τ μ L r
    (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D)) seed.2)
  have he : Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed) =
      (⟨state.weight + a, x, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g)⟩ : State E) := by
    simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
    rfl
  rw [he]
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr.le⟩
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hxC : x ∈ C := AffineResidualLocal.localPlan_mem C s τ μ
    (fun i z => (reply (i, z)).1) (fun i z => (reply (i, z)).2)
    hCcompact ⟨center, hcC⟩ hC hμ hτ hL (by positivity) seed.1
  have ha : 0 < a := (AffineSoftmaxPredictor.ratio_properties hμ hA).1
  exact ⟨by dsimp; linarith, hxC.1,
    (OracleTemplate.SaddlePoint.project_spec ⟨state.primal, hx⟩ hcompact hX _).1⟩

lemma finalStepPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (state : State E) (τ L r D ε μ : ℝ) (H : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seed => (Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed)).weight) ∧
      Measurable (fun seed => (Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed)).primal) ∧
      Measurable (fun seed => (Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed)).dual) := by
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  have hx := AffineResidualLocal.localPlan_observable_measurable C s τ μ L r
    (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) reply id
  have hg := AffineResidualMultilevel.cachedProxGradientPlan_measurable C s τ μ L r reply
    (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D))
  have hp := (NondualProjection.project_lipschitz hne hcompact hX).continuous.measurable
  simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
  exact ⟨measurable_const, hx.comp measurable_fst,
    hp.comp (measurable_const.sub ((hg.comp measurable_snd).const_smul (nextWeight μ state.weight / 2)))⟩

lemma outerStepPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (state : State E) (τ L r D ε floor cap : ℝ) (H b : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seed => (Program.eval reply (outerStepPlan m X state τ L r D ε floor cap H b seed)).weight) ∧
      Measurable (fun seed => (Program.eval reply (outerStepPlan m X state τ L r D ε floor cap H b seed)).primal) ∧
      Measurable (fun seed => (Program.eval reply (outerStepPlan m X state τ L r D ε floor cap H b seed)).dual) := by
  let μ := fun seed : OuterSeed => Program.eval reply
    (regularizationSearchPlan m X state τ L r floor cap H b seed.1)
  have hm : Measurable μ := (AffineResidualSearchTrace.regularizationSearchPlan_measurable
    m X state τ L r floor cap H b reply).comp measurable_fst
  have hf : (Set.range μ).Finite := by
    dsimp only [μ, regularizationSearchPlan]
    exact AffineResidualSearchTrace.searchPlan_finite_range
      (fun (seed : OuterSeed) i ν => probePlan m (X ∩ Metric.closedBall (predictor (max floor ν) state) r)
        (predictor (max floor ν) state) τ (max floor ν) L r (seed.1 i) b) reply r floor cap H
  have hfin ν := finalStepPlan_measurable m hX hcompact hne state τ L r D ε ν H reply
  have hA := measurable_dependent_finite μ
    (fun ν seed => (Program.eval reply (finalStepPlan m X state τ L r D ε ν H seed.2)).weight)
    hm hf (fun ν => (hfin ν).1.comp measurable_snd)
  have hx := measurable_dependent_finite μ
    (fun ν seed => (Program.eval reply (finalStepPlan m X state τ L r D ε ν H seed.2)).primal)
    hm hf (fun ν => (hfin ν).2.1.comp measurable_snd)
  have hv := measurable_dependent_finite μ
    (fun ν seed => (Program.eval reply (finalStepPlan m X state τ L r D ε ν H seed.2)).dual)
    hm hf (fun ν => (hfin ν).2.2.comp measurable_snd)
  simpa only [outerStepPlan, Program.eval_bind, μ] using And.intro hA (And.intro hx hv)

lemma outerRunPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (initial : E) (τ L r D ε floor cap : ℝ) (H b n : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds => (Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)).weight) ∧
      Measurable (fun seeds => (Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)).primal) ∧
      Measurable (fun seeds => (Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)).dual) := by
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
      let run := fun seeds : ℕ → OuterSeed => Program.eval reply
        (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)
      let encode := fun state : State E => (state.weight, state.primal, state.dual)
      let f := fun seeds => encode (run seeds)
      let decode := fun z : ℝ × E × E => (⟨z.1, z.2.1, z.2.2⟩ : State E)
      let next := fun (z : ℝ × E × E) (seeds : ℕ → OuterSeed) =>
        if 100 * D ^ 2 / ε ≤ z.1 then decode z else
          Program.eval reply (outerStepPlan m X (decode z) τ L r D ε floor cap H b (seeds n))
      have hf : Measurable f := ih.1.prodMk (ih.2.1.prodMk ih.2.2)
      have hfinite : (Set.range f).Finite :=
        ((outerRunPlan_finite_range m X initial τ L r D ε floor cap H b n reply).image encode).subset
          (by rintro _ ⟨seeds, rfl⟩; exact ⟨run seeds, ⟨seeds, rfl⟩, rfl⟩)
      have hn z : Measurable (fun seeds => (next z seeds).weight) ∧
          Measurable (fun seeds => (next z seeds).primal) ∧ Measurable (fun seeds => (next z seeds).dual) := by
        by_cases hs : 100 * D ^ 2 / ε ≤ z.1
        · simp only [next, hs, ite_true]
          exact ⟨measurable_const, measurable_const, measurable_const⟩
        · simp only [next, hs, ite_false]
          have hh := outerStepPlan_measurable m hX hcompact hne (decode z) τ L r D ε floor cap H b reply
          exact ⟨hh.1.comp (measurable_pi_apply n), hh.2.1.comp (measurable_pi_apply n),
            hh.2.2.comp (measurable_pi_apply n)⟩
      have hA := measurable_dependent_finite f (fun z seeds => (next z seeds).weight) hf hfinite (fun z => (hn z).1)
      have hx := measurable_dependent_finite f (fun z seeds => (next z seeds).primal) hf hfinite (fun z => (hn z).2.1)
      have hv := measurable_dependent_finite f (fun z seeds => (next z seeds).dual) hf hfinite (fun z => (hn z).2.2)
      have he seeds : Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds (n + 1)) =
          next (f seeds) seeds := by
        simp only [outerRunPlan, Program.eval_bind, next, f, encode, decode, run]
        split_ifs <;> rfl
      simp_rw [he]
      exact ⟨hA, hx, hv⟩

lemma outerRunPlan_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L r D ε floor cap : ℝ) (H b n : ℕ)
    (reply : Fin m × E → ℝ × E) (seeds other : ℕ → OuterSeed)
    (hp : ∀ i, i < n → seeds i = other i) :
    Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n) =
      Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b other n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [outerRunPlan, Program.eval_bind, ih (fun i hi => hp i (by omega)), hp n (Nat.lt_succ_self n)]

lemma outerRunPlan_observable_integrable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup Y]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty)
    (initial : E) (τ L r D ε floor cap : ℝ) (H b n : ℕ) (reply : Fin m × E → ℝ × E)
    (observe : State E → Y) (P : Measure (ℕ → OuterSeed)) [IsFiniteMeasure P] :
    Integrable (fun seeds => observe (Program.eval reply
      (outerRunPlan m X initial τ L r D ε floor cap H b seeds n))) P := by
  let run := fun seeds : ℕ → OuterSeed => Program.eval reply
    (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)
  let encode := fun state : State E => (state.weight, state.primal, state.dual)
  let f := fun seeds => encode (run seeds)
  have hm := outerRunPlan_measurable m hX hcompact hne initial τ L r D ε floor cap H b n reply
  have hf : Measurable f := hm.1.prodMk (hm.2.1.prodMk hm.2.2)
  have hfinite : (Set.range f).Finite :=
    ((outerRunPlan_finite_range m X initial τ L r D ε floor cap H b n reply).image encode).subset
      (by rintro _ ⟨seeds, rfl⟩; exact ⟨run seeds, ⟨seeds, rfl⟩, rfl⟩)
  exact integrable_observable_finite f (fun z => observe ⟨z.1, z.2.1, z.2.2⟩) hf hfinite P

lemma outerStepPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (D ε : ℝ) {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (hH : 0 < H) (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    let out := Program.eval reply (outerStepPlan m X state τ L r D ε floor cap H b seed)
    state.weight < out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  let μ := Program.eval reply (regularizationSearchPlan m X state τ L r floor cap H b seed.1)
  have hμrange : μ ∈ Set.Icc floor cap := by
    dsimp only [μ, regularizationSearchPlan]
    exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  have hμ : 0 < μ := hf.trans_le hμrange.1
  simpa only [outerStepPlan, Program.eval_bind, μ] using
    finalStepPlan_feasible m hX hcompact state hA hx hv D ε hτ hL hr hμ H hH seed.2 reply

lemma outerRunPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (D ε : ℝ)
    {τ L r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (hH : 0 < H) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (n : ℕ) :
    let out := Program.eval reply (outerRunPlan m X initial τ L r D ε floor cap H b seeds n)
    0 ≤ out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  induction n with
  | zero => exact ⟨le_rfl, hi, hi⟩
  | succ n ih =>
    simp only [outerRunPlan, Program.eval_bind]
    split_ifs
    · exact ih
    · have hs := outerStepPlan_feasible m hX hcompact _ ih.1 ih.2.1 ih.2.2 D ε hτ hL hr hf hfc H b hH (seeds n) reply
      exact ⟨ih.1.trans hs.1.le, hs.2⟩

end LongTails.Proofs.AffineResidualOuterExecution
