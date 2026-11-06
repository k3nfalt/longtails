import LongTails.Proofs.NondualProjection
import LongTails.Proofs.ExtragradientStep
import LongTails.Proofs.ClippedTwoPointExecution
import LongTails.Algorithms.AffineSoftmaxAcceleration
import LongTails.Proofs.AffineSoftmaxExecution
import LongTails.Proofs.ConstrainedStochasticAcceleration
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxAcceleration

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.AffineSoftmaxAcceleration
open LongTails.Algorithms.ClippedTwoPoint (acceleratedMix acceleratedUpdate)
open OracleTemplate.ComponentEnvelope

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma solverPlan_eval [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ D μ : ℝ)
    (project : E → E) (initial : E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (n : ℕ) :
    Program.eval reply (solverPlan s τ D μ project initial seeds n) =
      solverState D project (fun x seed => Program.eval reply (seededEstimatorPlan s τ x seed) +
        μ • (x - s.anchor)) initial seeds n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [solverPlan, Program.eval_bind, Program.eval_map, ih, solverState]

lemma solverPlan_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ D μ : ℝ)
    (project : E → E) (initial : E) (seeds : ℕ → StepSeed)
    (reply : ι × E → ℝ × E) (n : ℕ) :
    Program.cost reply (solverPlan s τ D μ project initial seeds n) =
      ∑ k ∈ Finset.range n, ((seeds k).1 + 1) := by
  induction n with
  | zero => simp [solverPlan, Program.cost]
  | succ n ih =>
    simp only [solverPlan, Program.cost_bind, Program.cost_map,
      AffineSoftmaxExecution.seededEstimatorPlan_cost, ih, Finset.sum_range_succ]

lemma solverState_prefix (D : ℝ) (project : E → E) (G : E → StepSeed → E)
    (initial : E) (n : ℕ) (ξ ξ' : ℕ → StepSeed)
    (hprefix : ∀ k, k < n → ξ k = ξ' k) :
    solverState D project G initial ξ n = solverState D project G initial ξ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := ih (fun k hk => hprefix k (by omega))
    simp only [solverState, hh, hprefix n (by omega)]


lemma solverState_mem {C : Set E} (hC : Convex ℝ C) {project : E → E}
    (hp : ∀ x, project x ∈ C) (D : ℝ) (G : E → StepSeed → E)
    {initial : E} (hinit : initial ∈ C) (seeds : ℕ → StepSeed) (n : ℕ) :
    (solverState D project G initial seeds n).1 ∈ C ∧
      (solverState D project G initial seeds n).2 ∈ C := by
  induction n with
  | zero => exact ⟨hinit, hinit⟩
  | succ n ih =>
    exact ClippedTwoPointExecution.accelerated_update_mem hC hp ih.1 _ _ _

lemma solverState_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (D : ℝ) {project : E → E} (hp : Continuous project) (G : E → StepSeed → E)
    (hG : Measurable (Function.uncurry G)) (initial : E) (n : ℕ) :
    Measurable (fun seeds : ℕ → StepSeed => solverState D project G initial seeds n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hc := (ClippedTwoPointExecution.accelerated_mix_continuous n).measurable.comp ih
    have hg := hG.comp (hc.prodMk (measurable_pi_apply n))
    exact (ClippedTwoPointExecution.accelerated_update_continuous hp (2 * D) n).measurable.comp
      (ih.prodMk hg)

lemma solver_query_mem {C : Set E} (hC : Convex ℝ C) {project : E → E}
    (hp : ∀ x, project x ∈ C) (D : ℝ) (G : E → StepSeed → E)
    {initial : E} (hinit : initial ∈ C) (seeds : ℕ → StepSeed) (n : ℕ) :
    acceleratedMix n (solverState D project G initial seeds n).1
      (solverState D project G initial seeds n).2 ∈ C := by
  have hh := solverState_mem hC hp D G hinit seeds n
  exact ClippedTwoPointExecution.accelerated_mix_mem hC hh.1 hh.2 n


noncomputable def energy (f : E → ℝ) (u : E) (D : ℝ) (n : ℕ) (state : E × E) : ℝ :=
  (n : ℝ) * (n + 1) / 4 * (f state.1 - f u) + D / 2 * ‖state.2 - u‖ ^ 2

lemma projected_update_energy [CompleteSpace E] {C : Set E} (hc : Convex ℝ C)
    (hcompact : IsCompact C) {f : E → ℝ} {L D : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hf : ConvexOn ℝ C f)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {state : E × E} (hx : state.1 ∈ C) (hz : state.2 ∈ C)
    {u : E} (hu : u ∈ C) (t : ℕ) (g : E) :
    let y := acceleratedMix t state.1 state.2
    let next := acceleratedUpdate (OracleTemplate.SaddlePoint.project C) (2 * D) t state g
    energy f u D (t + 1) next ≤ energy f u D t state +
      ((t : ℝ) + 1) / 2 * ⟪gradient f y - g, state.2 - u⟫ +
      (((t : ℝ) + 1) / 2) ^ 2 * ‖gradient f y - g‖ ^ 2 / D := by
  let A : ℝ := (t : ℝ) * (t + 1) / 4
  let a : ℝ := ((t : ℝ) + 1) / 2
  let p := OracleTemplate.SaddlePoint.project C (state.2 - (a / D) • g)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : 0 < A + a := by dsimp [A, a]; positivity
  have hab : a ^ 2 ≤ A + a := by dsimp [A, a]; nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hp : p ∈ C := (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc _).1
  have hproj := OracleTemplate.SaddlePoint.project_inequality ⟨u, hu⟩ hcompact hc (a / D) state.2 g u hu
  have hpr : a * ⟪g, p - u⟫ ≤ D / 2 *
      (‖state.2 - u‖ ^ 2 - ‖p - u‖ ^ 2 - ‖p - state.2‖ ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hproj (show 0 ≤ D / 2 by positivity)
    change D / 2 * (2 * (a / D) * ⟪g, p - u⟫) ≤ _ at hh
    have he : D / 2 * (2 * (a / D) * ⟪g, p - u⟫) = a * ⟪g, p - u⟫ := by field_simp
    rw [he, norm_sub_rev state.2 p] at hh
    exact hh
  have hm (x z : E) : (A / (A + a)) • x + (a / (A + a)) • z = acceleratedMix t x z := by
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    have ht2 : (t : ℝ) + 2 ≠ 0 := by positivity
    have he1 : A / (A + a) = (t : ℝ) / (t + 2) := by dsimp [A, a]; field_simp; ring
    have he2 : a / (A + a) = 2 / (t + 2 : ℝ) := by dsimp [A, a]; field_simp; ring
    rw [he1, he2]
    rfl
  have hs := ConstrainedStochasticAcceleration.projected_energy_step hL hD hLD hf hg hlip
    state.1 state.2 u g p hx hz hu hp hA ha hB hab hpr
  dsimp only at hs
  rw [hm, hm] at hs
  have heta : ((t : ℝ) + 1) / (2 * D) = a / D := by dsimp [a]; ring
  have hweight : A + a = ((t : ℝ) + 1) * (t + 2) / 4 := by dsimp [A, a]; ring
  simp only [acceleratedUpdate, heta]
  dsimp only [energy]
  simp only [Nat.cast_add, Nat.cast_one]
  simpa only [hweight, A, a, p, add_assoc, one_add_one_eq_two] using hs

omit [InnerProductSpace ℝ E] in
lemma energy_nonneg {C : Set E} {f : E → ℝ} {u : E} {D : ℝ}
    (hD : 0 ≤ D) (hmin : ∀ x ∈ C, f u ≤ f x) (n : ℕ)
    {state : E × E} (hx : state.1 ∈ C) : 0 ≤ energy f u D n state := by
  unfold energy
  exact add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hmin _ hx)))
    (mul_nonneg (by positivity) (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
lemma energy_continuousOn {C : Set E} {f : E → ℝ} (hf : ContinuousOn f C)
    (u : E) (D : ℝ) (n : ℕ) : ContinuousOn (energy f u D n) (C ×ˢ C) := by
  have hx : ContinuousOn (fun state : E × E => f state.1) (C ×ˢ C) :=
    hf.comp continuous_fst.continuousOn (fun _ h => h.1)
  exact ((hx.sub continuousOn_const).const_mul _).add
    ((((continuous_snd.sub continuous_const).norm.pow 2).continuousOn).const_mul _)

lemma solver_energy_integrable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : ProbabilityMeasure (ℕ → StepSeed))
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} (hf : ContinuousOn f C) {project : E → E}
    (hp : Continuous project) (hpC : ∀ x, project x ∈ C)
    (D : ℝ) (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G))
    {initial : E} (hinit : initial ∈ C) (u : E) (n : ℕ) :
    Integrable (fun seeds => energy f u D n (solverState D project G initial seeds n))
      (P : Measure (ℕ → StepSeed)) := by
  apply ConstrainedStochasticAcceleration.integrable_compact_image P (hcompact.prod hcompact)
    (energy f u D n) (energy_continuousOn hf u D n)
    (fun seeds => solverState D project G initial seeds n)
    (solverState_measurable D hp G hG initial n)
  intro seeds
  exact solverState_mem hc hpC D G hinit seeds n

lemma expected_projected_update_energy [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} {L D V : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {state : E × E} (hx : state.1 ∈ C) (hz : state.2 ∈ C)
    {u : E} (hu : u ∈ C) (t : ℕ) (g : Ω → E) (hgm : Measurable g)
    (hgi : Integrable g (P : Measure Ω))
    (hmean : (∫ ω, g ω ∂(P : Measure Ω)) = gradient f (acceleratedMix t state.1 state.2))
    (hei : Integrable (fun ω => ‖gradient f (acceleratedMix t state.1 state.2) - g ω‖ ^ 2)
      (P : Measure Ω))
    (hvar : (∫ ω, ‖gradient f (acceleratedMix t state.1 state.2) - g ω‖ ^ 2
      ∂(P : Measure Ω)) ≤ V) :
    (∫ ω, energy f u D (t + 1)
      (acceleratedUpdate (OracleTemplate.SaddlePoint.project C) (2 * D) t state (g ω))
      ∂(P : Measure Ω)) ≤ energy f u D t state + (((t : ℝ) + 1) / 2) ^ 2 / D * V := by
  have hp : ∀ x, OracleTemplate.SaddlePoint.project C x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc := (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  have hnext : Measurable (fun ω =>
      acceleratedUpdate (OracleTemplate.SaddlePoint.project C) (2 * D) t state (g ω)) :=
    (ClippedTwoPointExecution.accelerated_update_continuous hpc (2 * D) t).measurable.comp
      (measurable_const.prodMk hgm)
  have henergy := ConstrainedStochasticAcceleration.integrable_compact_image P
    (hcompact.prod hcompact) (energy f u D (t + 1)) (energy_continuousOn hfc u D (t + 1))
    _ hnext (fun ω => ClippedTwoPointExecution.accelerated_update_mem hc hp hx _ _ _)
  have he : Integrable (fun ω => gradient f (acceleratedMix t state.1 state.2) - g ω)
      (P : Measure Ω) := (integrable_const _).sub hgi
  have hzero : (∫ ω, gradient f (acceleratedMix t state.1 state.2) - g ω
      ∂(P : Measure Ω)) = 0 := by
    rw [integral_sub (integrable_const _) hgi, hmean]
    simp
  apply ConstrainedStochasticAcceleration.integrate_projected_energy P _ _ (state.2 - u)
    hD henergy he hei hzero hvar
  intro ω
  simpa only [div_mul_eq_mul_div] using
    projected_update_energy hc hcompact hL hD hLD hf hg hlip hx hz hu t (g ω)

lemma solver_energy_step [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (p : ProbabilityMeasure StepSeed)
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} {L D V : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : u ∈ C) (hmin : ∀ x ∈ C, f u ≤ f x)
    (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G))
    (hGi : ∀ x ∈ C, Integrable (G x) (p : Measure StepSeed))
    (hmean : ∀ x ∈ C, (∫ ω, G x ω ∂(p : Measure StepSeed)) = gradient f x)
    (hei : ∀ x ∈ C, Integrable (fun ω => ‖gradient f x - G x ω‖ ^ 2) (p : Measure StepSeed))
    (hvar : ∀ x ∈ C, (∫ ω, ‖gradient f x - G x ω‖ ^ 2 ∂(p : Measure StepSeed)) ≤ V)
    {initial : E} (hinit : initial ∈ C) (t : ℕ) :
    let P := Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed)
    let state := fun seeds n => solverState D (OracleTemplate.SaddlePoint.project C) G initial seeds n
    (∫ seeds, energy f u D (t + 1) (state seeds (t + 1)) ∂P) ≤
      (∫ seeds, energy f u D t (state seeds t) ∂P) + (((t : ℝ) + 1) / 2) ^ 2 / D * V := by
  let P : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed), inferInstance⟩
  let project := OracleTemplate.SaddlePoint.project C
  have hp : ∀ x, project x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc : Continuous project :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  let Y := ↥(C ×ˢ C)
  let X : (ℕ → StepSeed) → Y := fun seeds =>
    ⟨solverState D project G initial seeds t, solverState_mem hc hp D G hinit seeds t⟩
  have hX : Measurable X := (solverState_measurable D hpc G hG initial t).subtype_mk
  have hdep : ∀ ξ ξ', (∀ i, i < t → ξ i = ξ' i) → X ξ = X ξ' := by
    intro ξ ξ' hh
    apply Subtype.ext
    exact solverState_prefix D project G initial t ξ ξ' hh
  let update : Y × StepSeed → E × E := fun z =>
    acceleratedUpdate project (2 * D) t z.1.val (G (acceleratedMix t z.1.val.1 z.1.val.2) z.2)
  have hstate : Measurable (fun z : Y × StepSeed => z.1.val) := measurable_subtype_coe.comp measurable_fst
  have hquery := (ClippedTwoPointExecution.accelerated_mix_continuous t).measurable.comp hstate
  have hupdate : Measurable update :=
    (ClippedTwoPointExecution.accelerated_update_continuous hpc (2 * D) t).measurable.comp
      (hstate.prodMk (hG.comp (hquery.prodMk measurable_snd)))
  have hupdate_mem : ∀ z, update z ∈ C ×ˢ C := fun z =>
    ClippedTwoPointExecution.accelerated_update_mem hc hp z.1.property.1 _ _ _
  let Φ : Y → StepSeed → ℝ := fun z seed => energy f u D (t + 1) (update (z, seed))
  have hΦ : Measurable (Function.uncurry Φ) :=
    (energy_continuousOn hfc u D (t + 1)).domRestrict.measurable.comp
      (hupdate.subtype_mk (h := hupdate_mem))
  have henergy := solver_energy_integrable P hc hcompact hfc hpc hp D G hG hinit u (t + 1)
  have htower := OracleTemplate.TwoSidedPL.integral_prefix_dep (p : Measure StepSeed) t X hX hdep Φ hΦ henergy
  have hbound : ∀ z : Y, (∫ seed, Φ z seed ∂(p : Measure StepSeed)) ≤
      energy f u D t z.val + (((t : ℝ) + 1) / 2) ^ 2 / D * V := by
    intro z
    have hq := ClippedTwoPointExecution.accelerated_mix_mem hc z.property.1 z.property.2 t
    exact expected_projected_update_energy p hc hcompact hL hD hLD hf hfc hg hlip
      z.property.1 z.property.2 hu t (G (acceleratedMix t z.val.1 z.val.2))
      (hG.comp ((measurable_const (a := acceleratedMix t z.val.1 z.val.2)).prodMk measurable_id))
      (hGi _ hq) (hmean _ hq) (hei _ hq) (hvar _ hq)
  have hecurrent := solver_energy_integrable P hc hcompact hfc hpc hp D G hG hinit u t
  change (∫ seeds, Φ (X seeds) (seeds t) ∂(P : Measure (ℕ → StepSeed))) ≤ _
  change (∫ seeds, Φ (X seeds) (seeds t) ∂(P : Measure (ℕ → StepSeed))) =
    (∫ seeds, (∫ seed, Φ (X seeds) seed ∂(p : Measure StepSeed)) ∂(P : Measure (ℕ → StepSeed))) at htower
  rw [htower]
  have hi := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun seeds => integral_nonneg (fun seed =>
      energy_nonneg hD.le hmin (t + 1) (hupdate_mem (X seeds, seed)).1)))
    (hecurrent.add (integrable_const ((((t : ℝ) + 1) / 2) ^ 2 / D * V)))
    (Filter.Eventually.of_forall (fun seeds => hbound (X seeds)))
  simp only [Pi.add_apply] at hi
  rw [integral_add hecurrent (integrable_const _), integral_const] at hi
  simpa only [probReal_univ, one_smul, P, ProbabilityMeasure.coe_mk, project, Φ] using hi

lemma solver_rate [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (p : ProbabilityMeasure StepSeed)
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} {L D V : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hV : 0 ≤ V)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : u ∈ C) (hmin : ∀ x ∈ C, f u ≤ f x)
    (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G))
    (hGi : ∀ x ∈ C, Integrable (G x) (p : Measure StepSeed))
    (hmean : ∀ x ∈ C, (∫ ω, G x ω ∂(p : Measure StepSeed)) = gradient f x)
    (hei : ∀ x ∈ C, Integrable (fun ω => ‖gradient f x - G x ω‖ ^ 2) (p : Measure StepSeed))
    (hvar : ∀ x ∈ C, (∫ ω, ‖gradient f x - G x ω‖ ^ 2 ∂(p : Measure StepSeed)) ≤ V)
    {initial : E} (hinit : initial ∈ C) {n : ℕ} (hn : 0 < n) :
    (∫ seeds, f (solverOutput D (OracleTemplate.SaddlePoint.project C) G initial seeds n) - f u
      ∂(Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed))) ≤
      2 * D * ‖initial - u‖ ^ 2 / ((n : ℝ) * (n + 1)) + (n : ℝ) * V / D := by
  let P : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed), inferInstance⟩
  let project := OracleTemplate.SaddlePoint.project C
  let state := fun seeds k => solverState D project G initial seeds k
  let e := fun k => ∫ seeds, energy f u D k (state seeds k) ∂(P : Measure (ℕ → StepSeed))
  have hp : ∀ x, project x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc : Continuous project :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  have heinit : e 0 ≤ D / 2 * ‖initial - u‖ ^ 2 := by
    simp [e, state, solverState, energy]
  have hstep : ∀ k, e (k + 1) ≤ e k + (((k : ℝ) + 1) / 2) ^ 2 * V / D := by
    intro k
    simpa only [e, P, ProbabilityMeasure.coe_mk, state, project, div_mul_eq_mul_div] using
      solver_energy_step p hc hcompact hL hD hLD hf hfc hg hlip hu hmin G hG hGi hmean hei hvar hinit k
  have hgap : (n : ℝ) * (n + 1) / 4 *
      (∫ seeds, f (state seeds n).1 - f u ∂(P : Measure (ℕ → StepSeed))) ≤ e n := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun seeds => mul_nonneg (by positivity)
        (sub_nonneg.mpr (hmin _ (solverState_mem hc hp D G hinit seeds n).1))))
      (solver_energy_integrable P hc hcompact hfc hpc hp D G hG hinit u n)
    apply Filter.Eventually.of_forall
    intro seeds
    dsimp [energy]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  exact ConstrainedStochasticAcceleration.rate_of_energy_recursion e hD hV heinit hstep hn hgap

lemma solverPlan_expected_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ D μ : ℝ)
    (project : E → E) (initial : E) (reply : ι × E → ℝ × E) (n : ℕ) :
    (∫ seeds : ℕ → StepSeed, (Program.cost reply (solverPlan s τ D μ project initial seeds n) : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed))) = 2 * n := by
  let c : StepSeed → ℝ := fun seed => ((seed.1 + 1 : ℕ) : ℝ)
  have hm : Measurable c := by unfold c; fun_prop
  have hmean : (∫ seed, c seed ∂(stepLaw : Measure StepSeed)) = 2 := by
    simpa only [AffineSoftmaxExecution.seededEstimatorPlan_cost] using
      AffineSoftmaxExecution.seededEstimatorPlan_expected_cost s τ initial reply
  have hi : Integrable c (stepLaw : Measure StepSeed) := by
    by_contra hn
    rw [integral_undef hn] at hmean
    norm_num at hmean
  have hpres k := measurePreserving_eval_infinitePi (fun _ : ℕ => (stepLaw : Measure StepSeed)) k
  have hki k : Integrable (fun seeds : ℕ → StepSeed => c (seeds k))
      (Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)) :=
    (hpres k).integrable_comp_of_integrable hi
  have hkmean k : (∫ seeds : ℕ → StepSeed, c (seeds k)
      ∂(Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed))) = 2 := by
    rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply k) hm.stronglyMeasurable,
      (hpres k).map_eq]
    exact hmean
  simp only [solverPlan_cost, Nat.cast_sum]
  change (∫ seeds : ℕ → StepSeed, ∑ k ∈ Finset.range n, c (seeds k)
    ∂(Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed))) = _
  rw [integral_finsetSum _ (fun k _ => hki k)]
  simp only [hkmean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma solverState_param_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Z : Type*} [MeasurableSpace Z]
    (D : Z → ℝ) (hD : Measurable D) (project : Z → E → E)
    (hp : Measurable (Function.uncurry project)) (G : Z → E → StepSeed → E)
    (hG : Measurable (fun w : Z × (E × StepSeed) => G w.1 w.2.1 w.2.2))
    (initial : Z → E) (hi : Measurable initial) (seeds : Z → ℕ → StepSeed)
    (hs : ∀ n, Measurable (fun z => seeds z n)) (n : ℕ) :
    Measurable (fun z => solverState (D z) (project z) (G z) (initial z) (seeds z) n) := by
  induction n with
  | zero => exact hi.prodMk hi
  | succ n ih =>
    have hq := (ClippedTwoPointExecution.accelerated_mix_continuous n).measurable.comp ih
    have hg := hG.comp (measurable_id.prodMk (hq.prodMk (hs n)))
    have hc : Measurable (fun z => ((n : ℝ) + 1) / (2 * D z)) :=
      measurable_const.div (measurable_const.mul hD)
    have hn := hp.comp (measurable_id.prodMk (ih.snd.sub (hc.smul hg)))
    exact ((ClippedTwoPointExecution.accelerated_mix_continuous n).measurable.comp
      (ih.fst.prodMk hn)).prodMk hn

end LongTails.Proofs.AffineSoftmaxAcceleration
