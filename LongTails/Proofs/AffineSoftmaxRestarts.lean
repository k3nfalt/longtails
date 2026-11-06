import LongTails.Proofs.AffineSoftmaxAcceleration
import LongTails.Proofs.AffineSoftmaxRegularization
import LongTails.Proofs.AffineSoftmaxMeasurability
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxRestarts

open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.AffineSoftmaxAcceleration
open LongTails.Proofs.AffineSoftmaxAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma solver_random_start_rate [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω)
    (p : ProbabilityMeasure StepSeed)
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
    (initial : Ω → E) (him : Measurable initial) (hinit : ∀ ω, initial ω ∈ C)
    {n : ℕ} (hn : 0 < n) :
    (∫ z : Ω × (ℕ → StepSeed),
      f (solverOutput D (OracleTemplate.SaddlePoint.project C) G (initial z.1) z.2 n) - f u
      ∂(Q : Measure Ω).prod (Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed))) ≤
      2 * D * (∫ ω, ‖initial ω - u‖ ^ 2 ∂(Q : Measure Ω)) / ((n : ℝ) * (n + 1)) +
        (n : ℝ) * V / D := by
  let P : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed), inferInstance⟩
  let W : ProbabilityMeasure (Ω × (ℕ → StepSeed)) :=
    ⟨(Q : Measure Ω).prod (P : Measure (ℕ → StepSeed)), inferInstance⟩
  let project := OracleTemplate.SaddlePoint.project C
  have hp : ∀ x, project x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc : Continuous project :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  let out := fun z : Ω × (ℕ → StepSeed) => solverOutput D project G (initial z.1) z.2 n
  have hm : Measurable out := by
    exact (solverState_param_measurable (fun _ : Ω × (ℕ → StepSeed) => D) measurable_const
      (fun _ => project) (hpc.measurable.comp measurable_snd) (fun _ => G)
      (hG.comp measurable_snd) (fun z => initial z.1) (him.comp measurable_fst)
      (fun z => z.2) (fun k => (measurable_pi_apply k).comp measurable_snd) n).fst
  have hmem : ∀ z, out z ∈ C := fun z => (solverState_mem hc hp D G (hinit z.1) z.2 n).1
  have hFi := ConstrainedStochasticAcceleration.integrable_compact_image W hcompact
    (fun x => f x - f u) (hfc.sub continuousOn_const) out hm hmem
  have hdi := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun x => ‖x - u‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    initial him hinit
  let a : ℝ := 2 * D / ((n : ℝ) * (n + 1))
  let b : ℝ := (n : ℝ) * V / D
  have hbnd (ω : Ω) : (∫ seeds, f (out (ω, seeds)) - f u ∂(P : Measure (ℕ → StepSeed))) ≤
      a * ‖initial ω - u‖ ^ 2 + b := by
    have hh := solver_rate p hc hcompact hL hD hLD hV hf hfc hg hlip hu hmin
      G hG hGi hmean hei hvar (hinit ω) hn
    simpa only [out, project, P, ProbabilityMeasure.coe_mk, a, b, div_mul_eq_mul_div] using hh
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => integral_nonneg (fun seeds =>
      sub_nonneg.mpr (hmin _ (hmem (ω, seeds))))))
    ((hdi.const_mul a).add (integrable_const b))
    (Filter.Eventually.of_forall hbnd)
  simp only [Pi.add_apply] at hle
  rw [integral_add (hdi.const_mul a) (integrable_const b), integral_const_mul, integral_const] at hle
  change (∫ z, f (out z) - f u ∂(W : Measure (Ω × (ℕ → StepSeed)))) ≤ _
  rw [show (W : Measure (Ω × (ℕ → StepSeed))) = (Q : Measure Ω).prod
    (P : Measure (ℕ → StepSeed)) from rfl, integral_prod _ hFi]
  simpa only [probReal_univ, one_smul, a, b, div_mul_eq_mul_div] using hle

lemma restartPlan_eval {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι]
    (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot ι E) (τ μ : ℝ)
    (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E) (initial : E)
    (seeds : ℕ → ℕ → StepSeed) (reply : ι × E → ℝ × E) (n : ℕ) :
    OracleTemplate.ComponentEnvelope.Program.eval reply (restartPlan s τ μ D steps project initial seeds n) =
      restartState D steps project (fun x seed => OracleTemplate.ComponentEnvelope.Program.eval reply
        (seededEstimatorPlan s τ x seed) + μ • (x - s.anchor)) initial seeds n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [restartPlan, OracleTemplate.ComponentEnvelope.Program.eval_bind,
      OracleTemplate.ComponentEnvelope.Program.eval_map, solverPlan_eval, ih, restartState, solverOutput]

lemma restartState_mem {C : Set E} (hc : Convex ℝ C) {project : E → E}
    (hp : ∀ x, project x ∈ C) (D : ℕ → ℝ) (steps : ℕ → ℕ)
    (G : E → StepSeed → E) {initial : E} (hi : initial ∈ C)
    (seeds : ℕ → ℕ → StepSeed) (n : ℕ) : restartState D steps project G initial seeds n ∈ C := by
  induction n with
  | zero => exact hi
  | succ n ih => exact (solverState_mem hc hp (D n) G ih (seeds n) (steps n)).1

lemma restartState_prefix (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E)
    (G : E → StepSeed → E) (initial : E) (n : ℕ) (ξ ξ' : ℕ → ℕ → StepSeed)
    (hprefix : ∀ k, k < n → ξ k = ξ' k) :
    restartState D steps project G initial ξ n = restartState D steps project G initial ξ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := ih (fun k hk => hprefix k (by omega))
    simp only [restartState, hh, hprefix n (by omega)]

lemma restartState_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (D : ℕ → ℝ) (steps : ℕ → ℕ) {project : E → E} (hp : Continuous project)
    (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G)) (initial : E) (n : ℕ) :
    Measurable (fun seeds : ℕ → ℕ → StepSeed => restartState D steps project G initial seeds n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (solverState_param_measurable (fun _ : ℕ → ℕ → StepSeed => D n) measurable_const
      (fun _ => project) (hp.measurable.comp measurable_snd) (fun _ => G)
      (hG.comp measurable_snd) _ ih (fun seeds => seeds n)
      (fun k => (measurable_pi_apply k).comp (measurable_pi_apply n)) (steps n)).fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma restartSteps_measurable {Z : Type*} [MeasurableSpace Z]
    (S V μ d : Z → ℝ) (hS : Measurable S) (hV : Measurable V)
    (hμ : Measurable μ) (hd : Measurable d) :
    Measurable (fun z => restartSteps (S z) (V z) (μ z) (d z)) := by
  exact (((hS.div hμ).sqrt.const_mul 8).add
    ((hV.const_mul 256).div (hμ.mul hd))).add_const 1 |>.nat_ceil

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma restartScale_measurable {Z : Type*} [MeasurableSpace Z]
    (S V μ d : Z → ℝ) (hS : Measurable S) (hV : Measurable V)
    (hμ : Measurable μ) (hd : Measurable d) :
    Measurable (fun z => restartScale (S z) (V z) (μ z) (d z)) := by
  exact (hS.const_mul 2).add
    (((((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (restartSteps_measurable S V μ d hS hV hμ hd)).const_mul 8).mul hV).div hd)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma restartRounds_measurable {Z : Type*} [MeasurableSpace Z]
    (d ε : Z → ℝ) (hd : Measurable d) (hε : Measurable ε) :
    Measurable (fun z => restartRounds (d z) (ε z)) := by
  exact (measurable_of_countable (Nat.clog 2)).comp (hd.div hε).nat_ceil

lemma restartState_param_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Z : Type*} [MeasurableSpace Z]
    (D : Z → ℕ → ℝ) (hD : ∀ j, Measurable (fun z => D z j))
    (steps : Z → ℕ → ℕ) (hsteps : ∀ j, Measurable (fun z => steps z j))
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (G : Z → E → StepSeed → E)
    (hG : Measurable (fun w : Z × (E × StepSeed) => G w.1 w.2.1 w.2.2))
    (initial : Z → E) (hi : Measurable initial)
    (seeds : Z → ℕ → ℕ → StepSeed)
    (hs : ∀ j k, Measurable (fun z => seeds z j k)) (n : ℕ) :
    Measurable (fun z => restartState (D z) (steps z) (project z)
      (G z) (initial z) (seeds z) n) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    have hm (k : ℕ) := (solverState_param_measurable (fun z => D z n) (hD n)
      project hp G hG _ ih (fun z => seeds z n) (hs n) k).fst
    exact AffineSoftmaxMeasurability.measurable_select _ hm _ (hsteps n)

lemma restartState_stopped_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Z : Type*} [MeasurableSpace Z]
    (D : Z → ℕ → ℝ) (hD : ∀ j, Measurable (fun z => D z j))
    (steps : Z → ℕ → ℕ) (hsteps : ∀ j, Measurable (fun z => steps z j))
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (G : Z → E → StepSeed → E)
    (hG : Measurable (fun w : Z × (E × StepSeed) => G w.1 w.2.1 w.2.2))
    (initial : Z → E) (hi : Measurable initial)
    (seeds : Z → ℕ → ℕ → StepSeed)
    (hs : ∀ j k, Measurable (fun z => seeds z j k))
    (n : Z → ℕ) (hn : Measurable n) :
    Measurable (fun z => restartState (D z) (steps z) (project z)
      (G z) (initial z) (seeds z) (n z)) := by
  exact AffineSoftmaxMeasurability.measurable_select _
    (restartState_param_measurable D hD steps hsteps project hp G hG initial hi seeds hs) n hn

lemma restartPlan_cost {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι]
    (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot ι E) (τ μ : ℝ)
    (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E) (initial : E)
    (seeds : ℕ → ℕ → StepSeed) (reply : ι × E → ℝ × E) (n : ℕ) :
    OracleTemplate.ComponentEnvelope.Program.cost reply (restartPlan s τ μ D steps project initial seeds n) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (steps j), ((seeds j k).1 + 1) := by
  induction n with
  | zero => simp [restartPlan, OracleTemplate.ComponentEnvelope.Program.cost]
  | succ n ih =>
    simp only [restartPlan, OracleTemplate.ComponentEnvelope.Program.cost_bind,
      OracleTemplate.ComponentEnvelope.Program.cost_map, solverPlan_cost, ih, Finset.sum_range_succ]

lemma restart_step_rate [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (p : ProbabilityMeasure StepSeed)
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} {L V : ℝ} (D : ℕ → ℝ) (steps : ℕ → ℕ) (t : ℕ)
    (hL : 0 ≤ L) (hD : 0 < D t) (hLD : 2 * L ≤ D t) (hV : 0 ≤ V)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : u ∈ C) (hmin : ∀ x ∈ C, f u ≤ f x)
    (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G))
    (hGi : ∀ x ∈ C, Integrable (G x) (p : Measure StepSeed))
    (hmean : ∀ x ∈ C, (∫ ω, G x ω ∂(p : Measure StepSeed)) = gradient f x)
    (hei : ∀ x ∈ C, Integrable (fun ω => ‖gradient f x - G x ω‖ ^ 2) (p : Measure StepSeed))
    (hvar : ∀ x ∈ C, (∫ ω, ‖gradient f x - G x ω‖ ^ 2 ∂(p : Measure StepSeed)) ≤ V)
    {initial : E} (hinit : initial ∈ C) (hn : 0 < steps t) :
    let P := Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed)
    let T := Measure.infinitePi fun _ : ℕ => P
    let state := fun seeds k => restartState D steps (OracleTemplate.SaddlePoint.project C) G initial seeds k
    (∫ seeds, f (state seeds (t + 1)) - f u ∂T) ≤
      2 * D t * (∫ seeds, ‖state seeds t - u‖ ^ 2 ∂T) / ((steps t : ℝ) * (steps t + 1)) +
        (steps t : ℝ) * V / D t := by
  let P : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed), inferInstance⟩
  let T : ProbabilityMeasure (ℕ → ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (P : Measure (ℕ → StepSeed)), inferInstance⟩
  let project := OracleTemplate.SaddlePoint.project C
  have hp : ∀ x, project x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc : Continuous project :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  let X : (ℕ → ℕ → StepSeed) → C := fun seeds =>
    ⟨restartState D steps project G initial seeds t, restartState_mem hc hp D steps G hinit seeds t⟩
  have hX : Measurable X := (restartState_measurable D steps hpc G hG initial t).subtype_mk
  have hdep : ∀ ξ ξ', (∀ k, k < t → ξ k = ξ' k) → X ξ = X ξ' := by
    intro ξ ξ' hh
    apply Subtype.ext
    exact restartState_prefix D steps project G initial t ξ ξ' hh
  let out := fun z : C × (ℕ → StepSeed) => solverOutput (D t) project G z.1.val z.2 (steps t)
  have hout : Measurable out :=
    (solverState_param_measurable (fun _ : C × (ℕ → StepSeed) => D t) measurable_const
      (fun _ => project) (hpc.measurable.comp measurable_snd) (fun _ => G)
      (hG.comp measurable_snd) (fun z => z.1.val) (measurable_subtype_coe.comp measurable_fst)
      (fun z => z.2) (fun k => (measurable_pi_apply k).comp measurable_snd) (steps t)).fst
  have hom : ∀ z, out z ∈ C := fun z => (solverState_mem hc hp (D t) G z.1.property z.2 (steps t)).1
  let Φ : C → (ℕ → StepSeed) → ℝ := fun x seeds => f (out (x, seeds)) - f u
  have hΦ : Measurable (Function.uncurry Φ) :=
    (hfc.domRestrict.measurable.comp (hout.subtype_mk (h := hom))).sub measurable_const
  have hint := ConstrainedStochasticAcceleration.integrable_compact_image T hcompact
    (fun x => f x - f u) (hfc.sub continuousOn_const)
    (fun seeds => restartState D steps project G initial seeds (t + 1))
    (restartState_measurable D steps hpc G hG initial (t + 1))
    (fun seeds => restartState_mem hc hp D steps G hinit seeds (t + 1))
  have htower := OracleTemplate.TwoSidedPL.integral_prefix_dep (P : Measure (ℕ → StepSeed)) t
    X hX hdep Φ hΦ hint
  have hdi := ConstrainedStochasticAcceleration.integrable_compact_image T hcompact
    (fun x => ‖x - u‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    (fun seeds => restartState D steps project G initial seeds t)
    (restartState_measurable D steps hpc G hG initial t)
    (fun seeds => restartState_mem hc hp D steps G hinit seeds t)
  let a : ℝ := 2 * D t / ((steps t : ℝ) * (steps t + 1))
  let b : ℝ := (steps t : ℝ) * V / D t
  have hbnd (x : C) : (∫ seeds, Φ x seeds ∂(P : Measure (ℕ → StepSeed))) ≤ a * ‖x.val - u‖ ^ 2 + b := by
    have hh := solver_rate p hc hcompact hL hD hLD hV hf hfc hg hlip hu hmin
      G hG hGi hmean hei hvar x.property hn
    simpa only [Φ, out, P, ProbabilityMeasure.coe_mk, project, a, b, div_mul_eq_mul_div] using hh
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun seeds => integral_nonneg (fun block =>
      sub_nonneg.mpr (hmin _ (hom (X seeds, block))))))
    ((hdi.const_mul a).add (integrable_const b))
    (Filter.Eventually.of_forall (fun seeds => hbnd (X seeds)))
  simp only [Pi.add_apply] at hle
  rw [integral_add (hdi.const_mul a) (integrable_const b), integral_const_mul, integral_const] at hle
  change (∫ seeds, Φ (X seeds) (seeds t) ∂(T : Measure (ℕ → ℕ → StepSeed))) ≤ _
  change (∫ seeds, Φ (X seeds) (seeds t) ∂(T : Measure (ℕ → ℕ → StepSeed))) =
    (∫ seeds, (∫ block, Φ (X seeds) block ∂(P : Measure (ℕ → StepSeed)))
      ∂(T : Measure (ℕ → ℕ → StepSeed))) at htower
  rw [htower]
  simpa only [T, P, ProbabilityMeasure.coe_mk, project, probReal_univ, one_smul, a, b,
    div_mul_eq_mul_div] using hle

lemma restartGap_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < restartGap d j := by
  unfold restartGap
  positivity

lemma restartGap_succ (d : ℝ) (j : ℕ) : restartGap d (j + 1) = restartGap d j / 2 := by
  simp only [restartGap, pow_succ, div_mul_eq_div_div]

lemma restartSteps_lower {S V μ d : ℝ} (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hμ : 0 < μ) (hd : 0 < d) :
    0 < restartSteps S V μ d ∧
      64 * S / μ ≤ (restartSteps S V μ d : ℝ) ^ 2 ∧
      256 * V / (μ * d) ≤ (restartSteps S V μ d : ℝ) := by
  have hn := Nat.le_ceil (8 * Real.sqrt (S / μ) + 256 * V / (μ * d) + 1)
  change 8 * Real.sqrt (S / μ) + 256 * V / (μ * d) + 1 ≤
    (restartSteps S V μ d : ℝ) at hn
  have hv : 0 ≤ 256 * V / (μ * d) := by positivity
  have hs := Real.sqrt_nonneg (S / μ)
  have hs2 := Real.sq_sqrt (div_nonneg hS hμ.le)
  have hn0 : 0 < (restartSteps S V μ d : ℝ) := by linarith
  refine ⟨by exact_mod_cast hn0, ?_, by linarith⟩
  have hh : 8 * Real.sqrt (S / μ) ≤ (restartSteps S V μ d : ℝ) := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hh)
    (show 0 ≤ (restartSteps S V μ d : ℝ) + 8 * Real.sqrt (S / μ) by positivity)
  have hsq : 64 * (Real.sqrt (S / μ)) ^ 2 ≤ (restartSteps S V μ d : ℝ) ^ 2 := by
    nlinarith only [hp]
  rw [hs2] at hsq
  convert hsq using 1
  ring

lemma restartScale_pos {S V μ d : ℝ} (hS : 0 < S) (hV : 0 ≤ V) (hd : 0 < d) :
    0 < restartScale S V μ d := by
  unfold restartScale
  positivity

lemma restartScale_lower {S V μ d : ℝ} (hV : 0 ≤ V) (hd : 0 < d) :
    2 * S ≤ restartScale S V μ d := by
  unfold restartScale
  exact le_add_of_nonneg_right (by positivity)

lemma restart_stage_rate {S V μ d r2 : ℝ} (hS : 0 < S) (hV : 0 ≤ V)
    (hμ : 0 < μ) (hd : 0 < d) (hr : r2 ≤ 2 * d / μ) :
    2 * restartScale S V μ d * r2 /
        ((restartSteps S V μ d : ℝ) * (restartSteps S V μ d + 1)) +
      (restartSteps S V μ d : ℝ) * V / restartScale S V μ d ≤ d / 2 := by
  have hh := restartSteps_lower hS.le hV hμ hd
  have ht : 0 < (restartSteps S V μ d : ℝ) := by exact_mod_cast hh.1
  have hb := ConstrainedStochasticAcceleration.restart_tuning hS hV hd hμ ht hr hh.2.1 hh.2.2
  change _ ≤ 3 * d / 8 at hb
  have he : 3 * d / 8 ≤ d / 2 := by linarith
  simpa only [restartScale] using hb.trans he

lemma restart_gap_bound [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (p : ProbabilityMeasure StepSeed)
    {C : Set E} (hc : Convex ℝ C) (hcompact : IsCompact C)
    {f : E → ℝ} {L V μ d0 : ℝ} (hL : 0 < L) (hV : 0 ≤ V) (hμ : 0 < μ) (hd0 : 0 < d0)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : u ∈ C) (hmin : ∀ x ∈ C, f u ≤ f x)
    (hgrowth : ∀ x ∈ C, μ / 2 * ‖x - u‖ ^ 2 ≤ f x - f u)
    (G : E → StepSeed → E) (hG : Measurable (Function.uncurry G))
    (hGi : ∀ x ∈ C, Integrable (G x) (p : Measure StepSeed))
    (hmean : ∀ x ∈ C, (∫ ω, G x ω ∂(p : Measure StepSeed)) = gradient f x)
    (hei : ∀ x ∈ C, Integrable (fun ω => ‖gradient f x - G x ω‖ ^ 2) (p : Measure StepSeed))
    (hvar : ∀ x ∈ C, (∫ ω, ‖gradient f x - G x ω‖ ^ 2 ∂(p : Measure StepSeed)) ≤ V)
    {initial : E} (hinit : initial ∈ C) (hinitgap : f initial - f u ≤ d0) (n : ℕ) :
    let D := fun j => restartScale L V μ (restartGap d0 j)
    let steps := fun j => restartSteps L V μ (restartGap d0 j)
    let P := Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed)
    let T := Measure.infinitePi fun _ : ℕ => P
    (∫ seeds, f (restartState D steps (OracleTemplate.SaddlePoint.project C) G initial seeds n) - f u ∂T) ≤
      restartGap d0 n := by
  let D := fun j => restartScale L V μ (restartGap d0 j)
  let steps := fun j => restartSteps L V μ (restartGap d0 j)
  let P : ProbabilityMeasure (ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (p : Measure StepSeed), inferInstance⟩
  let T : ProbabilityMeasure (ℕ → ℕ → StepSeed) :=
    ⟨Measure.infinitePi fun _ : ℕ => (P : Measure (ℕ → StepSeed)), inferInstance⟩
  let project := OracleTemplate.SaddlePoint.project C
  have hp : ∀ x, project x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hc x).1
  have hpc : Continuous project :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hc).continuous
  change (∫ seeds, f (restartState D steps project G initial seeds n) - f u
    ∂(T : Measure (ℕ → ℕ → StepSeed))) ≤ restartGap d0 n
  induction n with
  | zero => simpa only [restartState, restartGap, pow_zero, div_one, integral_const,
      probReal_univ, one_smul] using hinitgap
  | succ n ih =>
    have hd := restartGap_pos hd0 n
    have hns := restartSteps_lower hL.le hV hμ hd
    have hscale := restartScale_pos (μ := μ) hL hV hd
    have hscaleL := restartScale_lower (S := L) (μ := μ) hV hd
    have hr := restart_step_rate p hc hcompact D steps n hL.le hscale hscaleL hV
      hf hfc hg hlip hu hmin G hG hGi hmean hei hvar hinit hns.1
    have hdi := ConstrainedStochasticAcceleration.integrable_compact_image T hcompact
      (fun x => ‖x - u‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
      (fun seeds => restartState D steps project G initial seeds n)
      (restartState_measurable D steps hpc G hG initial n)
      (fun seeds => restartState_mem hc hp D steps G hinit seeds n)
    have hfi := ConstrainedStochasticAcceleration.integrable_compact_image T hcompact
      (fun x => f x - f u) (hfc.sub continuousOn_const)
      (fun seeds => restartState D steps project G initial seeds n)
      (restartState_measurable D steps hpc G hG initial n)
      (fun seeds => restartState_mem hc hp D steps G hinit seeds n)
    have hgrowthint := integral_mono (hdi.const_mul (μ / 2)) hfi (fun seeds =>
      hgrowth _ (restartState_mem hc hp D steps G hinit seeds n))
    rw [integral_const_mul] at hgrowthint
    have hdist : (∫ seeds, ‖restartState D steps project G initial seeds n - u‖ ^ 2
        ∂(T : Measure (ℕ → ℕ → StepSeed))) ≤ 2 * restartGap d0 n / μ := by
      apply (le_div_iff₀ hμ).2
      linarith
    have ht := restart_stage_rate hL hV hμ hd hdist
    have hr' : (∫ seeds, f (restartState D steps project G initial seeds (n + 1)) - f u
        ∂(T : Measure (ℕ → ℕ → StepSeed))) ≤
        2 * D n * (∫ seeds, ‖restartState D steps project G initial seeds n - u‖ ^ 2
          ∂(T : Measure (ℕ → ℕ → StepSeed))) / ((steps n : ℝ) * (steps n + 1)) +
          (steps n : ℝ) * V / D n := by
      simpa only [T, P, ProbabilityMeasure.coe_mk, project] using hr
    rw [restartGap_succ]
    exact hr'.trans ht

lemma restartRounds_accuracy {d ε : ℝ} (hε : 0 < ε) :
    restartGap d (restartRounds d ε) ≤ ε := by
  have hh := Nat.le_pow_clog (by norm_num : 1 < 2) (Nat.ceil (d / ε))
  have hp : (Nat.ceil (d / ε) : ℝ) ≤ (2 : ℝ) ^ restartRounds d ε := by
    exact_mod_cast hh
  have hr := (Nat.le_ceil (d / ε)).trans hp
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ restartRounds d ε)).2
  have hmul := (div_le_iff₀ hε).1 hr
  simpa only [mul_comm] using hmul

lemma restartSteps_upper {S V μ d : ℝ} (hV : 0 ≤ V) (hμ : 0 < μ) (hd : 0 < d) :
    (restartSteps S V μ d : ℝ) ≤ 8 * Real.sqrt (S / μ) + 256 * V / (μ * d) + 2 := by
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.sqrt (S / μ) + 256 * V / (μ * d) + 1 by positivity)
  change (restartSteps S V μ d : ℝ) < _ at hn
  linarith

lemma restartSteps_sum {S V μ d : ℝ} (hV : 0 ≤ V) (hμ : 0 < μ) (hd : 0 < d) (n : ℕ) :
    (∑ j ∈ Finset.range n, (restartSteps S V μ (restartGap d j) : ℝ)) ≤
      (n : ℝ) * (8 * Real.sqrt (S / μ) + 2) + 256 * V / (μ * d) * ((2 : ℝ) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hh := restartSteps_upper (S := S) hV hμ (restartGap_pos hd n)
    have he : 256 * V / (μ * restartGap d n) = 256 * V / (μ * d) * (2 : ℝ) ^ n := by
      unfold restartGap
      field_simp
    rw [he] at hh
    have ha := add_le_add ih hh
    push_cast
    rw [pow_succ]
    nlinarith only [ha]

lemma restartRounds_zero {d ε : ℝ} (hε : 0 < ε) (h : d ≤ ε) : restartRounds d ε = 0 := by
  apply Nat.clog_of_right_le_one
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_one, div_le_one hε] using h

lemma restartRounds_power {d ε : ℝ} (hJ : 0 < restartRounds d ε) :
    (2 : ℝ) ^ restartRounds d ε < 2 * (d / ε) := by
  have hceil : 1 < Nat.ceil (d / ε) := by
    by_contra h
    have hz := Nat.clog_of_right_le_one (Nat.le_of_not_gt h) 2
    change 0 < Nat.clog 2 (Nat.ceil (d / ε)) at hJ
    omega
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hceil
  have hreal : (2 : ℝ) ^ (restartRounds d ε - 1) < d / ε := by
    exact_mod_cast (Nat.lt_ceil.mp hp)
  have he : restartRounds d ε - 1 + 1 = restartRounds d ε :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hJ)
  have heq : (2 : ℝ) ^ restartRounds d ε = (2 : ℝ) ^ (restartRounds d ε - 1) * 2 := by
    rw [← pow_succ, he]
  rw [heq]
  linarith

lemma restartSteps_total {S V μ d ε : ℝ} (hV : 0 ≤ V) (hμ : 0 < μ)
    (hd : 0 < d) (hε : 0 < ε) :
    (∑ j ∈ Finset.range (restartRounds d ε), (restartSteps S V μ (restartGap d j) : ℝ)) ≤
      (restartRounds d ε : ℝ) * (8 * Real.sqrt (S / μ) + 2) + 512 * V / (μ * ε) := by
  by_cases hJ : restartRounds d ε = 0
  · simp only [hJ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, zero_add]
    positivity
  · have hp := restartRounds_power (Nat.pos_of_ne_zero hJ)
    have hcoeff : 0 ≤ 256 * V / (μ * d) := by positivity
    have hnoise := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) ^ restartRounds d ε - 1 ≤ 2 * (d / ε) by linarith) hcoeff
    have he : 256 * V / (μ * d) * (2 * (d / ε)) = 512 * V / (μ * ε) := by
      field_simp
      ring
    rw [he] at hnoise
    exact (restartSteps_sum (S := S) hV hμ hd _).trans (add_le_add (le_refl _) hnoise)

lemma restartPlan_cost_moments {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot ι E) (τ μ : ℝ)
    (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E) (initial : E)
    (reply : ι × E → ℝ × E) (n : ℕ) :
    Integrable (fun seeds : ℕ → ℕ → StepSeed =>
      (OracleTemplate.ComponentEnvelope.Program.cost reply
        (restartPlan s τ μ D steps project initial seeds n) : ℝ))
      (Measure.infinitePi fun _ : ℕ =>
        (Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed))) ∧
    (∫ seeds : ℕ → ℕ → StepSeed,
      (OracleTemplate.ComponentEnvelope.Program.cost reply
        (restartPlan s τ μ D steps project initial seeds n) : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ =>
        (Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)))) =
      2 * ∑ j ∈ Finset.range n, (steps j : ℝ) := by
  let P := Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)
  let T := Measure.infinitePi fun _ : ℕ => P
  let c : StepSeed → ℝ := fun seed => ((seed.1 + 1 : ℕ) : ℝ)
  have hm : Measurable c := by unfold c; fun_prop
  have hmean : (∫ seed, c seed ∂(stepLaw : Measure StepSeed)) = 2 := by
    simpa only [AffineSoftmaxExecution.seededEstimatorPlan_cost] using
      AffineSoftmaxExecution.seededEstimatorPlan_expected_cost s τ initial reply
  have hi : Integrable c (stepLaw : Measure StepSeed) := by
    by_contra hn
    rw [integral_undef hn] at hmean
    norm_num at hmean
  have hp k := measurePreserving_eval_infinitePi (fun _ : ℕ => (stepLaw : Measure StepSeed)) k
  have ht j := measurePreserving_eval_infinitePi (fun _ : ℕ => P) j
  have hpres j k : MeasurePreserving (fun seeds : ℕ → ℕ → StepSeed => seeds j k)
      T (stepLaw : Measure StepSeed) := (hp k).comp (ht j)
  have hki j k : Integrable (fun seeds : ℕ → ℕ → StepSeed => c (seeds j k)) T :=
    (hpres j k).integrable_comp_of_integrable hi
  have hkm j k : (∫ seeds : ℕ → ℕ → StepSeed, c (seeds j k) ∂T) = 2 := by
    rw [← integral_map_of_stronglyMeasurable
      (hpres j k).measurable hm.stronglyMeasurable,
      (hpres j k).map_eq]
    exact hmean
  constructor
  · simp only [restartPlan_cost, Nat.cast_sum]
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hki j k))
  · simp only [restartPlan_cost, Nat.cast_sum]
    change (∫ seeds : ℕ → ℕ → StepSeed,
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (steps j), c (seeds j k) ∂T) = _
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hki j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hki _ k), hkm]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma restartPlan_expected_cost_le {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot ι E) (τ : ℝ)
    {S V μ d ε : ℝ} (hV : 0 ≤ V) (hμ : 0 < μ) (hd : 0 < d) (hε : 0 < ε)
    (project : E → E) (initial : E) (reply : ι × E → ℝ × E) :
    (∫ seeds : ℕ → ℕ → StepSeed,
      (OracleTemplate.ComponentEnvelope.Program.cost reply
        (restartPlan s τ μ (fun j => restartScale S V μ (restartGap d j))
          (fun j => restartSteps S V μ (restartGap d j)) project initial seeds
          (restartRounds d ε)) : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ =>
        (Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)))) ≤
      (restartRounds d ε : ℝ) * (16 * Real.sqrt (S / μ) + 4) +
        1024 * V / (μ * ε) := by
  rw [(restartPlan_cost_moments s τ μ _ _ project initial reply _).2]
  have hh := mul_le_mul_of_nonneg_left (restartSteps_total (S := S) hV hμ hd hε)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert hh using 1
  ring

lemma restartRounds_scaled {d δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    restartRounds d (δ / 2 ^ j) ≤ restartRounds d δ + j := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  have hb := restartRounds_accuracy (d := d) hδ
  have hp : 0 < (2 : ℝ) ^ restartRounds d δ := by positivity
  have hd : d ≤ δ * (2 : ℝ) ^ restartRounds d δ := (div_le_iff₀ hp).1 hb
  have hr : d / δ ≤ (2 : ℝ) ^ restartRounds d δ :=
    (div_le_iff₀ hδ).2 (by simpa only [mul_comm] using hd)
  have hh := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ (2 : ℝ) ^ j)
  push_cast
  rw [pow_add]
  convert hh using 1
  field_simp

end LongTails.Proofs.AffineSoftmaxRestarts
