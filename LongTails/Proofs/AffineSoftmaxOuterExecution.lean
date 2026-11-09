import LongTails.Algorithms.AffineSoftmaxOuter
import LongTails.Proofs.AffineSoftmaxSearchExecution
import LongTails.Proofs.AffineSoftmaxMultilevel

namespace LongTails.Proofs.AffineSoftmaxOuterExecution

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxSearch
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.CappedProximal

lemma regularizationSearchPlan_param_measurable {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Z] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (state : Z → State E)
    (hA : ∀ z, 0 ≤ (state z).weight) (hx : ∀ z, (state z).primal ∈ X) (hv : ∀ z, (state z).dual ∈ X)
    (hmA : Measurable (fun z => (state z).weight))
    (hmx : Measurable (fun z => (state z).primal)) (hmv : Measurable (fun z => (state z).dual))
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (seeds : Z → ℕ → ProbeSeed) (hseeds : ∀ i a j k, Measurable (fun z => seeds z i a j k)) :
    Measurable (fun z => Program.eval reply
      (regularizationSearchPlan m X (state z) τ L G r floor cap H b (seeds z))) := by
  obtain ⟨M, hM⟩ := hcompact.isBounded.exists_norm_le
  let B := max 0 M
  have hB : 0 ≤ B := le_max_left _ _
  have hbound x (h : x ∈ X) : ‖x‖ ≤ B := (hM x h).trans (le_max_right _ _)
  have hproj := MovingBallProjection.measurable_moving_project hX hcompact hB hbound hr
  let center : Z × ℝ → E := fun w => predictor (max floor w.2) (state w.1)
  have hc : Measurable center := AffineSoftmaxPredictor.predictor_param_measurable
    (fun w : Z × ℝ => state w.1) (fun w => max floor w.2)
    (measurable_const.max measurable_snd) (hmA.comp measurable_fst)
    (hmx.comp measurable_fst) (hmv.comp measurable_fst)
  have hcX w : center w ∈ X := AffineSoftmaxPredictor.predictor_mem hX (state w.1)
    (hf.trans_le (le_max_left floor w.2)) (hA w.1) (hx w.1) (hv w.1)
  have hp : Measurable (fun w : (Z × ℝ) × E =>
      OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center w.1) r) w.2) :=
    hproj.comp (((hc.subtype_mk (h := hcX)).comp measurable_fst).prodMk measurable_snd)
  let probes : Z → ℕ → ℝ → Program (Fin m × E) (ℝ × E) ℝ := fun z i μ =>
    probePlan m (center (z, μ)) τ L G r (max floor μ)
      (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center (z, μ)) r)) (seeds z i) b
  have hprobes (i : ℕ) : Measurable (fun w : Z × ℝ => Program.eval reply (probes w.1 i w.2)) := by
    have hh := AffineSoftmaxSearchOracle.probePlan_param_measurable m center τ L G r
      (fun w => max floor w.2) hc (measurable_const.max measurable_snd)
      (fun w => OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center w) r)) hp
      reply hm (fun w => seeds w.1 i) (fun a j k => (hseeds i a j k).comp measurable_fst) b
    exact hh
  exact AffineSoftmaxSearchTrace.searchPlan_measurable probes reply r floor cap H hprobes

lemma finalStepPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G D ε : ℝ) {r μ : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (H : ℕ) (seed : FinalSeed) (reply : Fin m × E → ℝ × E) :
    let out := Program.eval reply (finalStepPlan m X state τ L G r D ε μ H seed)
    state.weight < out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  let a := nextWeight μ state.weight
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let project := OracleTemplate.SaddlePoint.project C
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let x := Program.eval reply (cachedProxPlan s τ L G r μ (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) project seed.1)
  let g := Program.eval reply (cachedProxGradientPlan s τ L G r μ
    (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D)) project seed.2)
  have he : Program.eval reply (finalStepPlan m X state τ L G r D ε μ H seed) =
      (⟨state.weight + a, x, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g)⟩ : State E) := by
    simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
    rfl
  rw [he]
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr⟩
  have hp : ∀ z, project z ∈ C := fun z =>
    (OracleTemplate.SaddlePoint.project_spec ⟨center, hcC⟩ hCcompact hC z).1
  have hxC : x ∈ C := AffineSoftmaxBallSolver.cachedProxPlan_mem hC s τ L G r μ _ project hp hcC reply seed.1
  have ha : 0 < a := (AffineSoftmaxPredictor.ratio_properties hμ hA).1
  exact ⟨by dsimp; linarith, hxC.1,
    (OracleTemplate.SaddlePoint.project_spec ⟨state.primal, hx⟩ hcompact hX _).1⟩

lemma outerStepPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G D ε : ℝ) {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (seed : OuterSeed) (reply : Fin m × E → ℝ × E) :
    let out := Program.eval reply (outerStepPlan m X state τ L G r D ε floor cap H b seed)
    state.weight < out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  let μ := Program.eval reply (regularizationSearchPlan m X state τ L G r floor cap H b seed.1)
  have hμrange : μ ∈ Set.Icc floor cap := by
    dsimp only [μ, regularizationSearchPlan]
    exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
  have hμ : 0 < μ := hf.trans_le hμrange.1
  simpa only [outerStepPlan, Program.eval_bind, μ] using
    finalStepPlan_feasible m hX hcompact state hA hx hv τ L G D ε hr hμ H seed.2 reply

lemma outerRunPlan_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) (n : ℕ) :
    let out := Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b seeds n)
    0 ≤ out.weight ∧ out.primal ∈ X ∧ out.dual ∈ X := by
  induction n with
  | zero => exact ⟨le_rfl, hi, hi⟩
  | succ n ih =>
    simp only [outerRunPlan, Program.eval_bind]
    split_ifs
    · exact ih
    · have hs := outerStepPlan_feasible m hX hcompact _ ih.1 ih.2.1 ih.2.2 τ L G D ε hr hf hfc H b (seeds n) reply
      exact ⟨ih.1.trans hs.1.le, hs.2⟩

lemma finalStepPlan_param_measurable {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Z] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty) (state : Z → State E)
    (hA : ∀ z, 0 ≤ (state z).weight) (hx : ∀ z, (state z).primal ∈ X) (hv : ∀ z, (state z).dual ∈ X)
    (hmA : Measurable (fun z => (state z).weight))
    (hmx : Measurable (fun z => (state z).primal)) (hmv : Measurable (fun z => (state z).dual))
    (τ L G D ε : ℝ) {r : ℝ} (hr : 0 < r) (μ : Z → ℝ) (hmμ : Measurable μ)
    (hμpos : ∀ z, 0 < μ z) (H : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (seed : Z → FinalSeed) (hseed : Measurable seed) :
    let out := fun z => Program.eval reply (finalStepPlan m X (state z) τ L G r D ε (μ z) H (seed z))
    Measurable (fun z => (out z).weight) ∧ Measurable (fun z => (out z).primal) ∧ Measurable (fun z => (out z).dual) := by
  let a := fun z => nextWeight (μ z) (state z).weight
  have hma : Measurable a := AffineSoftmaxPredictor.nextWeight_measurable μ (fun z => (state z).weight) hmμ hmA
  let center := fun z => predictor (μ z) (state z)
  have hmc : Measurable center := AffineSoftmaxPredictor.predictor_param_measurable state μ hmμ hmA hmx hmv
  have hcX z : center z ∈ X := AffineSoftmaxPredictor.predictor_mem hX (state z) (hμpos z) (hA z) (hx z) (hv z)
  obtain ⟨M, hM⟩ := hcompact.isBounded.exists_norm_le
  have hbound x (h : x ∈ X) : ‖x‖ ≤ max 0 M := (hM x h).trans (le_max_right _ _)
  let project := fun z => OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center z) r)
  have hmp : Measurable (Function.uncurry project) :=
    (MovingBallProjection.measurable_moving_project hX hcompact (le_max_left 0 M) hbound hr).comp
      (((hmc.subtype_mk (h := hcX)).comp measurable_fst).prodMk measurable_snd)
  let s : Z → Snapshot (Fin m) E := fun z => ⟨center z, (fun i => (reply (i, center z)).1),
    (fun i => (reply (i, center z)).2)⟩
  have hvalue i : Measurable (fun z => (s z).value i) := (hm.comp (measurable_const.prodMk hmc)).fst
  have hfield i : Measurable (fun z => (s z).field i) := (hm.comp (measurable_const.prodMk hmc)).snd
  let x := fun z => Program.eval reply (cachedProxPlan (s z) τ L G r (μ z)
    (μ z * r ^ 2 / (100000 * (H : ℝ) ^ 3)) (project z) (seed z).1)
  have hmx' : Measurable x := AffineSoftmaxBallSolver.cachedProxPlan_param_measurable s τ L G r μ
    (fun z => μ z * r ^ 2 / (100000 * (H : ℝ) ^ 3)) hmc hvalue hfield hmμ
    ((hmμ.mul_const _).div_const _) project hmp reply hm (fun z => (seed z).1)
    (fun j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hseed.fst))
  let g := fun z => Program.eval reply (cachedProxGradientPlan (s z) τ L G r (μ z)
    (Real.sqrt (μ z ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (ε / (1000 * D)) (project z) (seed z).2)
  have hmg : Measurable g := AffineSoftmaxMultilevel.cachedProxGradientPlan_param_measurable s τ L G r μ
    (fun z => Real.sqrt (μ z ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) (fun _ => ε / (1000 * D))
    hmc hvalue hfield hmμ (Real.continuous_sqrt.measurable.comp (((hmμ.pow_const 2).mul_const _).div_const _))
    measurable_const project hmp reply hm (fun z => (seed z).2) hseed.snd
  have hglobal : Measurable (OracleTemplate.SaddlePoint.project X) :=
    (NondualProjection.project_lipschitz hne hcompact hX).continuous.measurable
  have he z : Program.eval reply (finalStepPlan m X (state z) τ L G r D ε (μ z) H (seed z)) =
      (⟨(state z).weight + a z, x z, OracleTemplate.SaddlePoint.project X ((state z).dual - (a z / 2) • g z)⟩ : State E) := by
    simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
    rfl
  dsimp only
  simp_rw [he]
  exact ⟨hmA.add hma, hmx', hglobal.comp (hmv.sub ((hma.div_const 2).smul hmg))⟩

lemma outerStepPlan_param_measurable {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Z] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (hne : X.Nonempty) (state : Z → State E)
    (hA : ∀ z, 0 ≤ (state z).weight) (hx : ∀ z, (state z).primal ∈ X) (hv : ∀ z, (state z).dual ∈ X)
    (hmA : Measurable (fun z => (state z).weight))
    (hmx : Measurable (fun z => (state z).primal)) (hmv : Measurable (fun z => (state z).dual))
    (τ L G D ε : ℝ) {r floor cap : ℝ} (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (seed : Z → OuterSeed) (hseed : Measurable seed) :
    let out := fun z => Program.eval reply (outerStepPlan m X (state z) τ L G r D ε floor cap H b (seed z))
    Measurable (fun z => (out z).weight) ∧ Measurable (fun z => (out z).primal) ∧ Measurable (fun z => (out z).dual) := by
  let μ := fun z => Program.eval reply (regularizationSearchPlan m X (state z) τ L G r floor cap H b (seed z).1)
  have hmμ : Measurable μ := regularizationSearchPlan_param_measurable m hX hcompact state hA hx hv hmA hmx hmv
    τ L G hr hf cap H b reply hm (fun z => (seed z).1)
    (fun i a j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hseed.fst))))
  have hμpos z : 0 < μ z := by
    have hh : μ z ∈ Set.Icc floor cap := by
      dsimp only [μ, regularizationSearchPlan]
      exact AffineSoftmaxSearch.searchPlan_eval_mem _ reply r (hf.le.trans hfc) hfc H
    exact hf.trans_le hh.1
  simpa only [outerStepPlan, Program.eval_bind, μ] using
    finalStepPlan_param_measurable m hX hcompact hne state hA hx hv hmA hmx hmv
      τ L G D ε hr μ hmμ hμpos H reply hm (fun z => (seed z).2) hseed.snd

lemma outerRunPlan_param_measurable {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Z] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (initial : E) (hi : initial ∈ X)
    (τ L G D ε : ℝ) {r floor cap : ℝ} (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (seeds : Z → ℕ → OuterSeed) (hseeds : ∀ j, Measurable (fun z => seeds z j)) (n : ℕ) :
    let out := fun z => Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b (seeds z) n)
    Measurable (fun z => (out z).weight) ∧ Measurable (fun z => (out z).primal) ∧ Measurable (fun z => (out z).dual) := by
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
    let state := fun z => Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b (seeds z) n)
    have hstate z := outerRunPlan_feasible m hX hcompact initial hi τ L G D ε hr.le hf hfc H b (seeds z) reply n
    have hstep := outerStepPlan_param_measurable m hX hcompact ⟨initial, hi⟩ state
      (fun z => (hstate z).1) (fun z => (hstate z).2.1) (fun z => (hstate z).2.2)
      ih.1 ih.2.1 ih.2.2 τ L G D ε hr hf hfc H b reply hm (fun z => seeds z n) (hseeds n)
    have hstop : MeasurableSet {z | 100 * D ^ 2 / ε ≤ (state z).weight} :=
      measurableSet_le measurable_const ih.1
    have he z : Program.eval reply (outerRunPlan m X initial τ L G r D ε floor cap H b (seeds z) (n + 1)) =
        if 100 * D ^ 2 / ε ≤ (state z).weight then state z
        else Program.eval reply (outerStepPlan m X (state z) τ L G r D ε floor cap H b (seeds z n)) := by
      simp only [outerRunPlan, Program.eval_bind]
      split_ifs <;> rfl
    dsimp only
    simp_rw [he]
    simp only [apply_ite]
    exact ⟨Measurable.ite hstop ih.1 hstep.1, Measurable.ite hstop ih.2.1 hstep.2.1,
      Measurable.ite hstop ih.2.2 hstep.2.2⟩

lemma outerOutputPlan_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (initial : E) (hi : initial ∈ X) (τ L G D ε : ℝ)
    {r floor cap : ℝ} (hr : 0 ≤ r) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H b N : ℕ) (seeds : ℕ → OuterSeed) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (outerOutputPlan m X initial τ L G r D ε floor cap H b N seeds) ∈ X := by
  simpa only [outerOutputPlan, Program.eval_map] using
    (outerRunPlan_feasible m hX hcompact initial hi τ L G D ε hr hf hfc H b seeds reply N).2.1

lemma search_boost_count_failure (N H : ℕ) (hN : 0 < N) (hH : 3 ≤ H) :
    ((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (Nat.clog 2 (120 * N * H)) ≤ 1 / (12 * (N : ℝ)) := by
  let b := Nat.clog 2 (120 * N * H)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hHr : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hden : 0 < (120 : ℝ) * N * H := by positivity
  have hp : (120 : ℝ) * N * H ≤ 2 ^ b := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (120 * N * H)
  have hq : (1 / 4 : ℝ) ^ b ≤ 1 / 2 ^ b := by
    rw [← one_div_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) b
  have hn : ((2 * H + 9 : ℕ) : ℝ) ≤ 10 * (H : ℝ) := by
    exact_mod_cast (show 2 * H + 9 ≤ 10 * H by omega)
  calc
    ((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ b ≤ (10 * (H : ℝ)) * (1 / 2 ^ b) :=
      mul_le_mul hn hq (by positivity) (by positivity)
    _ ≤ (10 * (H : ℝ)) * (1 / ((120 : ℝ) * N * H)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hden hp) (by positivity)
    _ = 1 / (12 * (N : ℝ)) := by field_simp; ring

end LongTails.Proofs.AffineSoftmaxOuterExecution
