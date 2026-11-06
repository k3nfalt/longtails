import LongTails.Proofs.AffineSoftmaxPredictor
import LongTails.Proofs.MovingBallProjection

namespace LongTails.Proofs.AffineSoftmaxSearchExecution

open MeasureTheory
open scoped ENNReal
open LongTails.Algorithms.AffineSoftmaxEstimator
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch
open LongTails.Algorithms.CappedProximal

lemma regularizationProbe_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (state : State E)
    (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (fun z : ProbeSeed × ℝ => Program.eval reply
      (probePlan m (predictor (max floor z.2) state) τ L G r (max floor z.2)
        (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (predictor (max floor z.2) state) r)) z.1 b)) := by
  obtain ⟨M, hM⟩ := hcompact.isBounded.exists_norm_le
  have hMpos : 0 ≤ M := (norm_nonneg state.primal).trans (hM _ hx)
  have hproj := MovingBallProjection.measurable_moving_project hX hcompact hMpos hM hr
  have hcenter := (AffineSoftmaxPredictor.predictor_continuous state hA
    (fun μ : ℝ => max floor μ) (continuous_const.max continuous_id)
    (fun μ => hf.trans_le (le_max_left floor μ))).measurable
  let Z := ProbeSeed × ℝ
  let center : Z → E := fun z => predictor (max floor z.2) state
  have hc : Measurable center := hcenter.comp measurable_snd
  have hcX z : center z ∈ X := AffineSoftmaxPredictor.predictor_mem hX state
    (hf.trans_le (le_max_left floor z.2)) hA hx hv
  have hp : Measurable (fun z : Z × E =>
      OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center z.1) r) z.2) :=
    hproj.comp (((hc.subtype_mk (h := hcX)).comp measurable_fst).prodMk measurable_snd)
  exact AffineSoftmaxSearchOracle.probePlan_param_measurable m center τ L G r
    (fun z => max floor z.2) hc (measurable_const.max measurable_snd)
    (fun z => OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (center z) r)) hp
    reply hm (fun z => z.1)
    (fun a j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply a).comp measurable_fst))) b

lemma regularizationSearchPlan_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (state : State E)
    (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (τ L G : ℝ) {r floor : ℝ} (hr : 0 < r) (hf : 0 < floor) (cap : ℝ) (H b : ℕ)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply) :
    Measurable (fun seeds : ℕ → ProbeSeed => Program.eval reply
      (regularizationSearchPlan m X state τ L G r floor cap H b seeds)) := by
  have hp := regularizationProbe_measurable m hX hcompact state hA hx hv τ L G hr hf b reply hm
  let probes : (ℕ → ProbeSeed) → ℕ → ℝ → Program (Fin m × E) (ℝ × E) ℝ := fun seeds i μ =>
    probePlan m (predictor (max floor μ) state) τ L G r (max floor μ)
      (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (predictor (max floor μ) state) r)) (seeds i) b
  have hprobes (i : ℕ) : Measurable (fun z : (ℕ → ProbeSeed) × ℝ => Program.eval reply (probes z.1 i z.2)) := by
    have hmap : Measurable (fun z : (ℕ → ProbeSeed) × ℝ => (z.1 i, z.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    have hh := hp.comp hmap
    simpa only [probes, Function.comp_def] using hh
  exact AffineSoftmaxSearchTrace.searchPlan_measurable probes reply r floor cap H hprobes

lemma regularizationSearchPlan_failure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (f : Fin m → E → ℝ)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    {τ L G r floor cap D : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (hlocal : L * r ^ 2 ≤ τ)
    (hdiam : ‖state.dual - state.primal‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ X → y ∈ X →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ X → ‖gradient (f i) x‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (H b : ℕ) (hcap : 2 * G / r ≤ cap) (hend : cap / 2 ^ H ≤ floor)
    (hwidth : (2 * D + G / floor) / 2 ^ (H + 7) < r / 64) :
    let F := fun z => smoothValue τ (fun i => f i z)
    let displacement := fun μ => ‖AffineSoftmaxRegularization.exactProx X F μ (predictor μ state) - predictor μ state‖
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | let answer := Program.eval reply (regularizationSearchPlan m X state τ L G r floor cap H b seeds)
        ¬ (answer ∈ Set.Icc floor cap ∧
          ((answer = floor ∧ displacement answer < r) ∨
            (51 * r / 64 ≤ displacement answer ∧ displacement answer ≤ 61 * r / 64)))} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ b) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let d := fun μ => ‖AffineSoftmaxRegularization.exactProx X F (max floor μ)
    (predictor (max floor μ) state) - predictor (max floor μ) state‖
  let probe := fun (_ : ℕ) seed μ => probePlan m (predictor (max floor μ) state) τ L G r (max floor μ)
    (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall (predictor (max floor μ) state) r)) seed b
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFg x (hx' : x ∈ X) : HasGradientAt F (gradient F x) x := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx')
    rw [hh.gradient]
    exact hh
  have hFcont : ContinuousOn F X := fun x hx' => (hFg x hx').continuousAt.continuousWithinAt
  have hFb x (hx' : x ∈ X) : ‖gradient F x‖ ≤ G :=
    SmoothFiniteMaximumGeometry.smoothValue_gradient_bound f hτ.ne' (fun i => hg i x hx')
      (fun i => hbound i x hx')
  have hd : Measurable d := (AffineSoftmaxPredictor.proximal_predictor_displacement_continuous
    hcompact ⟨state.primal, hx⟩ hF hFcont state hA (fun μ : ℝ => max floor μ)
    (continuous_const.max continuous_id) (fun μ => hf.trans_le (le_max_left floor μ))).measurable
  have hcapPos : 0 < cap := hf.trans_le hfc
  have hdcap : d cap ≤ r / 2 := by
    dsimp [d]
    rw [max_eq_right hfc]
    apply (AffineSoftmaxPredictor.proximal_predictor_displacement_bound hcompact hF hFcont hFg hG.le hFb
      state hA hx hv hcapPos).trans
    apply (div_le_iff₀ hcapPos).mpr
    have hh := (div_le_iff₀ hr).mp hcap
    nlinarith
  have hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ (2 * D + G / floor) * |x - y| / min x y := by
    intro x hx' y hy'
    dsimp [d]
    rw [max_eq_right hx'.1, max_eq_right hy'.1]
    exact AffineSoftmaxPredictor.proximal_predictor_modulus hcompact hF hFcont hFg hG.le hf hFb
      state hA hx hv hdiam hx' hy'
  have hprob i μ (_hμ : μ ∈ Set.Icc floor cap) :
      (probeLaw : Measure ProbeSeed) {seed | r / 64 < |Program.eval reply (probe i seed μ) - min r (d μ)|} ≤
        ENNReal.ofReal ((1 / 4 : ℝ) ^ b) := by
    have hp := AffineSoftmaxSearchOracle.probePlan_global_failure m hX hcompact f
      (predictor (max floor μ) state) hL hG hr hτ (hf.trans_le (le_max_left floor μ)) hlocal
      hc hg hlip hbound (AffineSoftmaxPredictor.predictor_mem hX state
        (hf.trans_le (le_max_left floor μ)) hA hx hv) reply hm hreply b
    simpa only [probe, d, F, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4), ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hp
  have hD : 0 ≤ D := (norm_nonneg _).trans hdiam
  have hb := AffineSoftmaxSearchProbability.searchPlan_failure_bound probeLaw probe reply
    (fun _ => regularizationProbe_measurable m hX hcompact state hA hx hv τ L G hr hf b reply hm)
    d hd H hr hf hfc (by positivity : 0 ≤ 2 * D + G / floor) hdcap hend hmod hwidth
    (by positivity : 0 ≤ (1 / 4 : ℝ) ^ b) hprob
  apply le_trans (measure_mono ?_) hb
  intro seeds hbad hgood
  apply hbad
  simpa only [d, max_eq_right hgood.1.1, regularizationSearchPlan, probe, F] using hgood

end LongTails.Proofs.AffineSoftmaxSearchExecution
