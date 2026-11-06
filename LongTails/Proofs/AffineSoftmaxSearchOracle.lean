import LongTails.Proofs.AffineSoftmaxSearchProbability

namespace LongTails.Proofs.AffineSoftmaxSearchOracle

open MeasureTheory
open scoped ENNReal
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxSearch

lemma probePlan_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L G r μ : ℝ) (project : E → E)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (probePlan m center τ L G r μ project seeds b) =
      ‖Program.eval reply (boostedCachedPlan m
        ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
        τ L G r μ (μ * r ^ 2 / 32768) project seeds b) - center‖ := by
  simp only [probePlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]

lemma probePlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L G r μ : ℝ) (project : E → E)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (probePlan m center τ L G r μ project seeds b) = m +
      Program.cost reply (boostedCachedPlan m
        ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
        τ L G r μ (μ * r ^ 2 / 32768) project seeds b) := by
  simp only [probePlan, Program.cost_bind, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost,
    AffineSoftmaxExecution.cachePlan_eval]

lemma probePlan_param_measurable {E Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    (m : ℕ) [NeZero m] (center : Z → E) (τ L G r : ℝ) (μ : Z → ℝ)
    (hc : Measurable center) (hμ : Measurable μ)
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (reply : Fin m × E → ℝ × E) (hr : Measurable reply)
    (seeds : Z → ProbeSeed) (hs : ∀ a j k, Measurable (fun z => seeds z a j k)) (b : ℕ) :
    Measurable (fun z => Program.eval reply (probePlan m (center z) τ L G r (μ z) (project z) (seeds z) b)) := by
  let s := fun z => (⟨center z, (fun i => (reply (i, center z)).1),
    (fun i => (reply (i, center z)).2)⟩ : Snapshot (Fin m) E)
  have hb := AffineSoftmaxSearchProbability.boostedCachedPlan_param_measurable m s τ L G r μ
    (fun z => μ z * r ^ 2 / 32768) hc
    (fun i => (hr.comp (measurable_const.prodMk hc)).fst)
    (fun i => (hr.comp (measurable_const.prodMk hc)).snd)
    hμ ((hμ.mul_const _).div_const _) project hp reply hr seeds hs b
  simp_rw [probePlan_eval]
  exact (hb.sub hc).norm

lemma probePlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (center : E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hz : center ∈ C) (hradius : ∀ x ∈ C, ‖x - center‖ ≤ r)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ center) C u)
    (d : ℝ) (hclip : ‖u - center‖ = min r d) (b : ℕ) :
    (probeLaw : Measure ProbeSeed)
      {seeds | r / 64 < |Program.eval reply
        (probePlan m center τ L G r μ (OracleTemplate.SaddlePoint.project C) seeds b) - min r d|} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  have hv i : s.value i = f i s.anchor := by
    dsimp [s]
    rw [hreply i center hz]
  have hg' i : s.field i = gradient (f i) s.anchor := by
    dsimp [s]
    rw [hreply i center hz]
  have hb := AffineSoftmaxSearchProbability.boosted_displacement_probability m hC hcompact f s
    hL hG hr hτ hμ hcap hc hg hlip hbound hv hg' hz hradius reply hm hreply hu hmin b
  change (Measure.infinitePi (fun _ : ℕ =>
    (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure LongTails.Algorithms.AffineSoftmaxProx.ProxSeed))) _ ≤ _
  simp_rw [probePlan_eval]
  simpa only [s, hclip] using hb

lemma exactProx_local_displacement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E} {f : E → ℝ} (hcompact : IsCompact X)
    (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 ≤ r)
    {center : E} (hc : center ∈ X) :
    ‖AffineSoftmaxRegularization.exactProx (X ∩ Metric.closedBall center r) f μ center - center‖ =
      min r ‖AffineSoftmaxRegularization.exactProx X f μ center - center‖ := by
  have hlocalcompact : IsCompact (X ∩ Metric.closedBall center r) := hcompact.inter_right Metric.isClosed_closedBall
  have hcenter : center ∈ X ∩ Metric.closedBall center r :=
    ⟨hc, Metric.mem_closedBall_self hr⟩
  have hl := AffineSoftmaxRegularization.exactProx_spec hlocalcompact ⟨center, hcenter⟩
    (hfc.mono Set.inter_subset_left) μ center
  have hg := AffineSoftmaxRegularization.exactProx_spec hcompact ⟨center, hc⟩ hfc μ center
  exact AffineSoftmaxRegularization.local_min_displacement
    (AffineSoftmaxRegularization.regularized_convexOn hf hμ.le center) hg.1 hg.2
    (fun w hw hwm => AffineSoftmaxRegularization.exactProx_unique hf hμ center hw hg.1 hwm hg.2)
    hl.1 hl.2

lemma probePlan_global_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (center : E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (hz : center ∈ X)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (b : ℕ) :
    (probeLaw : Measure ProbeSeed)
      {seeds | r / 64 < |Program.eval reply
        (probePlan m center τ L G r μ
          (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall center r)) seeds b) -
          min r ‖AffineSoftmaxRegularization.exactProx X
            (fun z => smoothValue τ (fun i => f i z)) μ center - center‖|} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let C := X ∩ Metric.closedBall center r
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hcomp : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcenter : center ∈ C := ⟨hz, Metric.mem_closedBall_self hr.le⟩
  have hfc : ContinuousOn F X := by
    intro x hx
    exact (SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx)).continuousAt.continuousWithinAt
  have hfv : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hu := AffineSoftmaxRegularization.exactProx_spec hcomp ⟨center, hcenter⟩
    (hfc.mono Set.inter_subset_left) μ center
  have hclip := exactProx_local_displacement hcompact hfv hfc hμ hr.le hz
  exact probePlan_failure m hC hcomp f center hL hG hr hτ hμ hcap
    (fun i => (hc i).subset Set.inter_subset_left hC)
    (fun i x hx => hg i x hx.1)
    (fun i x y hx hy => hlip i x y hx.1 hy.1)
    (fun i x hx => hbound i x hx.1) hcenter
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.2)
    reply hm (fun i x hx => hreply i x hx.1) hu.1 hu.2 _ hclip b

end LongTails.Proofs.AffineSoftmaxSearchOracle
