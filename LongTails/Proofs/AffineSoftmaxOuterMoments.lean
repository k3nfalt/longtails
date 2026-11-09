import LongTails.Proofs.AffineSoftmaxOuterExecution

namespace LongTails.Proofs.AffineSoftmaxOuterMoments

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.CappedProximal
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)

lemma cached_gradient_standard_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (s : Snapshot (Fin m) E) {L G r τ μ σ β : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ) (hσ : 0 < σ) (hβ : 0 < β)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u) :
    let g := fun seed => Program.eval reply (cachedProxGradientPlan s τ L G r μ σ β
      (OracleTemplate.SaddlePoint.project C) seed)
    Measurable g ∧ Integrable g (multilevelLaw : Measure MultilevelSeed) ∧
      ‖(∫ seed, g seed ∂(multilevelLaw : Measure MultilevelSeed)) - μ • (s.anchor - u)‖ ≤ β ∧
      Integrable (fun seed => ‖g seed - μ • (s.anchor - u)‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) ∧
      (∫ seed, ‖g seed - μ • (s.anchor - u)‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlevel j := AffineSoftmaxBallSolver.levelPlan_distance_moments hC hcompact f s hL hG hr hτ hμ hδ
    hcap hc hg hlip hbound hvalue hfield hz hradius reply hm hreply hu hmin j
  refine ⟨AffineSoftmaxMultilevel.cachedProxGradientPlan_measurable s τ L G r μ σ β _ reply
    (fun j => (hlevel j).1), ?_⟩
  exact AffineSoftmaxMultilevel.cachedProxGradientPlan_moments s τ L G r hμ hσ hβ _ reply u
    (fun j => (hlevel j).2.2.1) (fun j => (hlevel j).2.2.2.1) (fun j => (hlevel j).2.2.2.2)

lemma predictor_balance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (state : State E) {μ : ℝ} (hμ : 0 < μ) (hA : 0 ≤ state.weight) :
    (state.weight + nextWeight μ state.weight) • predictor μ state =
      state.weight • state.primal + nextWeight μ state.weight • state.dual := by
  have ha := (AffineSoftmaxPredictor.ratio_properties hμ hA).1
  have hden : state.weight + nextWeight μ state.weight ≠ 0 := by linarith
  have h1 : (state.weight + nextWeight μ state.weight) *
      (state.weight / (state.weight + nextWeight μ state.weight)) = state.weight := by field_simp
  have h2 : (state.weight + nextWeight μ state.weight) *
      (nextWeight μ state.weight / (state.weight + nextWeight μ state.weight)) = nextWeight μ state.weight := by field_simp
  simp only [predictor, smul_add, smul_smul, h1, h2]

lemma finalStepPlan_expected_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (state : State E) (hA : 0 ≤ state.weight)
    (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    {τ L G r D ε μ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hD : 0 < D) (hε : 0 < ε) (hμ : 0 < μ) (H : ℕ) (hH : 0 < H)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (xs u : E) (hxs : xs ∈ X) (hu : u ∈ X) (hdiam : ‖state.dual - xs‖ ≤ D)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ (predictor μ state)) X u)
    (hur : ‖u - predictor μ state‖ ≤ r) :
    let F := fun z => smoothValue τ (fun i => f i z)
    let a := nextWeight μ state.weight
    let T := state.weight + a
    let φ := μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)
    let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
    let β := ε / (1000 * D)
    (∫ seed : FinalSeed,
      let out := Program.eval reply (finalStepPlan m X state τ L G r D ε μ H seed)
      T * (F out.primal - F xs) + ‖out.dual - xs‖ ^ 2 +
        μ * T / 8 * ‖predictor μ state - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤
      state.weight * (F state.primal - F xs) + ‖state.dual - xs‖ ^ 2 +
        T * φ + a * D * β + 3 * a ^ 2 / 4 * σ ^ 2 := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  let project := OracleTemplate.SaddlePoint.project C
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let φ := μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)
  let σ := Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))
  let β := ε / (1000 * D)
  let a := nextWeight μ state.weight
  let T := state.weight + a
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hφ : 0 < φ := by dsimp [φ]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hcenter : center ∈ X := AffineSoftmaxPredictor.predictor_mem hX state hμ hA hx hv
  have hC : Convex ℝ C := hX.inter (convex_closedBall center r)
  have hCcompact : IsCompact C := hcompact.inter_right Metric.isClosed_closedBall
  have hcC : center ∈ C := ⟨hcenter, Metric.mem_closedBall_self hr.le⟩
  have huC : u ∈ C := ⟨hu, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hur⟩
  have hminC : IsMinOn (regularized F μ center) C u := fun z hz => hmin hz.1
  have hcc i : ConvexOn ℝ C (f i) := (hc i).subset Set.inter_subset_left hC
  have hgg i z (hz : z ∈ C) := hg i z hz.1
  have hll i z x (hz : z ∈ C) (hx' : x ∈ C) := hlip i z x hz.1 hx'.1
  have hbb i z (hz : z ∈ C) := hbound i z hz.1
  have hvalue i : s.value i = f i s.anchor := by dsimp [s]; rw [hreply i center hcenter]
  have hfield i : s.field i = gradient (f i) s.anchor := by dsimp [s]; rw [hreply i center hcenter]
  have hradius z (hz : z ∈ C) : ‖z - s.anchor‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.2
  have hreplyC i z (hz : z ∈ C) := hreply i z hz.1
  have hp : ∀ z, project z ∈ C := fun z =>
    (OracleTemplate.SaddlePoint.project_spec ⟨center, hcC⟩ hCcompact hC z).1
  have hpc : Continuous project := (NondualProjection.project_lipschitz ⟨center, hcC⟩ hCcompact hC).continuous
  let x := fun seed : ProxSeed => Program.eval reply (cachedProxPlan s τ L G r μ φ project seed)
  let g := fun seed : MultilevelSeed => Program.eval reply (cachedProxGradientPlan s τ L G r μ σ β project seed)
  have hxm : Measurable x := AffineSoftmaxBallSolver.cachedProxPlan_measurable s τ L G r μ φ project hpc reply hm
  have hxC seed : x seed ∈ C := AffineSoftmaxBallSolver.cachedProxPlan_mem hC s τ L G r μ φ project hp hcC reply seed
  have hgm := cached_gradient_standard_moments m hC hCcompact f s hL hG hr hτ hμ hσ hβ hcap
    hcc hgg hll hbb hvalue hfield hcC hradius reply hm hreplyC huC hminC
  have hprox : (∫ seed : FinalSeed, regularized F μ center (x seed.1) - regularized F μ center u
      ∂(finalLaw : Measure FinalSeed)) ≤ φ := by
    change (∫ seed : FinalSeed, regularized F μ center (x seed.1) - regularized F μ center u
      ∂(proxLaw : Measure ProxSeed).prod (multilevelLaw : Measure MultilevelSeed)) ≤ φ
    rw [integral_fun_fst (fun seed : ProxSeed => regularized F μ center (x seed) - regularized F μ center u), probReal_univ, one_smul]
    exact AffineSoftmaxBallSolver.cached_restart_accuracy hC hCcompact f s hL hG hr hτ hμ hφ hcap
      hcc hgg hll hbb hvalue hfield hcC hradius reply hm hreplyC huC hminC
  have hbias : ‖(∫ seed : FinalSeed, g seed.2 ∂(finalLaw : Measure FinalSeed)) - μ • (center - u)‖ ≤ β := by
    change ‖(∫ seed : FinalSeed, g seed.2 ∂(proxLaw : Measure ProxSeed).prod (multilevelLaw : Measure MultilevelSeed)) -
      μ • (center - u)‖ ≤ β
    rw [integral_fun_snd, probReal_univ, one_smul]
    exact hgm.2.2.1
  have hmse : (∫ seed : FinalSeed, ‖g seed.2 - μ • (center - u)‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤ σ ^ 2 := by
    change (∫ seed : FinalSeed, ‖g seed.2 - μ • (center - u)‖ ^ 2
      ∂(proxLaw : Measure ProxSeed).prod (multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2
    rw [integral_fun_snd (fun seed : MultilevelSeed => ‖g seed - μ • (center - u)‖ ^ 2), probReal_univ, one_smul]
    exact hgm.2.2.2.2
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFg z (hz : z ∈ X) : HasGradientAt F (gradient F z) z := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)
    rw [hh.gradient]
    exact hh
  have ha := CappedProximalGeometry.accelerated_weight_properties hμ hA
  have henergy := AffineSoftmaxOuter.outer_expected_energy finalLaw hcompact hF hFg hA ha.1.le hμ.le hβ.le
    (show T = state.weight + a from rfl) ha.2 state.primal state.dual center u xs hx hu hxs hdiam
    (predictor_balance state hμ hA) hmin (fun seed : FinalSeed => x seed.1) (fun seed : FinalSeed => g seed.2)
    (hxm.comp measurable_fst) (hgm.1.comp measurable_snd) (fun seed => (hxC seed.1).1)
    (hgm.2.1.comp_snd (proxLaw : Measure ProxSeed))
    (hgm.2.2.2.1.comp_snd (proxLaw : Measure ProxSeed)) hbias hmse hprox
  have he seed : Program.eval reply (finalStepPlan m X state τ L G r D ε μ H seed) =
      (⟨T, x seed.1, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g seed.2)⟩ : State E) := by
    simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
    rfl
  dsimp only
  simp_rw [he]
  exact henergy

end LongTails.Proofs.AffineSoftmaxOuterMoments
