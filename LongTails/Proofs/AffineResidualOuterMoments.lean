import LongTails.Proofs.AffineResidualOuterExecution
import LongTails.Proofs.AffineSoftmaxOuterMoments
import LongTails.Proofs.AffineSoftmaxOuterProcess

namespace LongTails.Proofs.AffineResidualOuterMoments

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineResidualSaddle (localPlan)
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot smoothValue)
open LongTails.Algorithms.CappedProximal
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)

lemma finalStepPlan_expected_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (state : State E) (hA : 0 ≤ state.weight)
    (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    {τ L G r D ε μ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hD : 0 < D) (hε : 0 < ε) (hμ : 0 < μ) (H : ℕ) (hH : 0 < H)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
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
      let out := Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed)
      T * (F out.primal - F xs) + ‖out.dual - xs‖ ^ 2 +
        μ * T / 8 * ‖predictor μ state - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤
      state.weight * (F state.primal - F xs) + ‖state.dual - xs‖ ^ 2 +
        T * φ + a * D * β + 3 * a ^ 2 / 4 * σ ^ 2 := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
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
  let x := fun seed : LocalSeed => Program.eval reply (localPlan C s τ μ L r φ seed)
  let g := fun seed : MultilevelSeed => Program.eval reply (cachedProxGradientPlan C s τ μ L r σ β seed)
  have hxm : Measurable x := AffineResidualLocal.localPlan_observable_measurable C s τ μ L r φ reply id
  have hxC seed : x seed ∈ C := AffineResidualLocal.localPlan_mem C s τ μ
    (fun i z => (reply (i, z)).1) (fun i z => (reply (i, z)).2)
    hCcompact ⟨center, hcC⟩ hC hμ hτ hL hφ seed
  have hgmeas : Measurable g := AffineResidualMultilevel.cachedProxGradientPlan_measurable C s τ μ L r reply σ β
  have hgm := AffineResidualMultilevel.oracle_prox_gradient_moments C s τ μ L r reply f
    hCcompact hC hμ hτ hL hσ hβ hcc hgg hll hbb hcC hvalue hfield hradius u huC hminC hreplyC
  have hprox : (∫ seed : FinalSeed, regularized F μ center (x seed.1) - regularized F μ center u
      ∂(finalLaw : Measure FinalSeed)) ≤ φ := by
    change (∫ seed : FinalSeed, regularized F μ center (x seed.1) - regularized F μ center u
      ∂(localLaw : Measure LocalSeed).prod (multilevelLaw : Measure MultilevelSeed)) ≤ φ
    rw [integral_fun_fst (fun seed : LocalSeed => regularized F μ center (x seed) - regularized F μ center u), probReal_univ, one_smul]
    have heval seed := AffineResidualExecution.eval_eq_of_queriesWithin reply
      (fun q => (f q.1 q.2, gradient (f q.1) q.2)) (fun q => q.2 ∈ C)
      (localPlan C s τ μ L r φ seed)
      (AffineResidualExecution.localPlan_queriesWithin hCcompact ⟨center, hcC⟩ _ _ _ _ _ _ _ _)
      (fun q hq => hreplyC q.1 q.2 hq)
    dsimp only [x]
    simp_rw [heval]
    exact AffineResidualLocal.localPlan_accuracy C s τ μ f (fun i => gradient (f i))
      hCcompact hC hμ hτ hL hφ hcc hgg hll hcC hvalue hfield hradius u huC
  have hbias : ‖(∫ seed : FinalSeed, g seed.2 ∂(finalLaw : Measure FinalSeed)) - μ • (center - u)‖ ≤ β := by
    change ‖(∫ seed : FinalSeed, g seed.2 ∂(localLaw : Measure LocalSeed).prod (multilevelLaw : Measure MultilevelSeed)) -
      μ • (center - u)‖ ≤ β
    rw [integral_fun_snd, probReal_univ, one_smul]
    exact hgm.2.1
  have hmse : (∫ seed : FinalSeed, ‖g seed.2 - μ • (center - u)‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤ σ ^ 2 := by
    change (∫ seed : FinalSeed, ‖g seed.2 - μ • (center - u)‖ ^ 2
      ∂(localLaw : Measure LocalSeed).prod (multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2
    rw [integral_fun_snd (fun seed : MultilevelSeed => ‖g seed - μ • (center - u)‖ ^ 2), probReal_univ, one_smul]
    exact hgm.2.2.2
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFg z (hz : z ∈ X) : HasGradientAt F (gradient F z) z := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) z)
      hτ.ne' (fun i => hg i z hz)
    rw [hh.gradient]
    exact hh
  have ha := CappedProximalGeometry.accelerated_weight_properties hμ hA
  have henergy := AffineSoftmaxOuter.outer_expected_energy finalLaw hcompact hF hFg hA ha.1.le hμ.le hβ.le
    (show T = state.weight + a from rfl) ha.2 state.primal state.dual center u xs hx hu hxs hdiam
    (AffineSoftmaxOuterMoments.predictor_balance state hμ hA) hmin (fun seed : FinalSeed => x seed.1) (fun seed : FinalSeed => g seed.2)
    (hxm.comp measurable_fst) (hgmeas.comp measurable_snd) (fun seed => (hxC seed.1).1)
    (hgm.1.comp_snd (localLaw : Measure LocalSeed))
    (hgm.2.2.1.comp_snd (localLaw : Measure LocalSeed)) hbias hmse hprox
  have he seed : Program.eval reply (finalStepPlan m X state τ L r D ε μ H seed) =
      (⟨T, x seed.1, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g seed.2)⟩ : State E) := by
    simp only [finalStepPlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]
    rfl
  dsimp only
  simp_rw [he]
  exact henergy

open AffineSoftmaxOuterProcess (StateSpace state)

lemma finalStepPlan_expected_drift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (s : StateSpace X)
    {τ L G r D ε μ t : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (hD : 0 < D) (hε : 0 < ε) (hμ : 0 < μ) (H : ℕ) (hH : 3 ≤ H)
    (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hweightcap : (state s).weight ≤ 100 * D ^ 2 / ε)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X → ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i z, z ∈ X → reply (i, z) = (f i z, gradient (f i) z))
    (xs u : E) (hxs : xs ∈ X) (hu : u ∈ X) (hdiam : ‖(state s).dual - xs‖ ≤ D)
    (hmin : IsMinOn (RecursiveEnvelopeGeometry.regularized
      (fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)) μ (predictor μ (state s))) X u)
    (hur : ‖u - predictor μ (state s)‖ ≤ r)
    (hvalid : μ ≤ 2 * (ε * (H : ℝ) ^ 2 / (t * r ^ 2)) ∨ 3 * r / 4 ≤ ‖predictor μ (state s) - u‖) :
    let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
    let a := nextWeight μ (state s).weight
    let T := (state s).weight + a
    (∫ seed : FinalSeed,
      let out := Program.eval reply (finalStepPlan m X (state s) τ L r D ε μ H seed)
      T * (F out.primal - F xs) + ‖out.dual - xs‖ ^ 2 - ε / 100 * T +
        μ * T / 16 * ‖predictor μ (state s) - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤
      (state s).weight * (F (state s).primal - F xs) + ‖(state s).dual - xs‖ ^ 2 - ε / 100 * (state s).weight := by
  let F := fun z => LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => f i z)
  let a := nextWeight μ (state s).weight
  let T := (state s).weight + a
  let out := fun seed : FinalSeed => Program.eval reply (finalStepPlan m X (state s) τ L r D ε μ H seed)
  let pot := fun seed : FinalSeed => T * (F (out seed).primal - F xs) + ‖(out seed).dual - xs‖ ^ 2
  have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : 0 < H := by omega
  have hraw := finalStepPlan_expected_energy m hX hcompact f (state s)
    s.property.1 s.property.2.1 s.property.2.2 hτ hL hr hD hε hμ H hHpos
    hc hg hlip hbound reply hreply xs u hxs hu hdiam hmin hur
  have hout := AffineResidualOuterExecution.finalStepPlan_measurable m hX hcompact ⟨xs, hxs⟩
    (state s) τ L r D ε μ H reply
  let encode := fun q : State E => (q.weight, q.primal, q.dual)
  have hfinite : (Set.range (fun seed => encode (out seed))).Finite :=
    ((AffineResidualOuterExecution.finalStepPlan_finite_range m X (state s) τ L r D ε μ H reply).image encode).subset
      (by rintro _ ⟨seed, rfl⟩; exact ⟨out seed, ⟨seed, rfl⟩, rfl⟩)
  have hpi : Integrable pot (finalLaw : Measure FinalSeed) :=
    AffineResidualOuterExecution.integrable_observable_finite (fun seed => encode (out seed))
      (fun q => T * (F q.2.1 - F xs) + ‖q.2.2 - xs‖ ^ 2)
      (hout.1.prodMk (hout.2.1.prodMk hout.2.2)) hfinite _
  have ha := CappedProximalGeometry.accelerated_weight_properties hμ s.property.1
  have herr := AffineSoftmaxOuterBounds.final_error_bound hμ s.property.1 ha.1 hr hHreal hε ht hscale ha.2 hweightcap hvalid
  have hsqrt : (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3))) ^ 2 =
      μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3) := Real.sq_sqrt (by positivity)
  dsimp only at hraw
  rw [hsqrt] at hraw
  have hbias : a * D * (ε / (1000 * D)) = a * ε / 1000 := by field_simp
  change (∫ seed, pot seed + μ * T / 8 * ‖predictor μ (state s) - u‖ ^ 2 ∂(finalLaw : Measure FinalSeed)) ≤ _ at hraw
  rw [integral_add hpi (integrable_const _), integral_const, probReal_univ, one_smul] at hraw
  change (∫ seed, pot seed - ε / 100 * T + μ * T / 16 * ‖predictor μ (state s) - u‖ ^ 2
    ∂(finalLaw : Measure FinalSeed)) ≤ _
  have hpis : Integrable (fun seed => pot seed - ε / 100 * T) (finalLaw : Measure FinalSeed) :=
    hpi.sub (integrable_const _)
  rw [integral_add hpis (integrable_const _),
    integral_sub hpi (integrable_const (ε / 100 * T)), integral_const, integral_const, probReal_univ, one_smul, one_smul]
  dsimp only [a, T] at hbias ⊢
  rw [hbias] at hraw
  dsimp only [a, T, F, state, nextWeight] at hraw herr ⊢
  nlinarith only [hraw, herr]

end LongTails.Proofs.AffineResidualOuterMoments
