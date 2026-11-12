import LongTails.Algorithms.AffineResidualSearch
import LongTails.Proofs.AffineResidualLocal
import LongTails.Proofs.AffineSoftmaxSearchOracle

namespace LongTails.Proofs.AffineResidualSearch

open MeasureTheory
open scoped ENNReal
open LongTails.Algorithms.AffineResidualSaddle (localPlan)
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot smoothValue)
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSearch
open LongTails.Algorithms.AffineResidualProx (localLaw LocalSeed)
open LongTails.Algorithms.AffineSoftmaxSearch (selectTrialsPlan regularizedScorePlan)
open LongTails.Proofs.AffineSoftmaxSearch (selectTrialsPlan_eval_property selectTrialsPlan_score_le_trial
  independent_selection_failure expected_gap_failure selectTrialsPlan_cost regularizedScorePlan_cost)

lemma boostedCachedPlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ μ L r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (reply : Fin m × E → ℝ × E) (b : ℕ) (F : E → ℝ) (u : E)
    (hanchor : LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value = F s.anchor)
    (hscore : ∀ seed, Program.eval reply (regularizedScorePlan m τ μ s.anchor
      (Program.eval reply (LongTails.Algorithms.AffineResidualSaddle.localPlan
        C s τ μ L r δ seed))) =
      F (Program.eval reply (LongTails.Algorithms.AffineResidualSaddle.localPlan
        C s τ μ L r δ seed)))
    (hm : Measurable (fun seed => F (Program.eval reply
      (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed)) - F u))
    (hi : Integrable (fun seed => F (Program.eval reply
      (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed)) - F u)
      (localLaw : Measure _))
    (hn : ∀ seed, 0 ≤ F (Program.eval reply
      (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed)) - F u)
    (he : (∫ seed, F (Program.eval reply
      (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed)) - F u
      ∂(localLaw : Measure _)) ≤ δ) :
    (Measure.infinitePi (fun _ : ℕ =>
      (localLaw : Measure _)))
      {seeds | 4 * δ < F (Program.eval reply
        (boostedCachedPlan m C s τ μ L r δ seeds b)) - F u} ≤ (1 / 4 : ℝ≥0∞) ^ b := by
  let out := fun seed => Program.eval reply
    (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed)
  let trial := fun seed =>
    (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed).bind fun x =>
      (regularizedScorePlan m τ μ s.anchor x).map fun score => (x, score)
  have htrial (seed) : Program.eval reply (trial seed) = (out seed, F (out seed)) := by
    simp only [trial, Program.eval_bind, Program.eval_map, hscore, out]
  let initial := (s.anchor, LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value)
  let best := fun seeds : ℕ → LocalSeed => Program.eval reply (selectTrialsPlan (fun j => trial (seeds j)) initial b)
  have hbest (seeds) : (best seeds).2 = F (best seeds).1 := by
    exact selectTrialsPlan_eval_property (fun j => trial (seeds j)) initial reply
      (fun z => z.2 = F z.1) hanchor (fun j => by rw [htrial]) b
  have hout (seeds) : Program.eval reply
      (boostedCachedPlan m C s τ μ L r δ seeds b) = (best seeds).1 := by
    simp only [boostedCachedPlan, Program.eval_map, best, initial, trial]
  apply independent_selection_failure localLaw
    (fun seed => F (out seed) - F u) hm _ b (4 * δ) (1 / 4)
  · intro seeds j hj
    have hh := selectTrialsPlan_score_le_trial (fun j => trial (seeds j)) initial reply b j hj
    change (best seeds).2 ≤ (Program.eval reply (trial (seeds j))).2 at hh
    rw [hbest, htrial] at hh
    rw [hout]
    exact sub_le_sub_right hh (F u)
  · exact expected_gap_failure localLaw _ hδ hi hn he

lemma boostedCachedPlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ μ L r δ : ℝ)
    (seeds : ℕ → LocalSeed) (b : ℕ)
    (reply : Fin m × E → ℝ × E) :
    Program.cost reply (boostedCachedPlan m C s τ μ L r δ seeds b) =
      (∑ j ∈ Finset.range b, Program.cost reply
        (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ (seeds j))) + b * m := by
  simp only [boostedCachedPlan, Program.cost_map, selectTrialsPlan_cost,
    Program.cost_bind, regularizedScorePlan_cost, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]

lemma boostedCachedPlan_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ μ L r δ : ℝ)
    (seeds : ℕ → LocalSeed) (b : ℕ)
    (reply : Fin m × E → ℝ × E) (ha : s.anchor ∈ C)
    (ho : ∀ seed, Program.eval reply
      (LongTails.Algorithms.AffineResidualSaddle.localPlan C s τ μ L r δ seed) ∈ C) :
    Program.eval reply (boostedCachedPlan m C s τ μ L r δ seeds b) ∈ C := by
  simp only [boostedCachedPlan, Program.eval_map]
  apply selectTrialsPlan_eval_property _ _ reply (fun z => z.1 ∈ C) ha
  intro j
  simpa only [Program.eval_bind, Program.eval_map] using ho (seeds j)


lemma boostedCachedPlan_cost_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (s : Snapshot (Fin m) E) (τ μ L r δ : ℝ)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (boostedCachedPlan m C s τ μ L r δ seeds b) =
      b * (2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ μ L r δ + m) := by
  rw [boostedCachedPlan_cost]
  simp only [AffineResidualExecution.localPlan_cost, Fintype.card_fin,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
  ring

lemma boostedCachedPlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (m : ℕ) [NeZero m] (C : Set E) (s : Snapshot (Fin m) E) (τ μ L r δ : ℝ)
    (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds => Program.eval reply (boostedCachedPlan m C s τ μ L r δ seeds b)) := by
  simp only [boostedCachedPlan, Program.eval_map]
  apply Measurable.fst
  apply AffineSoftmaxSearch.selectTrialsPlan_measurable _ _ reply measurable_const _ b
  intro j
  simp only [Program.eval_bind, Program.eval_map]
  exact (AffineResidualLocal.localPlan_observable_measurable C s τ μ L r δ reply
    (fun x => (x, Program.eval reply (regularizedScorePlan m τ μ s.anchor x)))).comp (measurable_pi_apply j)

lemma boostedCachedPlan_queriesWithin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {C : Set E} (hcompact : IsCompact C) (hC : Convex ℝ C) (hne : C.Nonempty)
    (s : Snapshot (Fin m) E) {τ μ L r δ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    AffineSoftmaxQuerySafety.QueriesWithin reply (fun q => q.2 ∈ C)
      (boostedCachedPlan m C s τ μ L r δ seeds b) := by
  apply AffineSoftmaxQuerySafety.queriesWithin_map
  apply AffineSoftmaxQuerySafety.selectTrialsPlan_queries
  intro j
  apply AffineSoftmaxQuerySafety.queriesWithin_bind
  · exact AffineResidualExecution.localPlan_queriesWithin hcompact hne _ _ _ _ _ _ _ _
  · apply AffineSoftmaxQuerySafety.queriesWithin_map
    apply AffineSoftmaxQuerySafety.queriesWithin_map
    apply AffineSoftmaxQuerySafety.cachePlan_queries
    exact AffineResidualLocal.localPlan_mem C s τ μ (fun i x => (reply (i, x)).1)
      (fun i x => (reply (i, x)).2) hcompact hne hC hμ hτ hL hδ (seeds j)

lemma boosted_gap_probability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (s : Snapshot (Fin m) E) {L r τ μ δ : ℝ}
    (hL : 0 ≤ L) (hτ : 0 < τ) (hμ : 0 < μ) (hδ : 0 < δ)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u)
    (b : ℕ) :
    let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
    (Measure.infinitePi (fun _ : ℕ => (localLaw : Measure _)))
      {seeds | 4 * δ < F (Program.eval reply
        (boostedCachedPlan m C s τ μ L r δ seeds b)) - F u} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
  let out := fun seed => Program.eval reply (localPlan C s τ μ L r δ seed)
  have heval (seed : LocalSeed) := AffineResidualExecution.eval_eq_of_queriesWithin reply
    (fun q => (f q.1 q.2, gradient (f q.1) q.2)) (fun q => q.2 ∈ C)
    (localPlan C s τ μ L r δ seed)
    (AffineResidualExecution.localPlan_queriesWithin hcompact ⟨s.anchor, hz⟩ s τ μ L r δ seed reply)
    (fun q hq => hreply q.1 q.2 hq)
  have hmem seed : out seed ∈ C := by
    dsimp only [out]
    rw [heval]
    exact AffineResidualLocal.localPlan_mem C s τ μ f (fun i => gradient (f i))
      hcompact ⟨s.anchor, hz⟩ hC hμ hτ hL hδ seed
  apply boostedCachedPlan_failure m C s τ μ L r hδ reply b F u
  · dsimp [F, regularized]
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    congr 1
    exact funext hvalue
  · intro seed
    rw [AffineSoftmaxSearch.regularizedScorePlan_eval]
    change smoothValue τ (fun i => (reply (i, out seed)).1) + μ / 2 * ‖out seed - s.anchor‖ ^ 2 = F (out seed)
    have he : (fun i => (reply (i, out seed)).1) = (fun i => f i (out seed)) := by
      funext i
      rw [hreply i _ (hmem seed)]
    rw [he]
    rfl
  · exact AffineResidualLocal.localPlan_observable_measurable C s τ μ L r δ reply (fun x => F x - F u)
  · exact AffineResidualLocal.localPlan_observable_integrable C s τ μ L r δ reply (fun x => F x - F u) _
  · intro seed
    exact sub_nonneg.mpr (hmin (hmem seed))
  · simp_rw [heval]
    exact AffineResidualLocal.localPlan_accuracy C s τ μ f (fun i => gradient (f i))
      hcompact hC hμ hτ hL hδ hc hg hlip hz hvalue hfield hradius u hu

lemma boosted_displacement_probability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (s : Snapshot (Fin m) E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u)
    (b : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (localLaw : Measure _)))
      {seeds | r / 64 < |‖Program.eval reply
        (boostedCachedPlan m C s τ μ L r (μ * r ^ 2 / 32768) seeds b) - s.anchor‖ - ‖u - s.anchor‖|} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  have hδ : 0 < μ * r ^ 2 / 32768 := by positivity
  have hb := boosted_gap_probability m hC hcompact f s hL hτ hμ hδ hc hg hlip
    hvalue hfield hz hradius reply hreply hu hmin b
  apply le_trans (measure_mono ?_) hb
  intro seeds he
  have hlocal (seed : LocalSeed) : Program.eval reply
      (localPlan C s τ μ L r (μ * r ^ 2 / 32768) seed) ∈ C := by
    rw [AffineResidualExecution.eval_eq_of_queriesWithin reply
      (fun q => (f q.1 q.2, gradient (f q.1) q.2)) (fun q => q.2 ∈ C) _
      (AffineResidualExecution.localPlan_queriesWithin hcompact ⟨s.anchor, hz⟩ _ _ _ _ _ _ _ _)
      (fun q hq => hreply q.1 q.2 hq)]
    exact AffineResidualLocal.localPlan_mem C s τ μ f (fun i => gradient (f i))
      hcompact ⟨s.anchor, hz⟩ hC hμ hτ hL hδ seed
  have hmem := boostedCachedPlan_mem m C s τ μ L r (μ * r ^ 2 / 32768) seeds b reply hz hlocal
  have hfg (x : E) (hx : x ∈ C) :
      HasGradientAt (fun z => smoothValue τ (fun i => f i z))
        (gradient (fun z => smoothValue τ (fun i => f i z)) x) x := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  exact AffineSoftmaxSearchProbability.regularized_observation_gap
    (SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hC hc hg hbound) hfg hμ hr s.anchor hu hmem hmin he

lemma probePlan_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (center : E) (τ μ L r : ℝ)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (probePlan m C center τ μ L r seeds b) =
      ‖Program.eval reply (boostedCachedPlan m C
        ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
        τ μ L r (μ * r ^ 2 / 32768) seeds b) - center‖ := by
  simp only [probePlan, Program.eval_bind, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]

lemma probePlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (center : E) (τ μ L r : ℝ)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (probePlan m C center τ μ L r seeds b) = m +
      Program.cost reply (boostedCachedPlan m C
        ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
        τ μ L r (μ * r ^ 2 / 32768) seeds b) := by
  simp only [probePlan, Program.cost_bind, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost,
    AffineSoftmaxExecution.cachePlan_eval]

lemma probePlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (center : E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hz : center ∈ C) (hradius : ∀ x ∈ C, ‖x - center‖ ≤ r)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ center) C u)
    (d : ℝ) (hclip : ‖u - center‖ = min r d) (b : ℕ) :
    (probeLaw : Measure ProbeSeed)
      {seeds | r / 64 < |Program.eval reply
        (probePlan m C center τ μ L r seeds b) - min r d|} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  have hv i : s.value i = f i s.anchor := by
    dsimp [s]
    rw [hreply i center hz]
  have hg' i : s.field i = gradient (f i) s.anchor := by
    dsimp [s]
    rw [hreply i center hz]
  have hb := boosted_displacement_probability m hC hcompact f s
    hL hr hτ hμ hc hg hlip hbound hv hg' hz hradius reply hreply hu hmin b
  change (Measure.infinitePi (fun _ : ℕ =>
    (localLaw : Measure LocalSeed))) _ ≤ _
  simp_rw [probePlan_eval]
  simpa only [s, hclip] using hb

lemma probePlan_cost_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (C : Set E) (center : E) (τ μ L r : ℝ)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (probePlan m C center τ μ L r seeds b) = m +
      b * (2 * LongTails.Algorithms.AffineResidualSaddle.localSteps m τ μ L r (μ * r ^ 2 / 32768) + m) := by
  rw [probePlan_cost, boostedCachedPlan_cost_exact]

lemma probePlan_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (m : ℕ) [NeZero m]
    (C : Set E) (center : E) (τ μ L r : ℝ) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds => Program.eval reply (probePlan m C center τ μ L r seeds b)) := by
  simp_rw [probePlan_eval]
  exact ((boostedCachedPlan_measurable m C _ τ μ L r _ b reply).sub measurable_const).norm

lemma probePlan_queriesWithin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {C : Set E} (hcompact : IsCompact C) (hC : Convex ℝ C)
    (center : E) (hc : center ∈ C) {τ μ L r : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (seeds : ProbeSeed) (b : ℕ) (reply : Fin m × E → ℝ × E) :
    AffineSoftmaxQuerySafety.QueriesWithin reply (fun q => q.2 ∈ C)
      (probePlan m C center τ μ L r seeds b) := by
  apply AffineSoftmaxQuerySafety.queriesWithin_bind
  · exact AffineSoftmaxQuerySafety.cachePlan_queries m center reply hc
  · apply AffineSoftmaxQuerySafety.queriesWithin_map
    exact boostedCachedPlan_queriesWithin m hcompact hC ⟨center, hc⟩ _ hμ hτ hL (by positivity) seeds b reply

lemma probePlan_global_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (f : Fin m → E → ℝ) (center : E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i z, z ∈ X → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ X → x ∈ X →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ X → ‖gradient (f i) z‖ ≤ G)
    (hz : center ∈ X)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (b : ℕ) :
    (probeLaw : Measure ProbeSeed)
      {seeds | r / 64 < |Program.eval reply
        (probePlan m (X ∩ Metric.closedBall center r) center τ μ L r seeds b) -
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
  have hclip := AffineSoftmaxSearchOracle.exactProx_local_displacement hcompact hfv hfc hμ hr.le hz
  exact probePlan_failure m hC hcomp f center hL hr hτ hμ
    (fun i => (hc i).subset Set.inter_subset_left hC)
    (fun i x hx => hg i x hx.1)
    (fun i x y hx hy => hlip i x y hx.1 hy.1)
    (fun i x hx => hbound i x hx.1) hcenter
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.2)
    reply (fun i x hx => hreply i x hx.1) hu.1 hu.2 _ hclip b

end LongTails.Proofs.AffineResidualSearch
