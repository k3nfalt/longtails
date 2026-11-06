import LongTails.Proofs.AffineSoftmaxSearchGeometry
import LongTails.Proofs.AffineSoftmaxBallSolver

namespace LongTails.Proofs.AffineSoftmaxSearchProbability

open MeasureTheory
open scoped ENNReal

lemma visited_failure_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (X : ℕ → (ℕ → Ω) → S)
    (hX : ∀ k, Measurable (X k))
    (hdep : ∀ k ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X k ξ = X k ξ')
    (bad : ℕ → S → Ω → Prop)
    (hm : ∀ k, MeasurableSet {z : S × Ω | bad k z.1 z.2})
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ k x, (Q : Measure Ω) {ω | bad k x ω} ≤ ENNReal.ofReal p) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {ξ | ∃ k < n, bad k (X k ξ) (ξ k)} ≤ ENNReal.ofReal ((n : ℝ) * p) := by
  classical
  let Φ : ℕ → S → Ω → ℝ := fun k x ω => if bad k x ω then 1 else 0
  have hsection k x : MeasurableSet {ω | bad k x ω} :=
    (hm k).preimage (measurable_const.prodMk measurable_id)
  have hΦ k : Measurable (Function.uncurry (Φ k)) :=
    Measurable.ite (hm k) measurable_const measurable_const
  have hn k x ω : 0 ≤ Φ k x ω := by dsimp [Φ]; split_ifs <;> norm_num
  have heq k x : Φ k x = {ω | bad k x ω}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [Φ, Set.indicator_apply, Set.mem_ofPred_eq]
  have hi k x : Integrable (Φ k x) (Q : Measure Ω) := by
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator (hsection k x)
  have hmean k x : (∫ ω, Φ k x ω ∂(Q : Measure Ω)) ≤ p := by
    rw [heq, integral_indicator_const _ (hsection k x)]
    simp only [smul_eq_mul, mul_one]
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (hb k x)
    simpa only [measureReal_def, ENNReal.toReal_ofReal hp] using hh
  have hbound := AffineSoftmaxSearchTrace.prefix_failure_sum_bound Q X hX hdep Φ hΦ hn hi hmean n
  apply le_trans (measure_mono ?_) hbound
  intro ξ hξ
  rcases hξ with ⟨k, hk, hbad⟩
  have hterm : Φ k (X k ξ) (ξ k) = 1 := by simp [Φ, hbad]
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range n) => hn j (X j ξ) (ξ j))
    (Finset.mem_range.mpr hk)
  change 1 ≤ ∑ j ∈ Finset.range n, Φ j (X j ξ) (ξ j)
  simpa only [hterm] using hh

open AffineSoftmaxSearchTrace

noncomputable def query (floor cap : ℝ) (i : ℕ) (state : State) : ℝ :=
  if state.1 = 0 then max floor (cap / 2 ^ i) else (state.2.1 + state.2.2) / 2

def Active (H i : ℕ) (state : State) : Prop := state.1 = 0 ∨ (state.1 = 1 ∧ H < i)

lemma query_measurable (floor cap : ℝ) (i : ℕ) : Measurable (query floor cap i) := by
  unfold query
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
    ((measurable_snd.fst.add measurable_snd.snd).div_const 2)

lemma active_measurable (H i : ℕ) : MeasurableSet {state : State | Active H i state} := by
  unfold Active
  apply MeasurableSet.union (measurableSet_eq_fun measurable_fst measurable_const)
  exact (measurableSet_eq_fun measurable_fst measurable_const).inter (MeasurableSet.const _)

lemma query_range {floor cap : ℝ} (hc : 0 ≤ cap) (hfc : floor ≤ cap)
    (i : ℕ) (state : State) (hl : state.2.1 ∈ Set.Icc floor cap)
    (hu : state.2.2 ∈ Set.Icc floor cap) : query floor cap i state ∈ Set.Icc floor cap := by
  unfold query
  split_ifs
  · exact ⟨le_max_left _ _, max_le hfc (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))⟩
  · constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]

lemma search_bad_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (observe : ℕ → Ω → ℝ → ℝ)
    (ho : ∀ i, Measurable (Function.uncurry (observe i)))
    (d : ℝ → ℝ) (hd : Measurable d) (r floor cap : ℝ) (H : ℕ)
    {p : ℝ} (hp : 0 ≤ p)
    (hprob : ∀ i μ, μ ∈ Set.Icc floor cap →
      (Q : Measure Ω) {ω | r / 64 < |observe i ω μ - min r (d μ)|} ≤ ENNReal.ofReal p) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {ξ | ∃ i < n,
        let state := trajectory (fun k => observe k (ξ k)) r floor cap H i
        Active H i state ∧ query floor cap i state ∈ Set.Icc floor cap ∧
          r / 64 < |observe i (ξ i) (query floor cap i state) - min r (d (query floor cap i state))|} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  let X := fun (i : ℕ) (ξ : ℕ → Ω) => trajectory (fun k => observe k (ξ k)) r floor cap H i
  let bad := fun i (state : State) ω => Active H i state ∧
    query floor cap i state ∈ Set.Icc floor cap ∧
      r / 64 < |observe i ω (query floor cap i state) - min r (d (query floor cap i state))|
  apply visited_failure_bound Q X (fun i => seeded_trajectory_measurable observe ho r floor cap H i)
    (fun i ξ ξ' h => seeded_trajectory_prefix observe r floor cap H i ξ ξ' h) bad ?_ hp ?_ n
  · intro i
    have hq : Measurable (fun z : State × Ω => query floor cap i z.1) :=
      (query_measurable floor cap i).comp measurable_fst
    have hv : Measurable (fun z : State × Ω =>
        |observe i z.2 (query floor cap i z.1) - min r (d (query floor cap i z.1))|) :=
      by
        have hv' : Measurable (fun z : State × Ω =>
            observe i z.2 (query floor cap i z.1) - min r (d (query floor cap i z.1))) :=
          ((ho i).comp (measurable_snd.prodMk hq)).sub (measurable_const.min (hd.comp hq))
        simpa only [Real.norm_eq_abs] using hv'.norm
    exact ((active_measurable H i).preimage measurable_fst).inter
      ((measurableSet_Icc.preimage hq).inter (measurableSet_lt measurable_const hv))
  · intro i state
    by_cases hq : query floor cap i state ∈ Set.Icc floor cap
    · exact (measure_mono (fun ω h => h.2.2)).trans (hprob i _ hq)
    · have he : {ω | bad i state ω} = ∅ := by
        ext ω
        simp only [bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hq h.2.1
      rw [he, measure_empty]
      exact bot_le

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

lemma searchPlan_failure_bound {Ω Q R : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (probe : ℕ → Ω → ℝ → Program Q R ℝ) (reply : Q → R)
    (ho : ∀ i, Measurable (fun z : Ω × ℝ => Program.eval reply (probe i z.1 z.2)))
    (d : ℝ → ℝ) (hd : Measurable d) {r floor cap K : ℝ} (H : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64)
    {p : ℝ} (hp : 0 ≤ p)
    (hprob : ∀ i μ, μ ∈ Set.Icc floor cap →
      (P : Measure Ω) {ω | r / 64 < |Program.eval reply (probe i ω μ) - min r (d μ)|} ≤ ENNReal.ofReal p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {ξ | let answer := Program.eval reply (searchPlan (fun i => probe i (ξ i)) r floor cap H)
        ¬ (answer ∈ Set.Icc floor cap ∧
          ((answer = floor ∧ d answer < r) ∨ (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)))} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * p) := by
  let observe := fun i ω μ => Program.eval reply (probe i ω μ)
  have hb := search_bad_event_bound P observe ho d hd r floor cap H hp hprob (2 * H + 9)
  apply le_trans (measure_mono ?_) hb
  intro ξ hfail
  by_contra hgood
  apply hfail
  apply AffineSoftmaxSearchGeometry.searchPlan_certificate d (fun i => probe i (ξ i)) reply H
    hr hf hfc hK hcap hend hmod hs
  · intro i hi previous heq
    apply le_of_not_gt
    intro herror
    apply hgood
    refine ⟨i, hi, ?_⟩
    have hrange := trajectory_range (observe := fun k => observe k (ξ k)) r (hf.le.trans hfc) hfc H i
    have hqr := query_range (hf.le.trans hfc) hfc i _ hrange.1 hrange.2
    change trajectory (fun k => observe k (ξ k)) r floor cap H i = scan previous at heq
    rw [heq] at hqr ⊢
    exact ⟨Or.inl rfl, hqr, by simpa only [query, scan, Prod.fst, ite_true, observe] using herror⟩
  · intro i hi lower upper heq hit
    apply le_of_not_gt
    intro herror
    apply hgood
    refine ⟨i, hi, ?_⟩
    have hrange := trajectory_range (observe := fun k => observe k (ξ k)) r (hf.le.trans hfc) hfc H i
    have hqr := query_range (hf.le.trans hfc) hfc i _ hrange.1 hrange.2
    change trajectory (fun k => observe k (ξ k)) r floor cap H i = bracket lower upper at heq
    rw [heq] at hqr ⊢
    refine ⟨Or.inr ⟨rfl, hit⟩, hqr, ?_⟩
    simpa only [query, bracket, Prod.fst, Prod.snd, show ¬ (1 : ℕ) = 0 by decide, ite_false, observe] using herror

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)

lemma boosted_gap_probability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (s : Snapshot (Fin m) E) {L G r τ μ δ : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ) (hδ : 0 < δ)
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
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u)
    (b : ℕ) :
    let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
    (Measure.infinitePi (fun _ : ℕ => (proxLaw : Measure _)))
      {seeds | 4 * δ < F (Program.eval reply
        (boostedCachedPlan m s τ L G r μ δ (OracleTemplate.SaddlePoint.project C) seeds b)) - F u} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
  let out := fun seed => Program.eval reply
    (cachedProxPlan s τ L G r μ δ (OracleTemplate.SaddlePoint.project C) seed)
  have hp : ∀ x, OracleTemplate.SaddlePoint.project C x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hC x).1
  have hpc : Continuous (OracleTemplate.SaddlePoint.project C) :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hC).continuous
  have hom : Measurable out := AffineSoftmaxBallSolver.cachedProxPlan_measurable s τ L G r μ δ _ hpc reply hm
  have hmem seed : out seed ∈ C := AffineSoftmaxBallSolver.cachedProxPlan_mem hC s τ L G r μ δ _ hp hz reply seed
  have hgeom := AffineSoftmaxBallSolver.regularized_geometry hC f hτ hG.le hμ.le hc hg hlip hbound s.anchor
  have hfc : ContinuousOn F C := hgeom.2.1
  have hgapm : Measurable (fun seed => F (out seed) - F u) :=
    (hfc.domRestrict.measurable.comp (hom.subtype_mk (h := hmem))).sub measurable_const
  have hgapi := ConstrainedStochasticAcceleration.integrable_compact_image proxLaw hcompact
    (fun x => F x - F u) (hfc.sub continuousOn_const) out hom hmem
  apply AffineSoftmaxSearch.boostedCachedPlan_failure m s τ L G r μ hδ
    (OracleTemplate.SaddlePoint.project C) reply b F u
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
  · exact hgapm
  · exact hgapi
  · intro seed
    exact sub_nonneg.mpr (hmin (hmem seed))
  · exact AffineSoftmaxBallSolver.cached_restart_accuracy hC hcompact f s hL hG hr hτ hμ hδ
      hcap hc hg hlip hbound hvalue hfield hz hradius reply hm hreply hu hmin

lemma regularized_observation_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) (center : E) {u approximate : E}
    (hu : u ∈ C) (ha : approximate ∈ C) (hmin : IsMinOn (regularized f μ center) C u)
    (he : r / 64 < |‖approximate - center‖ - ‖u - center‖|) :
    4 * (μ * r ^ 2 / 32768) < regularized f μ center approximate - regularized f μ center u := by
  have hn := AffineSoftmaxSearch.observation_error center u approximate (le_refl ‖approximate - u‖)
  have hnorm : r / 64 < ‖approximate - u‖ := he.trans_le hn
  have hsq : (r / 64) ^ 2 < ‖approximate - u‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hnorm
  have hgrowth := AffineSoftmaxRegularization.regularized_growth_on hf hg μ center hu ha hmin
  calc
    4 * (μ * r ^ 2 / 32768) = μ / 2 * (r / 64) ^ 2 := by ring
    _ < μ / 2 * ‖approximate - u‖ ^ 2 := mul_lt_mul_of_pos_left hsq (by positivity)
    _ ≤ regularized f μ center approximate - regularized f μ center u := hgrowth

lemma boosted_displacement_probability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : Fin m → E → ℝ) (s : Snapshot (Fin m) E) {L G r τ μ : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ)
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
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u)
    (b : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (proxLaw : Measure _)))
      {seeds | r / 64 < |‖Program.eval reply
        (boostedCachedPlan m s τ L G r μ (μ * r ^ 2 / 32768)
          (OracleTemplate.SaddlePoint.project C) seeds b) - s.anchor‖ - ‖u - s.anchor‖|} ≤
      (1 / 4 : ℝ≥0∞) ^ b := by
  have hδ : 0 < μ * r ^ 2 / 32768 := by positivity
  have hb := boosted_gap_probability m hC hcompact f s hL hG hr hτ hμ hδ hcap hc hg hlip hbound
    hvalue hfield hz hradius reply hm hreply hu hmin b
  apply le_trans (measure_mono ?_) hb
  intro seeds he
  have hp : ∀ x, OracleTemplate.SaddlePoint.project C x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hC x).1
  have hmem := AffineSoftmaxSearch.boostedCachedPlan_mem m s τ L G r μ (μ * r ^ 2 / 32768)
    (OracleTemplate.SaddlePoint.project C) seeds b reply hz
    (fun seed => AffineSoftmaxBallSolver.cachedProxPlan_mem hC s τ L G r μ (μ * r ^ 2 / 32768) _ hp hz reply seed)
  have hfg (x : E) (hx : x ∈ C) :
      HasGradientAt (fun z => smoothValue τ (fun i => f i z))
        (gradient (fun z => smoothValue τ (fun i => f i z)) x) x := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  exact regularized_observation_gap
    (SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hC hc hg hbound) hfg hμ hr s.anchor hu hmem hmin he

lemma boostedCachedPlan_param_measurable {E Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    (m : ℕ) [NeZero m] (s : Z → Snapshot (Fin m) E) (τ L G r : ℝ) (μ δ : Z → ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i))
    (hμ : Measurable μ) (hδ : Measurable δ)
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (reply : Fin m × E → ℝ × E) (hr : Measurable reply)
    (seeds : Z → ℕ → ProxSeed) (hs : ∀ a j k, Measurable (fun z => seeds z a j k)) (b : ℕ) :
    Measurable (fun z => Program.eval reply
      (boostedCachedPlan m (s z) τ L G r (μ z) (δ z) (project z) (seeds z) b)) := by
  let out := fun z j => Program.eval reply
    (cachedProxPlan (s z) τ L G r (μ z) (δ z) (project z) (seeds z j))
  have hom j : Measurable (fun z => out z j) :=
    AffineSoftmaxBallSolver.cachedProxPlan_param_measurable s τ L G r μ δ ha hv hg hμ hδ
      project hp reply hr (fun z => seeds z j) (hs j)
  have hscore j := AffineSoftmaxSearch.regularizedScorePlan_measurable m τ μ hμ
    (fun z => (s z).anchor) (fun z => out z j) ha (hom j) reply hr
  have hinitial : Measurable (fun z => ((s z).anchor, smoothValue τ (s z).value)) := by
    apply ha.prodMk
    unfold smoothValue
    exact ((Finset.measurable_sum _ (fun i _ => ((hv i).div_const τ).exp)).log.const_mul τ)
  unfold boostedCachedPlan
  simp only [Program.eval_map]
  apply Measurable.fst
  apply AffineSoftmaxSearch.selectTrialsPlan_measurable _ _ reply hinitial
  intro j
  simpa only [Program.eval_bind, Program.eval_map, out] using (hom j).prodMk (hscore j)

end LongTails.Proofs.AffineSoftmaxSearchProbability
