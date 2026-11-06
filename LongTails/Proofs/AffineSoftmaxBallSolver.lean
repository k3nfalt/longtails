import LongTails.Algorithms.AffineSoftmaxProx
import LongTails.Proofs.AffineSoftmaxRestarts
import LongTails.Proofs.AffineSoftmaxOracle

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxBallSolver

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.AffineSoftmaxAcceleration
open LongTails.Proofs.SmoothFiniteMaximumGeometry
open LongTails.Proofs.AffineSoftmaxRegularization
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma regularized_geometry {C : Set E} (hC : Convex ℝ C) (f : ι → E → ℝ)
    {τ L G μ : ℝ} (hτ : 0 < τ) (hG : 0 ≤ G) (hμ : 0 ≤ μ)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G) (c : E) :
    let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ c
    ConvexOn ℝ C F ∧ ContinuousOn F C ∧
      (∀ x ∈ C, HasGradientAt F (gradient F x) x) ∧
      (∀ x ∈ C, ∀ y ∈ C, ‖gradient F x - gradient F y‖ ≤
        (L + 2 * G ^ 2 / τ + μ) * ‖x - y‖) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  have hfg (x : E) (hx : x ∈ C) : HasGradientAt F (gradient F x) x := by
    have hh := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  have hrg (x : E) (hx : x ∈ C) := regularized_hasGradientAt (hfg x hx) μ c
  have he (x : E) (hx : x ∈ C) := (hrg x hx).gradient
  refine ⟨regularized_convexOn (smoothValue_convex f hτ hC hc hg hbound) hμ c,
    fun x hx => (hrg x hx).continuousAt.continuousWithinAt, ?_, ?_⟩
  · intro x hx
    rw [he x hx]
    exact hrg x hx
  · intro x hx y hy
    rw [he x hx, he y hy]
    exact regularized_field_lipschitz
      (fun z hz w hw => smoothValue_gradient_lipschitz f hτ hG hc hg hbound hlip hz hw)
      hμ c hx hy

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma initial_regularized_gap {C : Set E} (hC : Convex ℝ C) (f : ι → E → ℝ)
    {τ G μ r : ℝ} (hτ : 0 < τ) (hG : 0 ≤ G) (hμ : 0 ≤ μ)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    {c u : E} (hcC : c ∈ C) (hu : u ∈ C) (hd : ‖u - c‖ ≤ r) :
    regularized (fun z => smoothValue τ (fun i => f i z)) μ c c -
      regularized (fun z => smoothValue τ (fun i => f i z)) μ c u ≤ G * r := by
  have hfg (x : E) (hx : x ∈ C) :
      HasGradientAt (fun z => smoothValue τ (fun i => f i z))
        (gradient (fun z => smoothValue τ (fun i => f i z)) x) x := by
    have hh := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  have hb := bounded_gradient_value_difference (smoothValue_convex f hτ hC hc hg hbound)
    hfg (fun x hx => smoothValue_gradient_bound f hτ.ne' (fun i => hg i x hx)
      (fun i => hbound i x hx)) hcC hu
  rw [norm_sub_rev c u] at hb
  have hm := mul_le_mul_of_nonneg_left hd hG
  have hq : 0 ≤ μ / 2 * ‖u - c‖ ^ 2 := by positivity
  unfold regularized
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero]
  linarith [le_abs_self (smoothValue τ (fun i => f i c) - smoothValue τ (fun i => f i u))]

lemma cached_restart_accuracy {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : ι → E → ℝ) (s : Snapshot ι E) {L G r τ μ ε : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ) (hε : 0 < ε)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r)
    (reply : ι × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u) :
    let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
    let S := L + 2 * G ^ 2 / τ + μ
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    let D := fun j => restartScale S V μ (restartGap (G * r) j)
    let steps := fun j => restartSteps S V μ (restartGap (G * r) j)
    (∫ seeds : ℕ → ℕ → StepSeed,
      F (OracleTemplate.ComponentEnvelope.Program.eval reply
        (restartPlan s τ μ D steps (OracleTemplate.SaddlePoint.project C) s.anchor seeds
          (restartRounds (G * r) ε))) - F u
      ∂(Measure.infinitePi fun _ : ℕ =>
        (Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)))) ≤ ε := by
  let F := regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
  let S := L + 2 * G ^ 2 / τ + μ
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  let H := fun x seed => OracleTemplate.ComponentEnvelope.Program.eval reply
    (seededEstimatorPlan s τ x seed) + μ • (x - s.anchor)
  have hS : 0 < S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hgeom := regularized_geometry hC f hτ hG.le hμ.le hc hg hlip hbound s.anchor
  have hH := AffineSoftmaxOracle.regularized_field_measurable s τ μ reply hm
  have hmoment x (hx : x ∈ C) := AffineSoftmaxOracle.local_regularized_gradient_moments
    f s μ hL hG.le hr.le hτ hcap hc hg hlip hbound hvalue hfield hz hx
    (hradius x hx) reply (fun i => hreply i x hx)
  have hfg (x : E) (hx : x ∈ C) :
      HasGradientAt (fun z => smoothValue τ (fun i => f i z))
        (gradient (fun z => smoothValue τ (fun i => f i z)) x) x := by
    have hh := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  have hgrowth (x : E) (hx : x ∈ C) : μ / 2 * ‖x - u‖ ^ 2 ≤ F x - F u :=
    regularized_growth_on (smoothValue_convex f hτ hC hc hg hbound) hfg μ s.anchor hu hx hmin
  have hi : F s.anchor - F u ≤ G * r :=
    initial_regularized_gap hC f hτ hG.le hμ.le hc hg hbound hz hu (hradius u hu)
  have hh := AffineSoftmaxRestarts.restart_gap_bound stepLaw hC hcompact hS hV hμ
    (mul_pos hG hr) hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2 hu
    (fun x hx => hmin hx) hgrowth H hH
    (fun x hx => (hmoment x hx).1) (fun x hx => (hmoment x hx).2.1)
    (fun x hx => (hmoment x hx).2.2.1) (fun x hx => (hmoment x hx).2.2.2)
    hz hi (restartRounds (G * r) ε)
  dsimp only at hh ⊢
  simp only [AffineSoftmaxRestarts.restartPlan_eval]
  exact hh.trans (AffineSoftmaxRestarts.restartRounds_accuracy hε)

omit [CompleteSpace E] in
lemma cachedProxPlan_measurable (s : Snapshot ι E) (τ L G r μ ε : ℝ)
    (project : E → E) (hp : Continuous project) (reply : ι × E → ℝ × E)
    (hm : Measurable reply) :
    Measurable (fun seeds => OracleTemplate.ComponentEnvelope.Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ ε project seeds)) := by
  unfold LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
  simp_rw [AffineSoftmaxRestarts.restartPlan_eval]
  exact AffineSoftmaxRestarts.restartState_measurable _ _ hp
    (fun x seed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) + μ • (x - s.anchor))
    (AffineSoftmaxOracle.regularized_field_measurable s τ μ reply hm) _ _

omit [CompleteSpace E] in
lemma cachedProxPlan_param_measurable {Z : Type*} [MeasurableSpace Z]
    (s : Z → Snapshot ι E) (τ L G r : ℝ) (μ ε : Z → ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i))
    (hμ : Measurable μ) (hε : Measurable ε)
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (reply : ι × E → ℝ × E) (hr : Measurable reply)
    (seeds : Z → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed)
    (hs : ∀ j k, Measurable (fun z => seeds z j k)) :
    Measurable (fun z => OracleTemplate.ComponentEnvelope.Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
        (s z) τ L G r (μ z) (ε z) (project z) (seeds z))) := by
  have hS : Measurable (fun z => L + 2 * G ^ 2 / τ + μ z) := measurable_const.add hμ
  have hfield : Measurable (fun w : Z × (E × StepSeed) =>
      OracleTemplate.ComponentEnvelope.Program.eval reply
        (seededEstimatorPlan (s w.1) τ w.2.1 w.2.2) + μ w.1 • (w.2.1 - (s w.1).anchor)) := by
    have he := AffineSoftmaxMeasurability.seededEstimatorPlan_measurable
      (fun w : Z × (E × StepSeed) => s w.1) (fun w => w.2.1) τ
      (ha.comp measurable_fst) (fun i => (hv i).comp measurable_fst)
      (fun i => (hg i).comp measurable_fst) measurable_snd.fst
      (fun _ => reply) (fun i => hr.comp (measurable_const.prodMk measurable_snd.fst))
      (fun w => w.2.2) measurable_snd.snd
    exact he.add ((hμ.comp measurable_fst).smul
      (measurable_snd.fst.sub (ha.comp measurable_fst)))
  unfold LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
  simp_rw [AffineSoftmaxRestarts.restartPlan_eval]
  apply AffineSoftmaxRestarts.restartState_stopped_measurable
  · intro j
    exact AffineSoftmaxRestarts.restartScale_measurable _ _ _ _ hS measurable_const hμ measurable_const
  · intro j
    exact AffineSoftmaxRestarts.restartSteps_measurable _ _ _ _ hS measurable_const hμ measurable_const
  · exact hp
  · exact hfield
  · exact ha
  · exact hs
  · exact AffineSoftmaxRestarts.restartRounds_measurable _ _ measurable_const hε

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma cachedProxPlan_mem {C : Set E} (hC : Convex ℝ C)
    (s : Snapshot ι E) (τ L G r μ ε : ℝ) (project : E → E)
    (hp : ∀ x, project x ∈ C) (hs : s.anchor ∈ C)
    (reply : ι × E → ℝ × E) (seeds : LongTails.Algorithms.AffineSoftmaxProx.ProxSeed) :
    OracleTemplate.ComponentEnvelope.Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ ε project seeds) ∈ C := by
  unfold LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
  rw [AffineSoftmaxRestarts.restartPlan_eval]
  exact AffineSoftmaxRestarts.restartState_mem hC hp _ _ _ hs _ _

lemma levelPlan_distance_moments {C : Set E} (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : ι → E → ℝ) (s : Snapshot ι E) {L G r τ μ δ : ℝ}
    (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hτ : 0 < τ) (hμ : 0 < μ) (hδ : 0 < δ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r)
    (reply : ι × E → ℝ × E) (hm : Measurable reply)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x))
    {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) C u)
    (j : ℕ) :
    let out := fun seeds => OracleTemplate.ComponentEnvelope.Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ
        (OracleTemplate.SaddlePoint.project C) j seeds)
    Measurable out ∧ (∀ seeds, out seeds ∈ C) ∧
      Integrable out (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _) ∧
      Integrable (fun seeds => ‖out seeds - u‖ ^ 2)
        (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _) ∧
      (∫ seeds, ‖out seeds - u‖ ^ 2
        ∂(LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)) ≤ (2 * δ / μ) / 2 ^ j := by
  let out := fun seeds => OracleTemplate.ComponentEnvelope.Program.eval reply
    (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ
      (OracleTemplate.SaddlePoint.project C) j seeds)
  have hp : ∀ x, OracleTemplate.SaddlePoint.project C x ∈ C := fun x =>
    (OracleTemplate.SaddlePoint.project_spec ⟨u, hu⟩ hcompact hC x).1
  have hpc : Continuous (OracleTemplate.SaddlePoint.project C) :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨u, hu⟩ hcompact hC).continuous
  have hom : Measurable out := cachedProxPlan_measurable s τ L G r μ (δ / 2 ^ j) _ hpc reply hm
  have hmem (seeds) : out seeds ∈ C := cachedProxPlan_mem hC s τ L G r μ (δ / 2 ^ j) _ hp hz reply seeds
  have hoi : Integrable out (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _) := by
    obtain ⟨B, hB⟩ := hcompact.isBounded.exists_norm_le
    exact (integrable_const B).mono' hom.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun seeds => hB _ (hmem seeds)))
  have ho2 := ConstrainedStochasticAcceleration.integrable_compact_image
    LongTails.Algorithms.AffineSoftmaxProx.proxLaw hcompact (fun x => ‖x - u‖ ^ 2)
    ((continuous_id.sub continuous_const).norm.pow 2).continuousOn out hom hmem
  have hgap := cached_restart_accuracy hC hcompact f s hL hG hr hτ hμ
    (show 0 < δ / 2 ^ j by positivity) hcap hc hg hlip hbound hvalue hfield hz hradius reply hm hreply hu hmin
  have hgap' : (∫ seeds,
      regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor (out seeds) -
        regularized (fun z => smoothValue τ (fun i => f i z)) μ s.anchor u
      ∂(LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)) ≤ δ / 2 ^ j := hgap
  have hfg (x : E) (hx : x ∈ C) :
      HasGradientAt (fun z => smoothValue τ (fun i => f i z))
        (gradient (fun z => smoothValue τ (fun i => f i z)) x) x := by
    have hh := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
    rw [hh.gradient]
    exact hh
  have hd := expected_regularized_distance_le LongTails.Algorithms.AffineSoftmaxProx.proxLaw hcompact
    (smoothValue_convex f hτ hC hc hg hbound) hfg hμ s.anchor hu hmin out hom hmem hgap'
  refine ⟨hom, hmem, hoi, ho2, ?_⟩
  convert hd using 1
  ring

end LongTails.Proofs.AffineSoftmaxBallSolver
