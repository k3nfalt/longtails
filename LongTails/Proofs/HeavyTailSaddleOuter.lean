import LongTails.Setups.HeavyTailedNcsc
import LongTails.Proofs.HeavyTailSaddleEpoch
import LongTails.Proofs.HeavyTailSaddleRecovery
open scoped BigOperators RealInnerProductSpace
open OracleTemplate.PLMinimax LongTails.Setups.StochasticTwoSidedPL
open LongTails.Setups.WeaklyConvexHeavyTailed LongTails.Proofs.RecursiveEnvelopeGeometry
namespace LongTails.Proofs.HeavyTailSaddleOuter
lemma proximal_gap_descent {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ) (c x : E) (y : F)
    (hg : proxObj (maxValue f) L c x-dual f L c y ≤ ζ) :
    maxValue f x+L*‖x-c‖^2 ≤ maxValue f c+ζ := by
  have hm := weakProx_min H.hL
    (continuous_iff_continuousAt.mpr (fun z => (H.hgx z y).differentiableAt.continuousAt))
    (H.slice_weak y) c (Set.mem_univ c)
  change dual f L c y ≤ f c y+L*‖c-c‖^2 at hm
  simp only [sub_self,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,add_zero] at hm
  have hv := H.le_max_value c y
  dsimp only [proxObj] at hg
  linarith

lemma value_gap_from_quantifiers {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ Δ : ℝ}
    (H : Hyp f gx gy L μ) (x0 x : E)
    (hg : ∀ x y, ∃ y', f x0 y-f x y' ≤ Δ) :
    maxValue f x0-maxValue f x ≤ Δ := by
  obtain ⟨y,hy⟩ := H.attain x0
  obtain ⟨v,hv⟩ := hg x y
  rw [H.max_value_eq hy]
  linarith [H.le_max_value x v]

lemma movement_telescope (v d : ℕ → ℝ) {L ζ : ℝ} (T : ℕ)
    (hs : ∀ k, k < T → v (k+1)+L*d k ≤ v k+ζ) :
    v T+L*(∑ k ∈ Finset.range T,d k) ≤ v 0+T*ζ := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hi := ih (fun k hk => hs k (by omega))
    have ht := hs T (by omega)
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith
open LongTails.Algorithms.HeavyTailSaddleEstimator
lemma coarse_update_score {E F : Type} [NormedAddCommGroup E] (j : ℕ)
    (s : (E × (E × F)) × (E × (E × F))) (reply : E × F) :
    (j+1 : ℝ)*movementScore (coarseUpdate j s reply).2 ≤
      (j : ℝ)*movementScore s.2+movementScore (s.1.2.1,reply) := by
  by_cases hj : j=0
  · subst j
    simp [coarseUpdate]
  · by_cases hh : movementScore (s.1.2.1,reply) ≤ movementScore s.2
    · simp only [coarseUpdate, hj, false_or, hh, ↓reduceIte]
      have ht := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg j : (0:ℝ) ≤ j)
      nlinarith
    · simp only [coarseUpdate, hj, false_or, hh, ↓reduceIte]
      have ht := le_of_lt (lt_of_not_ge hh)
      nlinarith
lemma coarse_update_certificate {E F : Type} [NormedAddCommGroup E]
    (P : E × (E × F) → Prop) (j : ℕ)
    (s : (E × (E × F)) × (E × (E × F))) (reply : E × F)
    (hold : j ≠ 0 → P s.2) (hnew : P (s.1.2.1,reply)) :
    P (coarseUpdate j s reply).1 ∧ P (coarseUpdate j s reply).2 := by
  constructor
  · exact hnew
  · unfold coarseUpdate
    split_ifs with h
    · exact hnew
    · exact hold (fun hj => h (Or.inl hj))

open MeasureTheory
lemma movement_score_measurable {E F : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace F] : Measurable (movementScore (E:=E) (F:=F)) := by
  exact (measurable_snd.fst.sub measurable_fst).norm.pow_const 2
lemma coarse_update_measurable {E F : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace F] (j : ℕ) :
    Measurable (fun z : ((E × (E × F)) × (E × (E × F))) × (E × F) =>
      coarseUpdate j z.1 z.2) := by
  have hn : Measurable (fun z : ((E × (E × F)) × (E × (E × F))) × (E × F) =>
      (z.1.1.2.1,z.2)) := measurable_fst.fst.snd.fst.prodMk measurable_snd
  have ho : Measurable (fun z : ((E × (E × F)) × (E × (E × F))) × (E × F) =>
      z.1.2) := measurable_fst.snd
  have hs : MeasurableSet {z : ((E × (E × F)) × (E × (E × F))) × (E × F) |
      j=0 ∨ movementScore (z.1.1.2.1,z.2) ≤ movementScore z.1.2} :=
    by
      by_cases hj : j=0
      · simp only [hj,true_or,Set.ofPred_true]
        exact MeasurableSet.univ
      · simp only [hj,false_or]
        exact measurableSet_le (movement_score_measurable.comp hn) (movement_score_measurable.comp ho)
  exact hn.prodMk (hn.ite hs ho)

open LongTails.Proofs.HeavyTailSaddleRecovery
lemma proximal_value_residual {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ) (c x : E) (y : F)
    (hg : proxObj (maxValue f) L c x-dual f L c y ≤ ζ) :
    ‖gradient (maxValue f) x+(2*L) • (x-c)‖^2 ≤ 2*(4*L^2/μ+2*L)*ζ := by
  have hgrad : ∀ z, HasGradientAt (maxValue f) (gradient (maxValue f) z) z := by
    intro z
    obtain ⟨v,hv⟩ := H.attain z
    exact (H.value_hasGradient hv).gradient.symm ▸ H.value_hasGradient hv
  have hpg : ∀ z, HasGradientAt (proxObj (maxValue f) L c)
      (gradient (maxValue f) z+(2*L) • (z-c)) z := by
    intro z
    convert regularized_hasGradient hgrad (2*L) c z using 1
    ext v
    simp [regularized,proxObj]
  have hlip : ∀ u v, ‖(gradient (maxValue f) u+(2*L) • (u-c))-
      (gradient (maxValue f) v+(2*L) • (v-c))‖ ≤ (4*L^2/μ+2*L)*‖u-v‖ := by
    intro u v
    have he : (gradient (maxValue f) u+(2*L) • (u-c))-
        (gradient (maxValue f) v+(2*L) • (v-c)) =
        (gradient (maxValue f) u-gradient (maxValue f) v)+(2*L) • (u-v) := by module
    rw [he]
    have ht := norm_add_le (gradient (maxValue f) u-gradient (maxValue f) v) ((2*L) • (u-v))
    rw [norm_smul,Real.norm_of_nonneg (show 0 ≤ 2*L by linarith [H.hL])] at ht
    nlinarith [H.value_gradient_lipschitz u v]
  have hpos : 0 < 4*L^2/μ+2*L := by have := H.hL; have := H.hμ; positivity
  have hm : ∀ z, proxObj (maxValue f) L c (primal f L c) ≤ proxObj (maxValue f) L c z :=
    fun z => weakProx_min H.hL H.value_continuous H.value_weak c (Set.mem_univ z)
  have hr := OracleTemplate.ComponentEnvelope.smooth_gradient_gap hpos hpg hlip hm x
  have hd := H.dual_le_envelope c y
  change dual f L c y ≤ proxObj (maxValue f) L c (primal f L c) at hd
  exact hr.trans (mul_le_mul_of_nonneg_left (by linarith :
    proxObj (maxValue f) L c x-proxObj (maxValue f) L c (primal f L c) ≤ ζ) (by positivity))
lemma proximal_pair_distance {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ θ : ℝ}
    (H : Hyp f gx gy L μ) (c x u : E) (y v : F)
    (hx : proxObj (maxValue f) L c x-dual f L c y ≤ ζ)
    (hu : proxObj (maxValue f) L c u-dual f L c v ≤ θ) :
    L*‖u-x‖^2 ≤ 4*(ζ+θ) := by
  have hdx := H.dual_le_envelope c y
  have hdu := H.dual_le_envelope c v
  have hgx := weakProx_growth H.hL H.value_continuous H.value_weak c x
  have hgu := weakProx_growth H.hL H.value_continuous H.value_weak c u
  change dual f L c y ≤ proxObj (maxValue f) L c (primal f L c) at hdx
  change dual f L c v ≤ proxObj (maxValue f) L c (primal f L c) at hdu
  change proxObj (maxValue f) L c (primal f L c)+L/2*‖x-primal f L c‖^2 ≤ _ at hgx
  change proxObj (maxValue f) L c (primal f L c)+L/2*‖u-primal f L c‖^2 ≤ _ at hgu
  have hn := LongTails.Proofs.AuxiliaryInner.norm_add_sq_le (u-primal f L c) (primal f L c-x)
  rw [sub_add_sub_cancel,norm_sub_rev (primal f L c) x] at hn
  have ht := mul_le_mul_of_nonneg_left hn H.hL.le
  linarith

lemma coarse_fine_gradient_transfer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L ε : ℝ} (hL : 0 ≤ L) (he : 0 < ε) (g c x u : E)
    (hr : ‖g+(2*L) • (u-c)‖^2 ≤ ε^2/1024)
    (ha : (L*‖u-x‖)^2 ≤ ε^2/1024)
    (hb : (L*‖x-c‖)^2 ≤ ε^2/1024) : ‖g‖ ≤ ε := by
  have hr' : ‖g+(2*L) • (u-c)‖ ≤ ε/32 := by nlinarith [norm_nonneg (g+(2*L) • (u-c))]
  have ha' : L*‖u-x‖ ≤ ε/32 := by nlinarith [mul_nonneg hL (norm_nonneg (u-x))]
  have hb' : L*‖x-c‖ ≤ ε/32 := by nlinarith [mul_nonneg hL (norm_nonneg (x-c))]
  have hn := norm_sub_le (g+(2*L) • (u-c)) ((2*L) • (u-c))
  simp only [add_sub_cancel_right,norm_smul,Real.norm_of_nonneg (show 0 ≤ 2*L by positivity)] at hn
  have ht := norm_sub_le_norm_sub_add_norm_sub u x c
  have hm := mul_le_mul_of_nonneg_left ht hL
  linarith

noncomputable def coarseGood {E F : Type} [NormedAddCommGroup E]
    (value : E → ℝ) (gap : E × (E × F) → ℝ) (initial : E × F)
    (L Δ ζ : ℝ) (T j : ℕ) (s : (E × (E × F)) × (E × (E × F))) : Prop :=
  value s.1.2.1+L*j*movementScore s.2 ≤ value initial.1+j*ζ ∧
  (j=0 → s=((initial.1,initial),(initial.1,initial))) ∧
  (j≠0 → gap s.1 ≤ ζ ∧ gap s.2 ≤ ζ ∧ L*movementScore s.1 ≤ Δ+T*ζ)
lemma coarse_initial_good {E F : Type} [NormedAddCommGroup E]
    (value : E → ℝ) (gap : E × (E × F) → ℝ) (initial : E × F)
    (L Δ ζ : ℝ) (T : ℕ) :
    coarseGood value gap initial L Δ ζ T 0 ((initial.1,initial),(initial.1,initial)) := by
  simp [coarseGood]
lemma coarse_good_step {E F : Type} [NormedAddCommGroup E]
    (value : E → ℝ) (gap : E × (E × F) → ℝ) (initial : E × F)
    {L Δ ζ : ℝ} (hL : 0 ≤ L) (hζ : 0 ≤ ζ) {T j : ℕ} (hj : j < T)
    (s : (E × (E × F)) × (E × (E × F))) (reply : E × F)
    (hold : coarseGood value gap initial L Δ ζ T j s)
    (hgap : gap (s.1.2.1,reply) ≤ ζ)
    (hdesc : value reply.1+L*movementScore (s.1.2.1,reply) ≤ value s.1.2.1+ζ)
    (hglobal : value initial.1-value reply.1 ≤ Δ) :
    coarseGood value gap initial L Δ ζ T (j+1) (coarseUpdate j s reply) := by
  have hs := coarse_update_score j s reply
  have hl := mul_le_mul_of_nonneg_left hs hL
  have hn : 0 ≤ L*j*movementScore s.2 := by unfold movementScore; positivity
  have hv : value s.1.2.1 ≤ value initial.1+j*ζ := by linarith [hold.1]
  have ht : (j:ℝ)+1 ≤ T := by exact_mod_cast hj
  have htz := mul_le_mul_of_nonneg_right ht hζ
  have hm : L*movementScore (s.1.2.1,reply) ≤ Δ+T*ζ := by linarith
  have hc := coarse_update_certificate (fun r => gap r ≤ ζ) j s reply
    (fun h => (hold.2.2 h).2.1) hgap
  refine ⟨?_,?_,?_⟩
  · change value reply.1+L*(j+1:ℕ)*movementScore (coarseUpdate j s reply).2 ≤ _
    push_cast
    nlinarith [hold.1]
  · intro hz
    omega
  · intro _
    exact ⟨hc.1,hc.2,hm⟩
lemma coarse_selected_movement {E F : Type} [NormedAddCommGroup E]
    (value : E → ℝ) (gap : E × (E × F) → ℝ) (initial : E × F)
    {L Δ ζ : ℝ} {T : ℕ} (s : (E × (E × F)) × (E × (E × F)))
    (h : coarseGood value gap initial L Δ ζ T T s)
    (hg : value initial.1-value s.1.2.1 ≤ Δ) :
    L*T*movementScore s.2 ≤ Δ+T*ζ := by linarith [h.1]

open OracleTemplate LongTails.Algorithms.QueryLayers LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.StochasticEnvelopeExecution LongTails.Proofs.StochasticEnvelopeFreshness
open LongTails.Proofs.RecursiveEnvelopeExecution
lemma eval_coarse_plan {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E × F → Ω → E × F) (p σ L μ Δ G ζ δ : ℝ) (T : ℕ) (initial : E × F)
    (seeds : ℕ → CoarseProfile p σ L μ Δ G ζ T) (ξ : ℕ → Ω) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    let cost := fun j (_ : S) => recoveryCalls p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ
    let child := fun j (seed : S) (state : (E × (E × F)) × (E × (E × F))) =>
      recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (seed j) state.1.2.1 state.1.2
    evalAt (fun k x => g x (ξ k)) (coarsePlan p σ L μ Δ G ζ δ T seeds initial) 0 =
      (freshRun cost (fun j state (w : S × (ℕ → Ω)) =>
        coarseUpdate j state (evalAt (fun k x => g x (w.2 k)) (child j w.1 state) 0))
        T 0 ((initial.1,initial),(initial.1,initial)) (seeds,ξ)).2 := by
  intro S cost child
  have he := evalAt_substituted_statePlan cost child g (fun _ state => state) coarseUpdate
    seeds ξ T 0 0 ((initial.1,initial),(initial.1,initial))
  rw [cursorRun_freshRun] at he
  simp only [slotCalls,Nat.zero_add] at he
  calc
    _ = (evalAt (fun k x => g x (ξ k))
        (substitutePlan (fun j => cost j (seeds j)) (fun j => child j (seeds j))
          (statePlan (fun _ state => state) coarseUpdate T 0 ((initial.1,initial),(initial.1,initial))) 0) 0).2 :=
      evalAt_map (fun k x => g x (ξ k)) Prod.snd _ 0
    _ = _ := congrArg Prod.snd he

lemma coarse_good_measurable {E F : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F]
    {value : E → ℝ} {gap : E × (E × F) → ℝ} (hv : Measurable value) (hg : Measurable gap)
    (initial : E × F) (L Δ ζ : ℝ) (T j : ℕ) :
    MeasurableSet {s | coarseGood value gap initial L Δ ζ T j s} := by
  have he : MeasurableSet {s : (E × (E × F)) × (E × (E × F)) |
      value s.1.2.1+L*j*movementScore s.2 ≤ value initial.1+j*ζ} :=
    measurableSet_le ((hv.comp measurable_fst.snd.fst).add
      ((movement_score_measurable.comp measurable_snd).const_mul (L*j))) measurable_const
  have hc : MeasurableSet {s : (E × (E × F)) × (E × (E × F)) |
      gap s.1 ≤ ζ ∧ gap s.2 ≤ ζ ∧ L*movementScore s.1 ≤ Δ+T*ζ} :=
    (measurableSet_le (hg.comp measurable_fst) measurable_const).inter
      ((measurableSet_le (hg.comp measurable_snd) measurable_const).inter
        (measurableSet_le ((movement_score_measurable.comp measurable_fst).const_mul L) measurable_const))
  by_cases hj : j=0
  · convert he.inter (measurableSet_eq_fun measurable_id
      (show Measurable (fun _ : (E × (E × F)) × (E × (E × F)) => ((initial.1,initial),(initial.1,initial))) from measurable_const)) using 1
    ext s
    simp [coarseGood,hj]
    intro hs
    subst s
    exact le_rfl
  · convert he.inter hc using 1
    ext s
    simp [coarseGood,hj]

open LongTails.Proofs.HeavyTailSaddleEpoch
lemma coarse_stage_parameter_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ Δ G ζ δ : ℝ) (T j : ℕ) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    Measurable (fun w : ((E × (E × F)) × (E × (E × F))) × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k))
        (recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (w.2.1 j)
          w.1.1.2.1 w.1.1.2) 0) := by
  intro S
  exact (recovery_plan_parameter_measurable hg p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ).comp
    (show Measurable (fun w : ((E × (E × F)) × (E × (E × F))) × (S × (ℕ → Ω)) =>
      ((w.1.1.2.1,w.1.1.2),(w.2.1 j,w.2.2))) by fun_prop)
lemma coarse_plan_law {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ Δ G ζ δ : ℝ) (T : ℕ) (initial : E × F) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    let Q := (coarseProfileLaw p σ L μ Δ G ζ T : Measure S)
    let child := fun j (seed : S) (state : (E × (E × F)) × (E × (E × F))) =>
      recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (seed j) state.1.2.1 state.1.2
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
        (coarsePlan p σ L μ Δ G ζ δ T w.1 initial) 0)
      (fun samples => (idealRun
        (fun j (state : (E × (E × F)) × (E × (E × F))) (w : S × (ℕ → Ω)) =>
          coarseUpdate j state (evalAt (fun k x => g x (w.2 k)) (child j w.1 state) 0))
        T 0 ((initial.1,initial),(initial.1,initial)) samples).2)
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      (Measure.infinitePi fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)) := by
  intro S Q child
  have hs (j : ℕ) : Measurable (fun w : ((E × (E × F)) × (E × (E × F))) × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k)) (child j w.2.1 w.1) 0) :=
    coarse_stage_parameter_measurable hg p σ L μ Δ G ζ δ T j
  have hh := substituted_statePlan_identDistrib Q pnoise
    (fun j (_ : S) => recoveryCalls p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ)
    (fun _ => measurable_const) child g (fun _ state => state) coarseUpdate
    hs (fun _ => measurable_id) coarse_update_measurable T ((initial.1,initial),(initial.1,initial))
  have hp := hh.comp measurable_snd
  convert hp using 1
  · funext w
    exact evalAt_map (fun k x => g x (w.2 k)) Prod.snd _ 0
  · rfl

open LongTails.Proofs.HeavyTailSaddleEpoch
lemma coarse_initialization {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ Δ G ζ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (initial : E × F) (hgap : ∀ x y, ∃ y', f initial.1 y-f x y' ≤ Δ)
    (hG : ‖gy initial.1 initial.2‖ ≤ G) (hΔ : 0 ≤ Δ) (hζ : 0 ≤ ζ)
    (T j : ℕ) (s : (E × (E × F)) × (E × (E × F)))
    (hs : coarseGood (maxValue f)
      (fun r => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2)
      initial L Δ ζ T j s) :
    ∃ v, gy (innerPrimal f L s.1.2.1 v) v = 0 ∧
      μ*‖s.1.2.1-innerPrimal f L s.1.2.1 v‖^2 ≤ coarseInitialBound L μ Δ G ζ T j ∧
      -dual f L s.1.2.1 s.1.2.2-(-dual f L s.1.2.1 v)+μ/2*‖s.1.2.2-v‖^2 ≤
        coarseInitialBound L μ Δ G ζ T j := by
  by_cases hj : j=0
  · have he := hs.2.1 hj
    subst s
    simpa [coarseInitialBound,hj] using proximal_initial_energy H hsc initial.1 initial.2 hgap hG
  · obtain ⟨v,hv,hr,hd⟩ := proximal_warm_energy H hsc s.1.1 s.1.2.1 s.1.2.1 s.1.2.2 (hs.2.2 hj).1
    have hk : 1 ≤ L/μ := (le_div_iff₀ H.hμ).mpr (by simpa using H.hμL)
    have hm : L*‖s.1.1-s.1.2.1‖^2 ≤ Δ+T*ζ := by
      rw [norm_sub_rev]
      exact (hs.2.2 hj).2.2
    have hb := warm_public_envelope hk hζ hΔ T hm
    refine ⟨v,hv,?_,?_⟩
    · simpa [coarseInitialBound,hj] using hr.trans hb
    · simpa [coarseInitialBound,hj] using hd.trans hb

lemma coarse_profile_coordinate_law (p σ L μ Δ G ζ : ℝ) (T j : ℕ) :
    MeasurePreserving (fun s : CoarseProfile p σ L μ Δ G ζ T => s j)
      (coarseProfileLaw p σ L μ Δ G ζ T : Measure _)
      (Measure.infinitePi fun _ : ℕ =>
        (recoveryProfileLaw p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) : Measure _)) := by
  exact ⟨measurable_pi_apply j,Measure.infinitePi_map_eval _ j⟩
lemma coarse_stage_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {Δ G ζ δ : ℝ} (hΔ : 0 ≤ Δ) (hζ : 0 < ζ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (initial : E × F) (hgap : ∀ x y, ∃ y', f initial.1 y-f x y' ≤ Δ)
    (hG : ‖gy initial.1 initial.2‖ ≤ G) {T j : ℕ} (hj : j < T)
    (state : (E × (E × F)) × (E × (E × F)))
    (hs : coarseGood (maxValue f)
      (fun r => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2)
      initial L Δ ζ T j state) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    let Q := (coarseProfileLaw p σ L μ Δ G ζ T : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : S × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
      (recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (w.1 j) state.1.2.1 state.1.2) 0
    P {w | ¬coarseGood (maxValue f)
      (fun r => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2)
      initial L Δ ζ T (j+1) (coarseUpdate j state (output w))} ≤ ENNReal.ofReal δ := by
  intro S Q P output
  obtain ⟨u,hu,hr,hd⟩ := coarse_initialization H hsc initial hgap hG hΔ hζ.le T j state hs
  let B := coarseInitialBound L μ Δ G ζ T j
  let S0 := RecoveryProfile p σ L μ ζ B
  let output0 := fun w : (ℕ → S0) × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
    (recoveryPlan p σ L μ ζ B δ w.1 state.1.2.1 state.1.2) 0
  have hphys := recovery_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
    hζ hδ hδ1 state.1.2.1 B state.1.2 u hu hr hd
  have hm : Measurable output0 :=
    (recovery_plan_parameter_measurable (g := fun z ω => (ox z ω,oy z ω)) (hox.prodMk hoy) p σ L μ ζ B δ).comp
      (show Measurable (fun w : (ℕ → S0) × (ℕ → Ω) => ((state.1.2.1,state.1.2),w)) by fun_prop)
  have hval : Measurable (maxValue f) := H.value_continuous.measurable
  have hdual : Measurable (dual f L state.1.2.1) :=
    (continuous_iff_continuousAt.mpr (fun v => (H.dual_hasGradient state.1.2.1 v).differentiableAt.continuousAt)).measurable
  let bad := {w : (ℕ → S0) × (ℕ → Ω) |
    ζ < proxObj (maxValue f) L state.1.2.1 (output0 w).1-dual f L state.1.2.1 (output0 w).2}
  have hb : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    unfold proxObj
    fun_prop
  have hmap := (coarse_profile_coordinate_law p σ L μ Δ G ζ T j).prod
    (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => Pnoise))
  have hmeasure := (hmap.measure_preimage hb.nullMeasurableSet).trans_le hphys
  refine (measure_mono ?_).trans hmeasure
  intro w hfail
  by_contra hn
  have hg : proxObj (maxValue f) L state.1.2.1 (output w).1-dual f L state.1.2.1 (output w).2 ≤ ζ :=
    le_of_not_gt hn
  exact hfail (coarse_good_step (maxValue f)
    (fun r => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2) initial H.hL.le hζ.le hj
    state (output w) hs hg (proximal_gap_descent H _ _ _ hg)
    (value_gap_from_quantifiers H initial.1 (output w).1 hgap))

lemma executed_coarse_probability {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (pnoise : Measure Ω) [IsProbabilityMeasure pnoise]
    {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ Δ G ζ δ : ℝ) (T : ℕ) (hT : 0 < T) (initial : E × F)
    (good : ℕ → Set ((E × (E × F)) × (E × (E × F))))
    (hgood : ∀ j, MeasurableSet (good j))
    (hinit : ((initial.1,initial),(initial.1,initial)) ∈ good 0)
    (bad : Set (E × (E × F))) (hbad : MeasurableSet bad)
    (hterminal : ∀ state, state ∈ good T → state.2 ∉ bad)
    {η : ℝ} (hη : 0 ≤ η) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    let Q := (coarseProfileLaw p σ L μ Δ G ζ T : Measure S)
    let P := Q.prod (Measure.infinitePi fun _ : ℕ => pnoise)
    let step := fun j (state : (E × (E × F)) × (E × (E × F))) (w : S × (ℕ → Ω)) =>
      coarseUpdate j state (evalAt (fun k x => g x (w.2 k))
        (recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (w.1 j) state.1.2.1 state.1.2) 0)
    (∀ j, j < T → ∀ state, state ∈ good j →
      P {w | step j state w ∉ good (j+1)} ≤ ENNReal.ofReal η) →
    ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => pnoise))
      {w | evalAt (fun k x => g x (w.2 k)) (coarsePlan p σ L μ Δ G ζ δ T w.1 initial) 0 ∈ bad}
      ≤ ENNReal.ofReal (T*η) := by
  intro S Q P step hprob
  let good' := fun j => if j ≤ T then good j else Set.univ
  have hgood' (j : ℕ) : MeasurableSet (good' j) := by
    dsimp [good']
    split_ifs
    · exact hgood j
    · exact MeasurableSet.univ
  have ht (j : ℕ) : Measurable (Function.uncurry (step j)) :=
    (coarse_update_measurable j).comp (measurable_fst.prodMk
      (coarse_stage_parameter_measurable hg p σ L μ Δ G ζ δ T j))
  have hp' (j : ℕ) (state) (hs : state ∈ good' j) :
      P.real {w | step j state w ∉ good' (j+1) ∨ step j state w ∉ (Set.univ : Set _)} ≤ η := by
    by_cases hj : j < T
    · have hh := hprob j hj state (by simpa [good',Nat.le_of_lt hj] using hs)
      have hr := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hη)
      simpa [good',show j+1 ≤ T by omega,Measure.real] using hr
    · have hn : ¬j+1 ≤ T := by omega
      simpa [good',hn] using hη
  have hh := inhomogeneous_terminal_certificate P step ht good' (fun _ => Set.univ) hgood'
    (fun _ => MeasurableSet.univ) hη hp' T hT ((initial.1,initial),(initial.1,initial))
    (by simpa [good'] using hinit)
  have hd := coarse_plan_law pnoise hg p σ L μ Δ G ζ δ T initial
  refine (hd.measure_mem_eq hbad).trans_le ((measure_mono ?_).trans hh)
  intro samples hs
  left
  intro hgoodT
  have hhT : idealRun step T 0 ((initial.1,initial),(initial.1,initial)) samples ∈ good T := by
    simpa [good'] using hgoodT
  exact hterminal _ hhT hs

lemma proximal_joint_gap_measurable {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ) :
    Measurable (fun r : E × (E × F) => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2) := by
  have hv := H.value_continuous.measurable
  have hd : Measurable (fun r : E × (E × F) => -dual f L r.1 r.2.2) := by
    have hh := (proximal_regularized_value_measurable H 0).comp
      (show Measurable (fun r : E × (E × F) => ((r.1,(0:F)),r.2.2)) by fun_prop)
    simpa only [Function.comp_def,zero_div,zero_mul,inner_zero_left,add_zero,sub_zero] using hh
  change Measurable (fun r : E × (E × F) => maxValue f r.2.1+L*‖r.2.1-r.1‖^2-dual f L r.1 r.2.2)
  convert ((hv.comp measurable_snd.fst).add
      (((measurable_snd.fst.sub measurable_fst).norm.pow_const 2).const_mul L)).add hd using 1
  funext r
  exact sub_eq_add_neg _ _

lemma coarse_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {Δ G ζ δ : ℝ} (hΔ : 0 ≤ Δ) (hζ : 0 < ζ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (initial : E × F) (hgap : ∀ x y, ∃ y', f initial.1 y-f x y' ≤ Δ)
    (hG : ‖gy initial.1 initial.2‖ ≤ G) (T : ℕ) (hT : 0 < T)
 :
    let S := CoarseProfile p σ L μ Δ G ζ T
    let Q := (coarseProfileLaw p σ L μ Δ G ζ T : Measure S)
    let P := (Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k)))
      (coarsePlan p σ L μ Δ G ζ δ T w.1 initial) 0
    P {w | ζ < proxObj (maxValue f) L (output w).1 (output w).2.1-dual f L (output w).1 (output w).2.2 ∨
      Δ+T*ζ < L*T*movementScore (output w)} ≤ ENNReal.ofReal (T*δ) := by
  intro S Q P output
  let gap := fun r : E × (E × F) => proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2
  let good := fun j => {s | coarseGood (maxValue f) gap initial L Δ ζ T j s}
  let bad := {r : E × (E × F) | ζ < gap r ∨ Δ+T*ζ < L*T*movementScore r}
  have hgapm : Measurable gap := proximal_joint_gap_measurable H
  have hgood (j : ℕ) : MeasurableSet (good j) :=
    coarse_good_measurable H.value_continuous.measurable hgapm initial L Δ ζ T j
  have hbad : MeasurableSet bad :=
    (measurableSet_lt measurable_const hgapm).union
      (measurableSet_lt measurable_const (movement_score_measurable.const_mul (L*T)))
  have hterminal (s) (hs : s ∈ good T) : s.2 ∉ bad := by
    have hc := (hs.2.2 (Nat.ne_of_gt hT)).2.1
    have hm := coarse_selected_movement (maxValue f) gap initial s hs
      (value_gap_from_quantifiers H initial.1 s.1.2.1 hgap)
    exact not_or.mpr ⟨not_lt_of_ge hc,not_lt_of_ge hm⟩
  apply executed_coarse_probability Pnoise (g := fun z ω => (ox z ω,oy z ω)) (hox.prodMk hoy)
    p σ L μ Δ G ζ δ T hT initial good hgood
    (coarse_initial_good (maxValue f) gap initial L Δ ζ T) bad hbad hterminal hδ.le
  intro j hj state hs
  exact coarse_stage_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
    hΔ hζ hδ hδ1 initial hgap hG hj state hs

lemma independent_seed_append_failure {S V Ω U : Type*} [MeasurableSpace S] [MeasurableSpace V]
    [MeasurableSpace Ω] [MeasurableSpace U]
    (Q : Measure S) [IsProbabilityMeasure Q] (R : Measure V) [IsProbabilityMeasure R]
    (p : Measure Ω) [IsProbabilityMeasure p] {length : S → ℕ} (hl : Measurable length)
    (X : S × (ℕ → Ω) → U) (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ j, j < length s → ξ j=ζ j) → X (s,ξ)=X (s,ζ))
    {bad : Set (U × (V × (ℕ → Ω)))} (hbad : MeasurableSet bad)
    {B : Set U} (hB : MeasurableSet B) {α β : ENNReal}
    (hrough : (Q.prod (Measure.infinitePi fun _ : ℕ => p)) {w | X w ∈ B} ≤ α)
    (hcond : ∀ u, u ∉ B → (R.prod (Measure.infinitePi fun _ : ℕ => p)) {w | (u,w) ∈ bad} ≤ β) :
    ((Q.prod R).prod (Measure.infinitePi fun _ : ℕ => p))
      {w | (X (w.1.1,w.2),(w.1.2,fun j => w.2 (length w.1.1+j))) ∈ bad} ≤ α+β := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let M := (Q.prod P).map (fun w => (w.1,X w))
  have hm : Measurable (fun w : S × (ℕ → Ω) => (w.1,X w)) := measurable_fst.prodMk hX
  have : IsProbabilityMeasure M := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hbad' : MeasurableSet {w : (S × U) × (V × (ℕ → Ω)) | (w.1.2,w.2) ∈ bad} :=
    hbad.preimage (measurable_fst.snd.prodMk measurable_snd)
  have hB' : MeasurableSet {w : S × U | w.2 ∈ B} := hB.preimage measurable_snd
  have hr : M {w : S × U | w.2 ∈ B} ≤ α := by
    rw [Measure.map_apply hm hB']
    exact hrough
  have hb := product_failure_probability M (R.prod P) hbad' hB' hr (fun w hw => hcond w.2 hw)
  have hp := (measurePreserving_prodAssoc M R P).comp
    ((swap_middle_preserving M P R).comp
      (((seed_prefix_tail_preserving p Q hl X hX hdep).prod (MeasurePreserving.id R)).comp
        (swap_middle_preserving Q R P)))
  exact (hp.measure_preimage hbad'.nullMeasurableSet).trans_le hb

lemma coarse_plan_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ Δ G ζ δ : ℝ) (T : ℕ) (initial : E × F) :
    let S := CoarseProfile p σ L μ Δ G ζ T
    Measurable (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun k x => g x (w.2 k))
      (coarsePlan p σ L μ Δ G ζ δ T w.1 initial) 0) := by
  intro S
  let cost := fun j (_ : S) => recoveryCalls p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ
  let step := fun j (state : (E × (E × F)) × (E × (E × F))) (w : S × (ℕ → Ω)) =>
    coarseUpdate j state (evalAt (fun k x => g x (w.2 k))
      (recoveryPlan p σ L μ ζ (coarseInitialBound L μ Δ G ζ T j) δ (w.1 j) state.1.2.1 state.1.2) 0)
  have ht (j : ℕ) : Measurable (Function.uncurry (step j)) :=
    (coarse_update_measurable j).comp (measurable_fst.prodMk
      (coarse_stage_parameter_measurable hg p σ L μ Δ G ζ δ T j))
  have hh := freshRun_measurable (cost:=cost) (fun _ => measurable_const) ht T 0
  have hm := (hh.comp (show Measurable (fun w : (ℕ → S) × (ℕ → Ω) =>
      (((initial.1,initial),(initial.1,initial)),w)) by fun_prop)).snd
  convert hm using 1
  funext w
  exact eval_coarse_plan g p σ L μ Δ G ζ δ T initial w.1 w.2

lemma outer_steps_positive (L Δ ε : ℝ) : 0 < outerSteps L Δ ε := by
  unfold outerSteps
  omega
lemma outer_steps_gap {L Δ ε : ℝ} (he : 0 < ε) :
    4096*L*Δ ≤ (outerSteps L Δ ε : ℝ)*ε^2 := by
  have hh := Nat.le_ceil (4096*L*Δ/ε^2)
  have ht : (⌈4096*L*Δ/ε^2⌉₊ : ℝ) ≤ outerSteps L Δ ε := by
    unfold outerSteps
    push_cast
    linarith
  exact (div_le_iff₀ (sq_pos_of_pos he)).mp (hh.trans ht)
lemma outer_accuracy_tuning {L μ ε : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) (he : 0 < ε) :
    0 < fineAccuracy L μ ε ∧ fineAccuracy L μ ε ≤ coarseAccuracy L ε ∧
    2*(4*L^2/μ+2*L)*fineAccuracy L μ ε ≤ ε^2/1024 ∧
    4*L*(coarseAccuracy L ε+fineAccuracy L μ ε) ≤ ε^2/1024 := by
  have hL : 0 < L := hm.trans_le hmL
  have he2 := sq_pos_of_pos he
  have hc : L*coarseAccuracy L ε=ε^2/1048576 := by
    unfold coarseAccuracy
    field_simp
  have hf : L^2*fineAccuracy L μ ε=μ*ε^2/1048576 := by
    unfold fineAccuracy
    field_simp
  have hpos : 0 < fineAccuracy L μ ε := by unfold fineAccuracy; positivity
  have hle : fineAccuracy L μ ε ≤ coarseAccuracy L ε := by
    have hh := mul_le_mul_of_nonneg_right hmL he2.le
    have ht : L^2*fineAccuracy L μ ε ≤ L^2*coarseAccuracy L ε := by nlinarith
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp ht
  refine ⟨hpos,hle,?_,?_⟩
  · have hmul : μ*(2*(4*L^2/μ+2*L)*fineAccuracy L μ ε) =
        8*(L^2*fineAccuracy L μ ε)+4*μ*(L*fineAccuracy L μ ε) := by field_simp; ring
    have hh := mul_le_mul_of_nonneg_left hle hL.le
    have hu := mul_le_mul_of_nonneg_left hh hm.le
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hle hL.le
    nlinarith
lemma outer_movement_tuning {L Δ ε d : ℝ} (hL : 0 < L) (he : 0 < ε)
    (hmove : L*(outerSteps L Δ ε)*d^2 ≤ Δ+(outerSteps L Δ ε)*coarseAccuracy L ε) :
    (L*d)^2 ≤ ε^2/1024 := by
  have hT : (0:ℝ) < outerSteps L Δ ε := by exact_mod_cast outer_steps_positive L Δ ε
  have hc : L*coarseAccuracy L ε=ε^2/1048576 := by unfold coarseAccuracy; field_simp
  have hh := outer_steps_gap (L:=L) (Δ:=Δ) he
  have hm := mul_le_mul_of_nonneg_left hmove hL.le
  have ht := mul_nonneg hT.le (sq_nonneg ε)
  nlinarith

lemma coarse_fine_accuracy {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ Δ ε : ℝ}
    (H : Hyp f gx gy L μ) (he : 0 < ε) (selected : E × (E × F)) (out : E × F)
    (hcoarse : proxObj (maxValue f) L selected.1 selected.2.1-dual f L selected.1 selected.2.2 ≤ coarseAccuracy L ε)
    (hmove : L*(outerSteps L Δ ε)*movementScore selected ≤ Δ+(outerSteps L Δ ε)*coarseAccuracy L ε)
    (hfine : proxObj (maxValue f) L selected.1 out.1-dual f L selected.1 out.2 ≤ fineAccuracy L μ ε) :
    ‖gradient (maxValue f) out.1‖ ≤ ε := by
  have ht := outer_accuracy_tuning H.hμ H.hμL he
  have hr := (proximal_value_residual H selected.1 out.1 out.2 hfine).trans ht.2.2.1
  have hd := proximal_pair_distance H selected.1 selected.2.1 out.1 selected.2.2 out.2 hcoarse hfine
  have hm := mul_le_mul_of_nonneg_left hd H.hL.le
  have ha : (L*‖out.1-selected.2.1‖)^2 ≤ ε^2/1024 := by nlinarith [ht.2.2.2]
  have hb := outer_movement_tuning H.hL he hmove
  exact coarse_fine_gradient_transfer H.hL.le he (gradient (maxValue f) out.1)
    selected.1 selected.2.1 out.1 hr ha hb

lemma eval_saddle_plan {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E × F → Ω → E × F) (p σ L μ Δ G ε δ : ℝ) (initial : E × F)
    (seed : SaddleSeed p σ L μ Δ G ε) (ξ : ℕ → Ω) :
    let C := coarseCalls p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ) (outerSteps L Δ ε)
    let selected := evalAt (fun k x => g x (ξ k))
      (coarsePlan p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ)
        (outerSteps L Δ ε) seed.1 initial) 0
    evalAt (fun k x => g x (ξ k)) (saddlePlan p σ L μ Δ G ε δ seed initial) 0 =
      (evalAt (fun k x => g x (ξ (C+k)))
        (recoveryPlan p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε)
          (outerConfidence L Δ ε δ) seed.2 selected.1 selected.2) 0).1 := by
  intro C selected
  unfold saddlePlan saddleCalls
  rw [evalAt_bind,evalAt_map,Nat.zero_add]
  simpa only [Nat.add_zero] using congrArg Prod.fst
    (evalAt_shift (fun k x => g x (ξ k))
      (recoveryPlan p σ L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε)
        (outerConfidence L Δ ε δ) seed.2 selected.1 selected.2) C 0).symm
lemma saddle_plan_measurable {E F Ω : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {g : E × F → Ω → E × F} (hg : Measurable (Function.uncurry g))
    (p σ L μ Δ G ε δ : ℝ) (initial : E × F) :
    Measurable (fun w : (SaddleSeed p σ L μ Δ G ε) × (ℕ → Ω) =>
      evalAt (fun k x => g x (w.2 k)) (saddlePlan p σ L μ Δ G ε δ w.1 initial) 0) := by
  let C := coarseCalls p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ) (outerSteps L Δ ε)
  let selected := fun w : (SaddleSeed p σ L μ Δ G ε) × (ℕ → Ω) =>
    evalAt (fun k x => g x (w.2 k))
      (coarsePlan p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ)
        (outerSteps L Δ ε) w.1.1 initial) 0
  have hs : Measurable selected :=
    (coarse_plan_measurable hg p σ L μ Δ G (coarseAccuracy L ε) (outerConfidence L Δ ε δ)
      (outerSteps L Δ ε) initial).comp (measurable_fst.fst.prodMk measurable_snd)
  have ht : Measurable (fun w : (SaddleSeed p σ L μ Δ G ε) × (ℕ → Ω) =>
      (selected w,(w.1.2,fun k => w.2 (C+k)))) := hs.prodMk (measurable_fst.snd.prodMk (by fun_prop))
  have hh := ((recovery_plan_parameter_measurable hg p σ L μ (fineAccuracy L μ ε)
    (fineInitialBound L μ ε) (outerConfidence L Δ ε δ)).comp ht).fst
  convert hh using 1
  funext w
  exact eval_saddle_plan g p σ L μ Δ G ε δ initial w.1 w.2

lemma saddle_success_probability {E F Ω : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (Pnoise : Measure Ω) [IsProbabilityMeasure Pnoise]
    (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) Pnoise) (hyi : ∀ z, Integrable (oy z) Pnoise)
    (hxm : ∀ z, ∫ ω, ox z ω ∂Pnoise = gx z.1 z.2)
    (hym : ∀ z, ∫ ω, oy z ω ∂Pnoise = gy z.1 z.2)
    {p σ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p) Pnoise)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z.1 z.2‖^2+‖oy z ω-gy z.1 z.2‖^2))^p ∂Pnoise) ≤ σ^p)
    {Δ G ε δ : ℝ} (hΔ : 0 ≤ Δ) (he : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (initial : E × F) (hgap : ∀ x y, ∃ y', f initial.1 y-f x y' ≤ Δ)
    (hG : ‖gy initial.1 initial.2‖ ≤ G) :
    let P := (saddleSeedLaw p σ L μ Δ G ε : Measure _).prod (Measure.infinitePi fun _ : ℕ => Pnoise)
    let output := fun w : (SaddleSeed p σ L μ Δ G ε) × (ℕ → Ω) =>
      evalAt (fun k z => (ox z (w.2 k),oy z (w.2 k))) (saddlePlan p σ L μ Δ G ε δ w.1 initial) 0
    P {w | ε < ‖gradient (maxValue f) (output w)‖} ≤ ENNReal.ofReal δ := by
  intro P output
  let T := outerSteps L Δ ε
  let ζ := coarseAccuracy L ε
  let θ := fineAccuracy L μ ε
  let d := outerConfidence L Δ ε δ
  let S := ℕ → CoarseProfile p σ L μ Δ G ζ T
  let V := ℕ → RecoveryProfile p σ L μ θ (fineInitialBound L μ ε)
  let Q := Measure.infinitePi fun _ : ℕ => (coarseProfileLaw p σ L μ Δ G ζ T : Measure (CoarseProfile p σ L μ Δ G ζ T))
  let R := Measure.infinitePi fun _ : ℕ => (recoveryProfileLaw p σ L μ θ (fineInitialBound L μ ε) : Measure (RecoveryProfile p σ L μ θ (fineInitialBound L μ ε)))
  let C := coarseCalls p σ L μ Δ G ζ d T
  let g := fun z ω => (ox z ω,oy z ω)
  have hg : Measurable (Function.uncurry g) := hox.prodMk hoy
  let X := fun w : S × (ℕ → Ω) => evalAt (fun k z => g z (w.2 k)) (coarsePlan p σ L μ Δ G ζ d T w.1 initial) 0
  let Y := fun w : (E × (E × F)) × (V × (ℕ → Ω)) => evalAt (fun k z => g z (w.2.2 k))
    (recoveryPlan p σ L μ θ (fineInitialBound L μ ε) d w.2.1 w.1.1 w.1.2) 0
  have hX : Measurable X := coarse_plan_measurable hg p σ L μ Δ G ζ d T initial
  have hY : Measurable Y := recovery_plan_parameter_measurable hg p σ L μ θ (fineInitialBound L μ ε) d
  have hgval : Measurable (gradient (maxValue f)) := by
    have hh : LipschitzWith (Real.toNNReal (4*L^2/μ)) (gradient (maxValue f)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.coe_toNNReal _ (by have := H.hμ; positivity),dist_eq_norm,dist_eq_norm]
      exact H.value_gradient_lipschitz x y
    exact hh.continuous.measurable
  let B := {r : E × (E × F) | ζ < proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2 ∨
    Δ+T*ζ < L*T*movementScore r}
  let bad := {w : (E × (E × F)) × (V × (ℕ → Ω)) | ε < ‖gradient (maxValue f) (Y w).1‖}
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_const (proximal_joint_gap_measurable H)).union
      (measurableSet_lt measurable_const (movement_score_measurable.const_mul (L*T)))
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const ((hgval.comp hY.fst).norm)
  have ht := outer_accuracy_tuning H.hμ H.hμL he
  have hθ : 0 < θ := ht.1
  have hζ : 0 < ζ := lt_of_lt_of_le ht.1 ht.2.1
  have hd : 0 < d := by dsimp [d,outerConfidence]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d,outerConfidence]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<outerSteps L Δ ε+2)).mpr
    nlinarith [show (0:ℝ) ≤ outerSteps L Δ ε from Nat.cast_nonneg _]
  have hrough : (Q.prod (Measure.infinitePi fun _ : ℕ => Pnoise)) {w | X w ∈ B} ≤ ENNReal.ofReal (T*d) :=
    coarse_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
      hΔ hζ hd hd1 initial hgap hG T (outer_steps_positive L Δ ε)
  have hcond (r : E × (E × F)) (hr : r ∉ B) :
      (R.prod (Measure.infinitePi fun _ : ℕ => Pnoise)) {w | (r,w) ∈ bad} ≤ ENNReal.ofReal d := by
    have hc : proxObj (maxValue f) L r.1 r.2.1-dual f L r.1 r.2.2 ≤ ζ :=
      le_of_not_gt (fun h => hr (Or.inl h))
    have hm : L*T*movementScore r ≤ Δ+T*ζ := le_of_not_gt (fun h => hr (Or.inr h))
    obtain ⟨u,hu,href,hstart⟩ := proximal_fine_initial_energy H hsc hζ.le r.1 r.2.1 r.2.2 hc
    have hf := recovery_success_probability H hsc Pnoise ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
      hθ hd hd1 r.1 (fineInitialBound L μ ε) r.2 u hu href hstart
    refine (measure_mono ?_).trans hf
    intro w hw
    by_contra hn
    have hj : proxObj (maxValue f) L r.1 (Y (r,w)).1-dual f L r.1 (Y (r,w)).2 ≤ θ := le_of_not_gt hn
    exact (not_lt_of_ge (coarse_fine_accuracy H he r (Y (r,w)) hc hm hj)) hw
  have hdep : ∀ s ξ ν, (∀ j, j < C → ξ j=ν j) → X (s,ξ)=X (s,ν) := by
    intro s ξ ν h
    apply StochasticEnvelopeExecution.evalAt_prefix_congr _ _ _ 0
    intro j hj z
    simp only [Nat.zero_add,h j hj]
  have hb := independent_seed_append_failure Q R Pnoise (length:=fun _ => C) measurable_const X hX hdep
    hbad hB hrough hcond
  have hc : (T:ℝ)*d+d ≤ δ := by
    calc
      (T:ℝ)*d+d = (T+1)*d := by ring
      _ ≤ δ := by
        dsimp [d,outerConfidence,T]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0:ℝ)<outerSteps L Δ ε+2)).mpr
        nlinarith
  have hb' := hb.trans ((ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg T) hd.le) hd.le).symm.le.trans
    (ENNReal.ofReal_le_ofReal hc))
  convert hb' using 1
  congr 1
  ext w
  change (ε < ‖gradient (maxValue f) (output w)‖) ↔ (ε < ‖gradient (maxValue f) (Y (X (w.1.1,w.2),(w.1.2,fun j => w.2 (C+j)))).1‖)
  rw [show output w=(Y (X (w.1.1,w.2),(w.1.2,fun j => w.2 (C+j)))).1 from
    eval_saddle_plan g p σ L μ Δ G ε δ initial w.1 w.2]

lemma execute_saddle {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E × F → Ω → E × F)
    (p σ L μ Δ G ε δ : ℝ) (initial : E × F) (seed : SaddleSeed p σ L μ Δ G ε) (ξ : ℕ → Ω)
    {K : ℕ} (hK : saddleCalls p σ L μ Δ G ε δ ≤ K) :
    execute { Seed := fun _ => Ω,law := P,answer := fun _ (_,z) ω => g z ω }
      (saddleAlgorithm p σ L μ Δ G ε δ initial) (fun _ => K) seed ξ =
      evalAt (fun k z => g z (ξ k)) (saddlePlan p σ L μ Δ G ε δ seed initial) 0 := by
  let O : Oracle (E × F) (E × F) :=
    { Seed := fun _ => Ω,law := P,answer := fun _ (_,z) ω => g z ω }
  let A := saddleAlgorithm p σ L μ Δ G ε δ initial
  have he (n : ℕ) (q : E × F) : executeAnswerAt O A seed ξ n (0,q)=g q (ξ n) := by
    change g q (ξ ((executeIndexedState O A seed ξ n).2.length))=g q (ξ n)
    exact congrArg (fun k => g q (ξ k)) (executeIndexedState_length O A seed ξ n)
  have hh := execute_plan_indexed (saddleSeedLaw p σ L μ Δ G ε) initial initial.1
    (fun seed => saddlePlan p σ L μ Δ G ε δ seed initial) O seed ξ hK
  exact hh.trans (congrArg
    (fun reply : ℕ → E × F → E × F => evalAt reply (saddlePlan p σ L μ Δ G ε δ seed initial) 0)
    (funext fun n => funext fun q => he n q))

lemma setup_success (q : LongTails.Setups.HeavyTailedNcsc.Params) (hv : LongTails.Setups.HeavyTailedNcsc.spec.valid q) (f : q.E → q.F → ℝ)
    (O : Oracle (q.E × q.F) (q.E × q.F)) (hadm : LongTails.Setups.HeavyTailedNcsc.spec.admissible q f O)
    (K : ℕ) (hK : saddleCalls q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ ≤ K) :
    let A := saddleAlgorithm q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ (q.x0,q.y0)
    let output := fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K) w.1 w.2
    LongTails.Setups.HeavyTailedNcsc.spec.successful q f output ⟨(A.law : Measure _).prod (O.law : Measure _),inferInstance⟩ := by
  intro A output
  rcases hv with ⟨hμ,hμL,hp,hp2,hσ,hΔ,_,he,hδ,hδhalf⟩
  rcases hadm with ⟨gx,gy,ox,oy,pnoise,P,hIID,rfl,hgx,hgy,hl,hsc,hgap,hG,hox,hoy,hxi,hyi,hxm,hym,hpi,hpV⟩
  have H := HeavyTailSaddleGeometry.minimax_value_hyp hμ hμL hgx hgy hl hsc
  let g := fun z ω => (ox z ω,oy z ω)
  have hg : Measurable (Function.uncurry g) := hox.prodMk hoy
  let out := fun w : (SaddleSeed q.p q.σ q.L q.μ q.Δ q.G q.ε) × (ℕ → q.Ω) =>
    evalAt (fun k z => g z (w.2 k)) (saddlePlan q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ w.1 (q.x0,q.y0)) 0
  have hout : output=out := by
    funext w
    exact execute_saddle P g q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ (q.x0,q.y0) w.1 w.2 hK
  rw [hout]
  have hm : Measurable out := saddle_plan_measurable hg q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ (q.x0,q.y0)
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi (fun _ : ℕ => (pnoise : Measure q.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change (P : Measure (ℕ → q.Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  have hprob := saddle_success_probability H hsc (pnoise : Measure q.Ω) ox oy hox hoy hxi hyi hxm hym hp hp2 hσ hpi hpV
    hΔ he hδ (by linarith) (q.x0,q.y0) hgap hG
  refine ⟨hm,?_,?_⟩
  · choose ys hys using H.attain
    exact ⟨ys,hys⟩
  · intro ys hys
    have heq : (fun x => f x (ys x))=maxValue f := by
      funext x
      exact (H.max_value_eq (hys x)).symm
    rw [heq]
    change ((saddleSeedLaw q.p q.σ q.L q.μ q.Δ q.G q.ε : Measure _).prod (P : Measure (ℕ → q.Ω)))
      {w | q.ε < ‖gradient (maxValue f) (out w)‖} ≤ ENNReal.ofReal q.δ
    rw [hP]
    exact hprob

end LongTails.Proofs.HeavyTailSaddleOuter
